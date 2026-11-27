#!/usr/bin/env python3
"""
pronews.jp 자동 번역 시스템 v8.0.0 — 전면 재작성
파이프라인: 일본어 원문 → Gemini 1회 JSON 통합 번역 → WordPress 게시

================================================================
v8 재작성 변경 요약 (2026-11-21, 감사 보고서 action-code-audit-2026-11-21.md 기반)
----------------------------------------------------------------
[수정된 감사 지적]
- §3-1  아카이브 파서 전면 교체: PRONEWS 아카이브는 전체가 하나의 <article>로
         감싸져 있고 개별 기사는 <a> 안 중첩 <article>이라 기존 파서는 페이지당
         1건만 수집했다. 앵커드 뉴스 URL 패턴 + articleList-item-title/time
         셀렉터로 바꿔 페이지당 전수(12건) 수집.
- §3-3  0건 출력 런은 exit 1로 실패 처리 (처리 대상이 있었는데 성공 0건).
         단, 수집 소스가 정상인데 신규 기사가 없는 날은 정상 종료(exit 0).
         수집 소스(RSS+아카이브) 전부 실패 시에도 exit 1.
- §3-5  동시 실행 방지: 워크플로우 concurrency guard (auto-translate.yml 참조).
- §3-6  Gemini JSON 파싱 실패 시 원문 일부를 로그에 남기고 1회 재시도.
- §3-7  본문 길이 검사를 번역 "전"으로 이동(원문 250자 미만 사전 필터) +
         스킵한 URL을 skipped_articles.json에 기록해 재시도 방지.
         번역 후 500자 검사는 안전망으로 유지 (스킵 시에도 skipped 기록).
- §3-10 posted_articles.json 손상 시 빈 리스트 반환 금지 → 에러 로그 + exit 1.
- §3-11 WP 업로드·게시 요청에 timeout 설정 (미디어 60초, 게시 30초).
- §3-12 RSS 엔트리 link/title 접근을 try 안으로 (결손 엔트리 스킵 + 로그).
- §3-13 본문 정제 시 content_div 자체를 decompose하지 않도록 가드.
- §3-15 upload_media MIME을 확장자 기준으로 정확히 선언 (mimetypes).
- §4-1  automation_engine.py는 목업 데드 코드라 v8에서 제외 (삭제 권장).
- §4-9  로그 버퍼링 방지: python -u 실행 (워크플로우) + flush 출력.
- §4-10 _strip_html URL 형태 입력 가드 (MarkupResemblesLocatorWarning 방지).
- 버전 표기 단일화: VERSION = "8.0.0" (헤더·실행 배너 동일).
[신규]
- R2 이관 검증 단계: 발행 후 대표 이미지 URL이 media.prodg.kr인지 확인하고,
  Cafe24 로컬본 잔존 여부를 HEAD로 확인해 경고 로그로 남김 (삭제는 안 함 —
  로컬 삭제는 WP 오프로드 플러그인 역할).
- git push 실패를 삼키지 않음: 커밋 실패 시 exit 1.
- posted/skipped JSON 원자적 저장 (임시 파일 + rename).
[유지된 동작]
- 스케줄 06:00 KST (cron '0 21 * * *'), 카테고리 430, 원문 날짜로 WP 날짜 기록,
  posted_articles.json 중복 방지 + WP 2차 검사, 초안/발행 모드,
  일일 한도 10건, 아카이브 최대 20페이지, 수동 실행 = 아카이브 오래된 순,
  Gemini 모델 gemini-2.5-flash-lite (환경변수 기본값, 감사 결과 단종 아님).
================================================================
"""

import hashlib
import html
import json
import mimetypes
import os
import re
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from urllib.parse import urljoin, urlparse

import feedparser
import requests
from bs4 import BeautifulSoup

VERSION = "8.0.0"

# ==========================================
# 설정
# ==========================================
WORDPRESS_URL = "https://prodg.kr"
WORDPRESS_USER = os.environ.get("WP_USER")
WORDPRESS_APP_PASSWORD = os.environ.get("WP_APP_PASSWORD")
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY")
PRONEWS_RSS = "https://jp.pronews.com/feed"
PRONEWS_ARCHIVE_BASE = "https://jp.pronews.com/news/page"
PRONEWS_BASE_URL = "https://jp.pronews.com"
POSTED_ARTICLES_FILE = "posted_articles.json"
POSTED_ARTICLES_DRAFT_FILE = "posted_articles_draft.json"  # B-3: draft 테스트 기록
SKIPPED_ARTICLES_FILE = "skipped_articles.json"  # 너무 짧아 스킵한 URL (재시도 방지)
FORCE_UPDATE = os.environ.get("FORCE_UPDATE", "false").lower() == "true"
DAILY_LIMIT = 10
ARCHIVE_MAX_PAGES = 20

# R2 이관 검증용
R2_PUBLIC_BASE = "https://media.prodg.kr"
WP_UPLOADS_BASE = "https://prodg.kr/wp-content/uploads"
# R2 경로 매핑 확정 여부 (#9): 실제 미디어 1건으로 경로 매핑을 수동 확정한 뒤에만
# True로 바꾼다. 확정 전에는 "로컬본 삭제 확인"을 절대 보고하지 않고 "확인 불가"로 기록한다.
R2_PATH_MAPPING_CONFIRMED = True

# 배포 검증(C1) — 발행 후 공개 URL이 HTTP 200을 돌려주는지 확인하는 재시도 창
DEPLOY_VERIFY_TIMEOUT = 120   # 초
DEPLOY_VERIFY_INTERVAL = 10   # 초

# 본문 길이 기준 (단위: 문자)
MIN_SOURCE_CHARS = 250      # 번역 전 원문 평문 최소 길이 (미만이면 번역 없이 스킵)
MIN_TRANSLATED_CHARS = 500  # 번역 후 본문 최소 길이 (안전망)

# HTTP 타임아웃 (초) — 무한 대기 금지
SCRAPE_TIMEOUT = 15
WP_TIMEOUT = 30
MEDIA_UPLOAD_TIMEOUT = 60

# 실행 모드 감지
# RUN_MODE_OVERRIDE: 워크플로우 입력(event_name_override)으로 스케줄 경로를
# 브랜치에서 시험할 때 사용. GitHub Actions는 기본 GITHUB_* 환경 변수의
# 덮어쓰기를 무시하므로 GITHUB_EVENT_NAME을 직접 바꾸는 방식은 동작하지 않는다.
# (재검수 1번) 비어 있으면 실제 이벤트명(schedule/workflow_dispatch)을 쓴다.
EFFECTIVE_EVENT = os.environ.get("RUN_MODE_OVERRIDE", "").strip() or os.environ.get("GITHUB_EVENT_NAME", "workflow_dispatch")
IS_SCHEDULED = EFFECTIVE_EVENT == "schedule"

# 게시 상태
POST_STATUS = os.environ.get("POST_STATUS", "publish")
CLEANUP_TEST_DRAFTS = os.environ.get("CLEANUP_TEST_DRAFTS", "false").strip().lower() == "true"  # B-3(c)
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash-lite")

USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"


def log(msg: str):
    """타임스탬프 + 즉시 flush 로그 (Actions 로그 뭉개짐 방지)."""
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)


# ==========================================
# Gemini 통합 엔진
# ==========================================
class GeminiEngine:
    def __init__(self):
        self.api_key = GEMINI_API_KEY
        if not self.api_key:
            log("❌ GEMINI_API_KEY 미설정")
            sys.exit(1)
        self.last_call_time = 0.0
        self.rate_limit_hit = False

    def _call_api(self, prompt: str, max_tokens: int = 8192, response_mime_type: str = None) -> str:
        if self.rate_limit_hit:
            return ""

        elapsed = time.time() - self.last_call_time
        if elapsed < 7:
            time.sleep(7 - elapsed)
        self.last_call_time = time.time()

        # M7: API 키를 URL 쿼리가 아닌 x-goog-api-key 헤더로 보낸다.
        # 쿼리에 두면 예외 메시지에 URL이 포함될 때 키가 로그에 찍힌다.
        url = (
            "https://generativelanguage.googleapis.com/v1beta/models/"
            f"{GEMINI_MODEL}:generateContent"
        )
        headers = {"x-goog-api-key": self.api_key}
        generation_config = {
            "maxOutputTokens": max_tokens,
            "temperature": 0.4,
        }
        if response_mime_type:
            # JSON 출력 호출에만 지정한다. plain-text 재번역 호출에는 쓰지 않는다.
            generation_config["responseMimeType"] = response_mime_type
        payload = {
            "contents": [{"parts": [{"text": prompt}]}],
            "generationConfig": generation_config,
        }

        backoff = [15, 30, 60]
        for attempt in range(3):
            try:
                res = requests.post(url, json=payload, headers=headers, timeout=120)

                if res.status_code == 429:
                    wait = backoff[min(attempt, len(backoff) - 1)]
                    log(f"⚠️ 429 Rate Limit (시도 {attempt + 1}/3) → {wait}초 대기...")
                    time.sleep(wait)
                    if attempt == 2:
                        log("❌ 429 반복 → 런 종료 (미게시 기사는 다음 런 자동 이월)")
                        self.rate_limit_hit = True
                        return ""
                    continue

                res.raise_for_status()
                candidates = res.json().get("candidates", [])
                if candidates:
                    parts = candidates[0]["content"]["parts"]
                    for part in parts:
                        if not part.get("thought", False) and "text" in part:
                            return part["text"].strip()
                    for part in reversed(parts):
                        if "text" in part:
                            return part["text"].strip()

                log(f"⚠️ Gemini 응답 없음 (시도 {attempt + 1}/3)")

            except Exception as e:
                log(f"⚠️ Gemini API 오류 (시도 {attempt + 1}/3): {e}")
                if attempt < 2:
                    time.sleep(backoff[attempt])

        return ""

    @staticmethod
    def _parse_json_response(raw: str):
        """모델 출력에서 JSON을 추출한다. 실패하면 None을 반환하고 원문을 로그에 남긴다."""
        try:
            clean = re.sub(r"```(?:json)?", "", raw).strip().rstrip("`").strip()
            match = re.search(r"(\{.*\})", clean, re.DOTALL)
            if match:
                return json.loads(match.group(1))
        except Exception as e:
            log(f"⚠️ JSON 파싱 실패: {e}")
        # 잘렸는지(토큰 제한) 확인하려고 앞뒤를 남긴다
        log(f"   원문 앞 300자: {raw[:300]!r}")
        log(f"   원문 뒤 200자: {raw[-200:]!r}")
        return None

    def translate_article(self, title_ja: str, body_text: str) -> dict:
        prompt = f"""당신은 영상·카메라·디지털 전문 미디어 proDG의 한국어 시니어 에디터입니다.
아래 일본어 기사(HTML)를 한국어로 번역·편집하여 JSON으로만 출력하세요.

=== 일본어 원문 ===
제목: {title_ja}

본문:
{body_text[:15000]}

=== 번역 규칙 ===
1. 일본어(히라가나·가타카나·한자)를 완전히 한국어로 번역. 일본어가 한 글자도 남으면 안 됨.
2. 문체: 반드시 '~다', '~했다', '~이다' 등 기사 형식의 평어체로 통일. '~합니다' 금지.
3. 브랜드명·모델명 표기:
   - 원문 영문 유지: Sony, Canon, Nikon, DJI, Blackmagic, Sigma, Tamron, Fujifilm 등
   - タムロン→탐론, ソニー→소니, キヤノン→캐논, ニコン→니콘, パナソニック→파나소닉
4. 기술 용어: 4K, 8K, Full HD, fps, RAW, ISO, f값, mm 등 원문 그대로 유지
5. ★절대 금지★: <img>, <figure>, <picture>, <iframe>, <video> 태그와 src·alt·width·height 속성 수정·삭제
6. 번역 품질 기준:
   - 기계 번역 티가 나면 안 됨. 한국 전문 기자가 직접 쓴 것처럼 자연스럽게. (단, 규칙 7의 국가·시장·언어 표기는 원문 그대로 — '한국 기자' 문체 때문에 일본을 한국으로 바꾸지 말 것.)
   - 제품 스펙·수치는 정확하게 유지
   - 문단 구조와 논리 흐름 유지
   - Google AdSense 고품질 콘텐츠 기준 충족
7. ★국가·시장·언어 표기는 원문 그대로★ (절대 현지화 금지):
   - 日本→일본, 日本語→일본어, 日本市場→일본 시장. 일본을 한국으로 바꾸거나 한국 독자 관점으로 현지화하지 말 것.
   - 国内(일본 국내를 뜻함)→"일본 내" / "일본 국내". 단독 "국내" 금지 (한국 독자는 한국으로 읽음).
   - 가격·통화는 원문 그대로: 円→엔 (엔화로 표기, 원화로 환산 금지).

=== 출력 JSON 규칙 ===
- title: SEO 최적화 제목 (브랜드명·모델명·핵심스펙 포함, 40~55자)
- content: 번역 본문 (HTML 구조·이미지 태그 완벽 유지, 최소 300자 이상)
- excerpt: 구글 스니펫용 요약 (핵심 정보 2문장, 80~120자, 평어체)
- tldr: 핵심 요약 3~4항목 (<ul><li> HTML, 각 항목 구체적 수치·스펙 포함, 평어체)
- 마크다운 백틱 없이 순수 JSON만 출력

{{
  "title": "SEO 제목",
  "content": "<p>본문</p> <figure><img src='...'></figure>",
  "excerpt": "요약문",
  "tldr": "<ul><li>요약1</li><li>요약2</li><li>요약3</li></ul>"
}}"""

        # 1차 시도 + 파싱 실패 시 1회 재시도 (§3-6)
        # JSON 출력이므로 responseMimeType을 application/json으로 지정한다
        # (토큰 한도로 잘린 경우 같은 프롬프트 재시도는 또 잘리므로, 애초에 JSON으로 받는다).
        for attempt in range(2):
            result = self._call_api(prompt, max_tokens=8192, response_mime_type="application/json")
            if not result:
                return {}
            parsed = self._parse_json_response(result)
            if parsed is not None:
                return parsed
            if attempt == 0:
                log("   🔁 JSON 파싱 실패 → 번역 1회 재시도...")
        log("❌ JSON 파싱 2회 실패 → 기사 스킵")
        return {}

    def retranslate_content(self, content_ko: str) -> str:
        prompt = f"""아래 한국어 본문(HTML 포함)에 일본어가 섞여 있습니다.
일본어 부분을 자연스러운 한국어 평어체(~다, ~했다, ~이다)로 번역하고 전체 본문을 반환하세요.
★중요★ <img>, <figure> 등 모든 HTML 태그와 속성은 절대 건드리지 말고 그대로 유지할 것.
★국가·시장·언어 표기는 원문 그대로: 日本→일본, 日本語→일본어, 日本市場→일본 시장, 国内→"일본 내". 일본을 한국으로 바꾸지 말 것. 가격 円→엔.
본문만 출력:

{content_ko[:15000]}"""
        result = self._call_api(prompt, max_tokens=8192)
        return result if result else content_ko

    def _has_japanese(self, text: str) -> bool:
        plain = BeautifulSoup(text, "lxml").get_text()
        return len(re.findall(r"[\u3040-\u309f\u30a0-\u30ff]", plain)) > 5


# ==========================================
# 메인 번역 시스템
# ==========================================
class NewsTranslator:
    # 아카이브 뉴스 링크: 반드시 URL 시작부터 일치시켜야 공유 링크(트위터/FB/LINE 등
    # 쿼리에 원문 URL을 품은 것)를 걸러낸다. (§3-1)
    NEWS_LINK_RE = re.compile(r"^https?://jp\.pronews\.com/news/\d+\.html$")
    NEWS_LINK_REL_RE = re.compile(r"^/news/\d+\.html$")
    ARCHIVE_DATE_RE = re.compile(r"(\d{4})\.(\d{2})\.(\d{2})$")

    def __init__(self):
        self.gemini = GeminiEngine()
        self.wordpress_api = f"{WORDPRESS_URL}/wp-json/wp/v2"
        self.posted_articles = self.load_posted_articles()
        self.posted_articles_draft = self.load_posted_articles_draft()
        self.posted_draft_dirty = False  # B-3: draft 기록이 바뀐 런은 커밋 대상
        self.skipped_articles = self.load_skipped_articles()
        self.skipped_dirty = False
        self.posted_dirty = False   # #6: posted 목록이 바뀐 런은 커밋 대상 (중복 기록 포함)
        self.skipped_this_run = 0   # #4: 이번 런의 스킵 횟수 (절반 초과 판정용)

    # ---------- 상태 파일 ----------

    def load_posted_articles(self) -> list:
        """posted 목록 로드. 파일 손상 시 빈 리스트로 속단하지 않고 실패로 종료한다. (§3-10)"""
        path = Path(POSTED_ARTICLES_FILE)
        if not path.exists():
            return []
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError) as e:
            log(f"❌ {POSTED_ARTICLES_FILE} 손상 — 파싱 불가: {e}")
            log("   빈 목록으로 진행하면 전체 기사를 재처리하므로 런을 중단합니다.")
            sys.exit(1)
        if not isinstance(data, list):
            log(f"❌ {POSTED_ARTICLES_FILE} 형식이 리스트가 아님 — 런을 중단합니다.")
            sys.exit(1)
        return data

    def load_posted_articles_draft(self) -> list:
        """B-3(a): draft 테스트 기록 로드. 항목 형식 {url, wp_post_id, slug, date}.
        파일이 없으면 []. 손상 시 posted와 동일하게 런을 중단한다
        (테스트 draft를 잃어버리면 정리할 수 없게 되므로)."""
        path = Path(POSTED_ARTICLES_DRAFT_FILE)
        if not path.exists():
            return []
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError) as e:
            log(f"❌ {POSTED_ARTICLES_DRAFT_FILE} 손상 — 파싱 불가: {e}")
            log("   테스트 draft 기록을 잃으면 정리할 수 없으므로 런을 중단합니다.")
            sys.exit(1)
        if not isinstance(data, list):
            log(f"❌ {POSTED_ARTICLES_DRAFT_FILE} 형식이 리스트가 아님 — 런을 중단합니다.")
            sys.exit(1)
        return data

    def load_skipped_articles(self) -> list:
        """스킵 목록 로드. 손상되어도 재시도 방지만 놓치는 수준이라 경고 후 빈 목록으로 간다.
        기록 형식: {url, reason, date, hits} — hits가 2회 이상일 때만 제외한다 (#4).
        구 형식(URL 문자열 목록)은 hits=2 기록으로 변환해 제외를 유지한다.
        파일이 없으면 []로 생성한다 (#1: git add 실패 방지)."""
        path = Path(SKIPPED_ARTICLES_FILE)
        if not path.exists():
            self._atomic_write_json(SKIPPED_ARTICLES_FILE, [])
            return []
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, UnicodeDecodeError) as e:
            log(f"⚠️ {SKIPPED_ARTICLES_FILE} 손상 — 빈 목록으로 시작: {e}")
            return []
        if not isinstance(data, list):
            log(f"⚠️ {SKIPPED_ARTICLES_FILE} 형식이 리스트가 아님 — 빈 목록으로 시작")
            return []
        today = datetime.now().strftime("%Y-%m-%d")
        records = []
        for item in data:
            if isinstance(item, dict) and item.get("url"):
                records.append({
                    "url": item["url"],
                    "reason": item.get("reason", ""),
                    "date": item.get("date", today),
                    "hits": int(item.get("hits", 1)),
                })
            elif isinstance(item, str) and item:
                # 구 형식: 이미 영구 스킵된 것으로 간주해 hits=2로 유지
                records.append({"url": item, "reason": "legacy", "date": today, "hits": 2})
        return records

    @staticmethod
    def _atomic_write_json(path: str, data: list):
        tmp = Path(path + ".tmp")
        tmp.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
        tmp.replace(path)

    def save_posted_articles(self):
        self._atomic_write_json(POSTED_ARTICLES_FILE, self.posted_articles)

    def save_posted_articles_draft(self):
        self._atomic_write_json(POSTED_ARTICLES_DRAFT_FILE, self.posted_articles_draft)

    def _draft_post_ids(self) -> set:
        """B-3(b): 테스트 draft로 기록된 WP 글 ID 집합."""
        ids = set()
        for e in self.posted_articles_draft:
            if isinstance(e, dict) and e.get("wp_post_id") is not None:
                ids.add(e["wp_post_id"])
        return ids

    def save_skipped_articles(self):
        self._atomic_write_json(SKIPPED_ARTICLES_FILE, self.skipped_articles)
        self.skipped_dirty = False

    def mark_skipped(self, url: str, reason: str):
        """너무 짧아 스킵한 URL을 기록한다. (#4)
        hits가 2회 이상이 되어야 수집 단계에서 제외된다. 1회 스킵(일시적 실패 가능)은
        다음 런에 다시 시도된다. 게시 성공 시 기록이 제거된다."""
        today = datetime.now().strftime("%Y-%m-%d")
        record = next((r for r in self.skipped_articles if r.get("url") == url), None)
        if record is None:
            hits = 1
            self.skipped_articles.append({"url": url, "reason": reason, "date": today, "hits": hits})
        else:
            hits = int(record.get("hits", 1)) + 1
            record["hits"] = hits
            record["reason"] = reason
            record["date"] = today
        self.skipped_dirty = True
        self.skipped_this_run += 1
        log(f"   📌 스킵 목록 기록 ({reason}, {hits}회): {url}")

    def _clear_skipped(self, url: str):
        """게시 성공 시 해당 URL의 스킵 기록을 제거한다."""
        before = len(self.skipped_articles)
        self.skipped_articles = [r for r in self.skipped_articles if r.get("url") != url]
        if len(self.skipped_articles) != before:
            self.skipped_dirty = True

    def _is_known(self, url: str) -> bool:
        if FORCE_UPDATE:
            return False
        if url in self.posted_articles:
            return True
        # 스킵 기록은 hits 2회 이상일 때만 제외한다 (#4 — 1회 스킵은 다음 런 재시도)
        for r in self.skipped_articles:
            if isinstance(r, dict) and r.get("url") == url and int(r.get("hits", 1)) >= 2:
                return True
        return False

    # ---------- 기사 수집 ----------

    def fetch_rss_articles(self):
        """RSS에서 미게시 기사를 수집한다. (기사 목록, 소스 정상 여부)를 반환한다."""
        log(f"📡 RSS 피드 확인: {PRONEWS_RSS}")
        try:
            feed = feedparser.parse(PRONEWS_RSS)
        except Exception as e:
            log(f"❌ RSS 파싱 실패: {e}")
            return [], False
        if getattr(feed, "bozo", False):
            log(f"⚠️ RSS 피드 비정상(bozo): {getattr(feed, 'bozo_exception', '')}")
        # #2: feedparser는 네트워크 실패 시에도 예외 없이 bozo=True, entries=0,
        # status=None을 반환하므로, 상태 코드 또는 엔트리 유무로 정상 여부를 판정한다.
        entries = getattr(feed, "entries", []) or []
        rss_ok = feed.get("status") == 200 or (bool(entries) and not getattr(feed, "bozo", False))
        if not rss_ok:
            log(f"❌ RSS 피드 응답 없음 (status={feed.get('status')}, bozo={getattr(feed, 'bozo', False)}, entries={len(entries)})")
        articles = []
        for entry in feed.entries:
            # §3-12: link/title 접근도 try 안으로 — 결손 엔트리가 런 전체를 죽이지 않게
            try:
                link = getattr(entry, "link", None)
                title = getattr(entry, "title", None)
                if not link or not title:
                    log(f"   ⚠️ RSS 엔트리 결손 스킵 (link/title 없음): {getattr(entry, 'id', '?')}")
                    continue
                if self._is_known(link):
                    continue
                try:
                    article_date = datetime(*entry.published_parsed[:6])
                except Exception:
                    article_date = datetime.now()
            except Exception as e:
                log(f"   ⚠️ RSS 엔트리 처리 오류 스킵: {e}")
                continue
            articles.append({
                "title": title,
                "link": link,
                "date": article_date,
                "source": "rss",
            })
        log(f"   RSS 미게시: {len(articles)}건")
        return articles, rss_ok

    def _parse_archive_page(self, soup: BeautifulSoup, seen_links: set) -> list:
        """아카이브 페이지 1장을 파싱한다. (§3-1)

        PRONEWS 아카이브 구조 (2026-11-21 실측):
          <article class="article"> (페이지 전체 래퍼)
            <a href="/news/<18자리숫자>.html">
              <article>
                <div class="articleList-item-thumb"><img alt="제목"></div>
                <div class="articleList-item-body">
                  <p class="articleList-item-title">제목</p>
                  <time class="articleList-item-date">2026.11.21</time>
                </div>
              </article>
            </a>  ... 12건 반복
        구 파서는 find_all('article') 후 article.find('a')를 했는데, 중첩 article은
        <a>의 자식이라 find('a')가 안 잡혀 페이지당 1건만 수집됐다.
        """
        found = []
        for a in soup.find_all("a", href=True):
            # #5: 리스트 항목(<a> 직속 자식 <article>)만 수집한다.
            # 사이드바 랭킹 등 <article>을 품지 않은 링크는 제외한다
            # (CSS 셀렉터 a:has(> article)와 같은 의미).
            if a.find("article", recursive=False) is None:
                continue
            href = a["href"].strip()
            if self.NEWS_LINK_REL_RE.match(href):
                href = urljoin(PRONEWS_BASE_URL, href)
            if not self.NEWS_LINK_RE.match(href):
                continue
            if href in seen_links:
                continue

            title = ""
            title_tag = a.find("p", class_="articleList-item-title")
            if title_tag:
                title = title_tag.get_text(strip=True)
            if not title:  # 구조 변경 대비 폴백 1: 썸네일 alt
                img = a.find("img", alt=True)
                if img:
                    title = (img.get("alt") or "").strip()
            if not title:  # 폴백 2: 링크 텍스트에서 말미 날짜 제거
                title = self.ARCHIVE_DATE_RE.sub("", a.get_text(strip=True)).strip()
            if not title:
                continue

            # #5: 날짜가 없으면 datetime.min — datetime.now()를 쓰면
            # 날짜 없는 링크가 스케줄 모드(최신순)에서 맨 앞에 오게 된다.
            article_date = datetime.min
            raw_date = ""
            date_tag = a.find("time", class_="articleList-item-date")
            if date_tag:
                raw_date = date_tag.get_text(strip=True)
            if not raw_date:
                m = self.ARCHIVE_DATE_RE.search(a.get_text(strip=True))
                if m:
                    raw_date = f"{m.group(1)}.{m.group(2)}.{m.group(3)}"
            if raw_date:
                try:
                    article_date = datetime.strptime(raw_date, "%Y.%m.%d")
                except ValueError:
                    pass

            found.append({"title": title, "link": href, "date": article_date, "source": "archive"})
        return found

    def fetch_archive_articles(self, need: int, oldest_first: bool = False):
        """아카이브를 크롤링해 미게시 기사를 수집한다. (기사 목록, 소스 정상 여부)를 반환한다."""
        log(f"📚 아카이브 크롤링 (필요: {need}건, 오래된순: {oldest_first})...")

        actual_max_page = ARCHIVE_MAX_PAGES
        if oldest_first:
            try:
                log("   🔍 실제 마지막 페이지 번호 탐색 중...")
                res = requests.get(
                    f"{PRONEWS_ARCHIVE_BASE}/1/",
                    headers={"User-Agent": USER_AGENT},
                    timeout=SCRAPE_TIMEOUT,
                )
                if res.status_code == 200:
                    soup = BeautifulSoup(res.text, "lxml")
                    pages = []
                    for a in soup.find_all("a", href=True):
                        match = re.search(r"/news/page/(\d+)", a["href"])
                        if match:
                            pages.append(int(match.group(1)))
                    if pages:
                        actual_max_page = min(max(pages), ARCHIVE_MAX_PAGES)
                        log(f"   ✅ 탐색된 시작 페이지: {actual_max_page}")
            except Exception as e:
                log(f"   ⚠️ 페이지 탐색 오류 (기본값 {ARCHIVE_MAX_PAGES} 사용): {e}")

        collected = []
        seen_links = set()
        pages_ok = 0
        pages_tried = 0
        total_found = 0  # #3: 발견 건수 합계 (페이지 HTTP 성공이 아닌 발견 건수로 판정)
        page = actual_max_page if oldest_first else 1

        while len(collected) < need * 3 and 1 <= page <= ARCHIVE_MAX_PAGES:
            url = f"{PRONEWS_ARCHIVE_BASE}/{page}/"
            pages_tried += 1
            try:
                res = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=SCRAPE_TIMEOUT)

                if res.status_code == 404:
                    if oldest_first:
                        log(f"   페이지 {page} 없음 → 이전 페이지 탐색")
                        page -= 1
                        continue
                    log(f"   페이지 {page} 없음 → 크롤링 종료")
                    break

                res.raise_for_status()
                pages_ok += 1
                soup = BeautifulSoup(res.text, "lxml")
                found = self._parse_archive_page(soup, seen_links)
                total_found += len(found)
                if not found:
                    log(f"   ⚠️ 페이지 {page}: 기사 0건 — 사이트 구조 변경 의심")

                for art in found:
                    if art["link"] not in seen_links:
                        seen_links.add(art["link"])
                        if not self._is_known(art["link"]):
                            collected.append(art)

                log(f"   페이지 {page}: {len(found)}건 발견, 누적 미게시: {len(collected)}건")
                page = page - 1 if oldest_first else page + 1
                time.sleep(1)

            except Exception as e:
                log(f"⚠️ 아카이브 페이지 {page} 오류: {e}")
                page = page - 1 if oldest_first else page + 1

        collected.sort(key=lambda x: x["date"], reverse=not oldest_first)
        result = collected[:need]
        log(f"   아카이브 수집 완료: {len(result)}건 (발견 합계 {total_found}건)")
        # #3: 성공 기준은 "발견 건수 합계 > 0" — HTTP 200만으로는 구조 변경을 못 잡는다.
        return result, total_found > 0

    def get_articles_to_process(self):
        """처리 대상 기사와 수집 소스 상태를 반환한다. (기사 목록, 수집 실패 여부)"""
        fetch_failed = False
        if IS_SCHEDULED:
            log("🕐 자동 실행: 최신 우선 + 아카이브 보충")
            rss, rss_ok = self.fetch_rss_articles()
            rss.sort(key=lambda x: x["date"], reverse=True)
            target = rss[:DAILY_LIMIT]
            need = DAILY_LIMIT - len(target)
            archive_ok = True
            if need > 0:
                log(f"   RSS {len(target)}건 → 아카이브에서 {need}건 보충")
                rss_links = {a["link"] for a in target}
                archive, archive_ok = self.fetch_archive_articles(need * 2, oldest_first=False)
                archive = [a for a in archive if a["link"] not in rss_links]
                target += archive[:need]
            target = target[:DAILY_LIMIT]
            fetch_failed = (not rss_ok) and (not archive_ok)
        else:
            log("📖 수동 실행: 아카이브 오래된 순 10건 (블로그 채우기)")
            target, archive_ok = self.fetch_archive_articles(DAILY_LIMIT, oldest_first=True)
            fetch_failed = not archive_ok

        log(f"✅ 처리 대상: {len(target)}건")
        return target, fetch_failed


    # ---------- 본문 스크래핑 ----------

    def fetch_full_content(self, url: str):
        try:
            log(f"📄 스크래핑: {url}")
            res = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=SCRAPE_TIMEOUT)
            res.raise_for_status()
            soup = BeautifulSoup(res.text, "lxml")

            article_date = None
            time_tag = soup.find("time", datetime=True)
            if time_tag:
                try:
                    article_date = datetime.fromisoformat(time_tag["datetime"].replace("Z", "+00:00"))
                except Exception:
                    pass

            if not article_date:
                date_text = soup.select_one(".articleHeader-date")
                if date_text:
                    try:
                        article_date = datetime.strptime(date_text.get_text(strip=True)[:10], "%Y.%m.%d")
                    except Exception:
                        pass

            content_div = (
                soup.find("div", class_="articleBody-inner")
                or soup.find("div", class_="articleBody")
                or soup.find("div", class_="entry-content")
                or soup.find("div", class_="post-content")
                or soup.find("div", class_="article-content")
                or soup.find("article")
            )
            if not content_div:
                return "", None

            noise_classes = [
                "articleAside", "mainLayout-side", "articleShareSticky",
                "articleShare", "relatedKeyword", "relatedArticle", "prnbox",
            ]
            for noise_class in noise_classes:
                for noise in content_div.find_all(class_=noise_class):
                    noise.decompose()

            removed = False
            for mv_class in ["articleBody-mv", "article-mv", "post-thumbnail",
                             "entry-thumbnail", "article-eye-catch"]:
                mv_area = content_div.find(class_=mv_class)
                if mv_area:
                    mv_area.decompose()
                    log(f"🗑️ 본문 상단 이미지 제거 ({mv_class})")
                    removed = True
                    break

            if not removed:
                first_child = content_div.find(recursive=False)
                if first_child and first_child.name in ["figure", "picture"]:
                    first_child.decompose()
                    log("🗑️ 본문 최상단 figure 제거")
                elif first_child and first_child.name == "img":
                    first_child.decompose()
                    log("🗑️ 본문 최상단 img 제거")
                elif first_child and first_child.name in ["div", "p"]:
                    inner = first_child.find_all(recursive=False)
                    if len(inner) == 1 and inner[0].name in ["img", "figure", "picture"]:
                        first_child.decompose()
                        log("🗑️ 본문 최상단 이미지 래퍼 제거")

            # §3-13: 노이즈 문자열의 부모를 지울 때 content_div 자체는 절대 지우지 않는다.
            for elem in content_div.find_all(string=re.compile(
                r"原文掲載時刻:|ソース:|バックナンバー|関連キーワード|この記事をシェア|FOLLOW US|画像をクリック|クリックすると拡大|※画像"
            )):
                parent = elem.find_parent()
                if parent is not None and parent is not content_div:
                    parent.decompose()

            for h_tag in content_div.find_all(["h2", "h3", "h4"]):
                if any(kw in h_tag.get_text(strip=True) for kw in
                       ["バックナンバー", "この記事をシェア", "FOLLOW US", "関連記事", "関連キーワード"]):
                    next_elem = h_tag.find_next_sibling()
                    h_tag.decompose()
                    while next_elem and next_elem.name not in ["h1", "h2", "h3", "h4"]:
                        temp = next_elem.find_next_sibling()
                        next_elem.decompose()
                        next_elem = temp

            for tag in content_div(["script", "style", "noscript", "form", "nav", "aside", "footer", "header"]):
                tag.decompose()

            for iframe in list(content_div.find_all("iframe")):
                if not any(v in iframe.get("src", "").lower() for v in ["youtube", "youtu.be", "vimeo"]):
                    iframe.decompose()

            for elem in content_div.find_all(class_=lambda x: x and any(
                sc in " ".join(x).lower() for sc in
                ["social-share", "share-buttons", "addtoany", "sharedaddy", "entry-footer", "post-meta"]
            )):
                elem.decompose()

            for a in list(content_div.find_all("a")):
                href = a.get("href", "")
                if any(kw in href.lower() for kw in
                       ["facebook.com", "twitter.com", "line.me", "/fellowship/", "hatena.ne.jp"]) \
                        or href.startswith("//") or not a.get_text(strip=True):
                    a.decompose()

            for tag_name in ["p", "div", "span", "li"]:
                for tag in content_div.find_all(tag_name):
                    if not tag.get_text(strip=True) and not tag.find("img"):
                        tag.decompose()

            return str(content_div), article_date

        except Exception as e:
            log(f"⚠️ 스크래핑 실패: {e}")
            return "", None

    # ---------- 슬러그 / 이미지 ----------

    def generate_seo_slug(self, title_ko: str, article_date: datetime, title_ja: str = "") -> str:
        date_str = article_date.strftime("%Y%m%d") if article_date else datetime.now().strftime("%Y%m%d")
        BRAND_SLUG = {
            "ソニー": "sony", "キヤノン": "canon", "ニコン": "nikon",
            "タムロン": "tamron", "シグマ": "sigma", "フジフイルム": "fujifilm",
            "パナソニック": "panasonic", "オリンパス": "olympus", "ライカ": "leica",
            "ブラックマジック": "blackmagic", "アップル": "apple", "アドビ": "adobe",
            "ゴープロ": "gopro", "ドローン": "drone", "カメラ": "camera",
            "レンズ": "lens", "ミラーレス": "mirrorless", "動画": "video",
            "映像": "video", "写真": "photo", "撮影": "shooting",
        }

        def extract_english(text: str) -> str:
            words = re.findall(r"[a-zA-Z][a-zA-Z0-9]*|[0-9]+[a-zA-Z]+|[a-zA-Z]+[0-9]+", text)
            filtered = [w.lower() for w in words if len(w) >= 2]
            return "-".join(filtered[:6])

        slug = extract_english(title_ko)
        if len(slug) < 3 and title_ja:
            slug = extract_english(title_ja)
        if len(slug) < 3 and title_ja:
            brand_words = [en for ja, en in BRAND_SLUG.items() if ja in title_ja]
            if brand_words:
                slug = "-".join(brand_words[:3])
        slug = re.sub(r"-+", "-", slug).strip("-")
        return f"{slug[:50]}-{date_str}" if len(slug) >= 3 else f"news-{date_str}"

    def get_main_image_url(self, link: str):
        try:
            res = requests.get(link, headers={"User-Agent": USER_AGENT}, timeout=SCRAPE_TIMEOUT)
            res.raise_for_status()
            soup = BeautifulSoup(res.text, "lxml")
            og = soup.find("meta", property="og:image")
            if og and og.get("content"):
                return og["content"]
            content = soup.find("div", class_="entry-content")
            if content:
                img = content.find("img")
                if img and img.get("src"):
                    src = img["src"]
                    return src if src.startswith("http") else urljoin(link, src)
        except Exception:
            pass
        return None

    def download_image(self, url: str):
        if not url:
            return None
        try:
            log(f"🖼️ 이미지 다운로드: {url}")
            res = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=SCRAPE_TIMEOUT)
            res.raise_for_status()
            url_hash = hashlib.md5(url.encode()).hexdigest()[:8]
            ext = os.path.splitext(os.path.basename(urlparse(url).path).split("?")[0])[1]
            if ext not in [".jpg", ".jpeg", ".png", ".gif", ".webp"]:
                ext = ".jpg"
            path = Path(f"/tmp/pronews_{int(time.time())}_{url_hash}{ext}")
            with open(path, "wb") as f:
                f.write(res.content)
            log(f"   ✅ {path.name}")
            return path
        except Exception as e:
            log(f"⚠️ 이미지 다운로드 실패: {e}")
            return None

    def upload_media(self, image_path: Path):
        """WP 미디어 라이브러리에 업로드한다. timeout + MIME 정확 선언 + 1회 재시도. (§3-11, §3-15)"""
        if not image_path or not image_path.exists():
            return None
        mime, _ = mimetypes.guess_type(str(image_path))
        mime = mime or "image/jpeg"
        for attempt in range(2):
            try:
                with open(image_path, "rb") as img:
                    res = requests.post(
                        f"{self.wordpress_api}/media",
                        auth=(WORDPRESS_USER, WORDPRESS_APP_PASSWORD),
                        headers={"Content-Disposition": f"attachment; filename={image_path.name}"},
                        files={"file": (image_path.name, img, mime)},
                        timeout=MEDIA_UPLOAD_TIMEOUT,
                    )
                    res.raise_for_status()
                    return res.json()
            except Exception as e:
                log(f"⚠️ 미디어 업로드 실패 (시도 {attempt + 1}/2): {e}")
                if attempt == 0:
                    time.sleep(5)
        log("   → 대표 이미지 없이 발행됩니다")
        return None

    # ---------- WP 중복 검사 / 게시 ----------

    def is_already_posted_on_wp(self, original_url: str) -> bool:
        """WP 2차 중복 검사. 본문에 원문 URL이 포함된 글이 있으면 True."""
        try:
            search_term = original_url.split("/")[-2] if original_url.endswith("/") else original_url.split("/")[-1]
            res = requests.get(
                f"{self.wordpress_api}/posts",
                auth=(WORDPRESS_USER, WORDPRESS_APP_PASSWORD),
                params={"search": search_term, "per_page": 10, "status": "any"},
                timeout=WP_TIMEOUT,
            )
            if res.status_code == 200:
                for post in res.json():
                    if original_url in post.get("content", {}).get("rendered", ""):
                        # B-3(b): publish 모드에서 테스트 draft는 무시한다.
                        # (status가 draft이고 ID가 테스트 기록에 있을 때만)
                        if (POST_STATUS == "publish"
                                and post.get("status") == "draft"
                                and post.get("id") in self._draft_post_ids()):
                            log(f"테스트 draft 무시: {post['id']}")
                            continue
                        log(f"⚠️ 중복 감지 → 스킵: {post['link']}")
                        return True
            return False
        except Exception as e:
            log(f"⚠️ 중복 체크 오류 (계속 진행): {e}")
            return False

    def post_to_wordpress(self, title: str, content: str, slug: str,
                          featured_media_id: int, original_date: datetime,
                          excerpt: str = "", status: str = "draft"):
        """WP에 글을 게시한다. 성공 시 게시글 dict(id/link 포함), 실패 시 None을 반환한다."""
        target_date = original_date.strftime("%Y-%m-%dT%H:%M:%S") if original_date else datetime.now().strftime("%Y-%m-%dT%H:%M:%S")
        post_data = {
            "title": title, "content": content, "slug": slug,
            "status": status, "featured_media": featured_media_id or 0,
            "date": target_date,
            "categories": [430],  # proNEWS 카테고리 고정
        }
        if excerpt:
            post_data["excerpt"] = excerpt
        try:
            res = requests.post(
                f"{self.wordpress_api}/posts",
                auth=(WORDPRESS_USER, WORDPRESS_APP_PASSWORD),
                json=post_data,
                timeout=WP_TIMEOUT,
            )
            res.raise_for_status()
            post = res.json()
            label = "📝 임시저장" if status == "draft" else "✨ 게시 성공"
            log(f"{label} ({target_date}): {post['link']}")
            return post
        except Exception as e:
            log(f"❌ 게시 실패: {e}")
            if hasattr(e, "response") and e.response is not None:
                log(f"   {e.response.text[:300]}")
            return None

    def verify_r2_offload(self, featured_media_id: int):
        """[신규] 발행 후 R2 이관 검증. 대표 이미지가 media.prodg.kr인지, Cafe24
        로컬본이 남아 있는지 확인하고 경고 로그만 남긴다. 삭제는 하지 않는다
        (로컬 삭제는 WP 오프로드 플러그인 역할). 검증 실패가 런을 실패시키지는 않는다."""
        if not featured_media_id:
            log("   R2 검증 스킵: 대표 이미지 없음")
            return
        try:
            res = requests.get(
                f"{self.wordpress_api}/media/{featured_media_id}",
                auth=(WORDPRESS_USER, WORDPRESS_APP_PASSWORD),
                timeout=WP_TIMEOUT,
            )
            res.raise_for_status()
            source_url = res.json().get("source_url", "")
        except Exception as e:
            log(f"   ⚠️ R2 검증 불가 (미디어 조회 실패): {e}")
            return
        if not source_url:
            log("   ⚠️ R2 검증 불가: source_url 없음")
            return
        if source_url.startswith(R2_PUBLIC_BASE):
            # #9: R2 URL 자체를 HEAD로 먼저 확인한다.
            # 키에 wp-content/uploads/가 남아 있으면 경로 치환이 틀어져 오탐이 난다.
            try:
                r2_head = requests.head(source_url, timeout=SCRAPE_TIMEOUT)
                if r2_head.status_code != 200:
                    log(f"   ⚠️ R2 확인 불가 (R2 URL HTTP {r2_head.status_code}): {source_url}")
                    return
            except Exception as e:
                log(f"   ⚠️ R2 확인 불가 (R2 URL 조회 실패): {e}")
                return
            log(f"   ✅ R2 오프로드 확인: {source_url}")
            # 로컬본 잔존 여부 확인 (HEAD만으로 확인, 다운로드 안 함)
            local_url = source_url.replace(R2_PUBLIC_BASE, WP_UPLOADS_BASE, 1)
            try:
                head = requests.head(local_url, timeout=SCRAPE_TIMEOUT)
                if head.status_code == 200:
                    log(f"   ⚠️ 로컬본 잔존 (Cafe24에 아직 있음): {local_url}")
                elif head.status_code == 404:
                    # 경로 매핑 미확정 상태에서는 "삭제 확인"을 보고하지 않는다.
                    # 매핑은 실제 미디어 1건으로 확정해야 하며, 확정 전에는 unverifiable이다.
                    if R2_PATH_MAPPING_CONFIRMED:
                        log("   ✅ 로컬본 삭제 확인")
                    else:
                        log("   ⚠️ 로컬본 404이나 경로 매핑 미확정 — 삭제 확인 불가 (unverifiable)")
                else:
                    log(f"   ⚠️ 로컬본 확인 불가 (HTTP {head.status_code})")
            except Exception as e:
                log(f"   ⚠️ 로컬본 확인 불가: {e}")
        else:
            log(f"   ⚠️ 대표 이미지가 R2가 아님 (플러그인 미처리 가능): {source_url}")

    # ---------- git 커밋 ----------

    def commit_posted_articles(self) -> bool:
        """posted/skipped JSON을 커밋·푸시한다. 실패를 삼키지 않고 False를 반환한다."""
        try:
            subprocess.run(["git", "config", "user.email", "action@github.com"], check=True)
            subprocess.run(["git", "config", "user.name", "GitHub Action"], check=True)
            # #1: 존재하는 파일만 git add한다 (skipped 파일이 없어도 실패하지 않게).
            # B-3(d): draft 기록 파일도 같은 방식으로 커밋한다.
            add_files = [f for f in (POSTED_ARTICLES_FILE, POSTED_ARTICLES_DRAFT_FILE, SKIPPED_ARTICLES_FILE) if Path(f).exists()]
            if not add_files:
                log("   ⚠️ 커밋할 상태 파일이 없음")
                return True
            subprocess.run(["git", "add", *add_files], check=True)
            result = subprocess.run(["git", "diff", "--cached", "--quiet"], capture_output=True)
            if result.returncode != 0:
                subprocess.run(["git", "commit", "-m",
                    f"chore: update posted_articles [{datetime.now().strftime('%Y-%m-%d %H:%M')}]"], check=True)
                # #8: 푸시 전 rebase — 런 도중 main에 들어온 커밋이 있으면 거절되지 않게.
                try:
                    subprocess.run(["git", "pull", "--rebase"], check=True)
                except subprocess.CalledProcessError as e:
                    log(f"❌ git pull --rebase 실패: {e}")
                    return False
                subprocess.run(["git", "push"], check=True)
                log("📝 상태 파일 커밋 완료")
            else:
                log("📝 커밋할 변경 없음")
            return True
        except subprocess.CalledProcessError as e:
            log(f"❌ git 커밋/푸시 실패: {e}")
            return False

    # ---------- 텍스트 유틸 / SEO 보강 ----------

    def _strip_html(self, html_text: str) -> str:
        # §4-10: HTML이 아닌 입력(URL·파일명 등)은 BeautifulSoup에 넣지 않는다.
        text = html_text or ""
        if "<" not in text:
            return re.sub(r"\s+", " ", text).strip()
        try:
            soup = BeautifulSoup(text, "lxml")
            plain = soup.get_text(" ", strip=True)
            return re.sub(r"\s+", " ", plain).strip()
        except Exception:
            return text.strip()

    def build_lede_summary(self, excerpt: str, tldr_html: str) -> str:
        """2~3문장 요약을 본문 최상단에 넣기 위한 텍스트 생성. 우선순위: excerpt → tldr → 빈 문자열"""
        base = (excerpt or "").strip()
        if not base:
            base = self._strip_html(tldr_html)
        if not base:
            return ""
        parts = re.split(r"(?<=[\.\!\?\u2026])\s+|(?<=다\.)\s+|(?<=요\.)\s+", base)
        parts = [p.strip() for p in parts if p.strip()]
        summary = " ".join(parts[:3]).strip()
        if len(summary) > 380:
            summary = summary[:377].rstrip() + "..."
        return summary

    def fetch_recent_posts(self, per_page: int = 50) -> list:
        """내부링크 후보를 만들기 위해 최근 게시글을 가져온다. 실패하면 빈 리스트 반환."""
        try:
            res = requests.get(
                f"{self.wordpress_api}/posts",
                params={"per_page": per_page, "status": "publish"},
                timeout=WP_TIMEOUT,
            )
            if res.status_code != 200:
                return []
            return res.json()
        except Exception:
            return []

    def pick_related_posts(self, title: str, limit: int = 3) -> list:
        """매우 단순한 토큰 겹침 기반 관련 글 선택(빠르고 안정적)."""
        posts = self.fetch_recent_posts(per_page=60)
        if not posts:
            return []

        def tokens(s: str) -> set:
            s = (s or "").lower()
            return set(re.findall(r"[a-z0-9]+|[가-힣]{2,}", s))

        t_tokens = tokens(title)
        if not t_tokens:
            return []

        scored = []
        for p in posts:
            p_title = self._strip_html(p.get("title", {}).get("rendered", ""))
            p_link = p.get("link", "")
            if not p_link:
                continue
            p_tokens = tokens(p_title)
            score = len(t_tokens & p_tokens)
            if score <= 0:
                continue
            scored.append((score, p_title, p_link))

        scored.sort(key=lambda x: (-x[0], x[1]))
        picked = []
        used_links = set()
        for _, pt, pl in scored:
            if pl in used_links:
                continue
            used_links.add(pl)
            picked.append({"title": pt, "link": pl})
            if len(picked) >= limit:
                break
        return picked

    def build_internal_links_html(self, title: str, limit: int = 3) -> str:
        related = self.pick_related_posts(title, limit=limit)
        pronews_category_url = f"{WORDPRESS_URL}/category/pronews/"
        if not related:
            return (
                "<hr style='margin:32px 0 18px 0;border:0;border-top:1px solid #e0e0e0;'>\n"
                "<h3 style='margin:0 0 10px 0;'>관련 글</h3>\n"
                "<ul>\n"
                f"<li><a href='{pronews_category_url}'>proNEWS 카테고리</a></li>\n"
                f"<li><a href='{WORDPRESS_URL}/'>홈</a></li>\n"
                "</ul>\n"
            )
        items = "\n".join(
            f"<li><a href='{html.escape(r['link'])}'>{html.escape(r['title'])}</a></li>"
            for r in related
        )
        return (
            "<hr style='margin:32px 0 18px 0;border:0;border-top:1px solid #e0e0e0;'>\n"
            "<h3 style='margin:0 0 10px 0;'>관련 글</h3>\n"
            "<ul>\n"
            f"{items}\n"
            "</ul>\n"
        )


    # ---------- 기사 처리 ----------

    def process_article(self, article: dict) -> str:
        """기사 1건을 처리한다. 결과 상태를 반환한다.
        "published" / "duplicate" / "skipped" / "failed" (#6: 종료 코드 판정용)."""
        log(f"\n{'=' * 60}")
        log(f"📰 {article['title'][:70]}")
        log(f"📅 {article['date'].strftime('%Y-%m-%d %H:%M')} [{article.get('source', '?')}]")
        log(f"{'=' * 60}")

        if self.gemini.rate_limit_hit:
            log("🛑 429 플래그 → 다음 런 이월")
            return "failed"

        if not FORCE_UPDATE and self.is_already_posted_on_wp(article["link"]):
            # B-3(a): draft 모드에서는 posted_articles.json을 쓰지 않는다.
            if POST_STATUS == "publish" and article["link"] not in self.posted_articles:
                self.posted_articles.append(article["link"])
                self.save_posted_articles()
                self.posted_dirty = True  # #6: 중복으로 추가한 기록도 커밋 대상
            return "duplicate"

        body_text, exact_date = self.fetch_full_content(article["link"])
        if not body_text:
            log("⚠️ 본문 스크래핑 실패 → 스킵")
            return "failed"

        if exact_date:
            article["date"] = exact_date
            log(f"🕒 원문 시각 복원 성공: {exact_date.strftime('%Y-%m-%d %H:%M:%S')}")

        # §3-7: 번역 "전" 길이 검사 — 짧은 글을 번역한 뒤 스킵하는 Gemini 낭비 방지.
        source_len = len(self._strip_html(body_text))
        if source_len < MIN_SOURCE_CHARS:
            log(f"⚠️ 원문 너무 짧음 ({source_len}자 < {MIN_SOURCE_CHARS}자) → 번역 없이 스킵")
            self.mark_skipped(article["link"], f"원문 {source_len}자")
            return "skipped"
        log(f"   ✅ 원문 길이: {source_len}자")

        log("🔄 [1단계] Gemini 번역 (1회 JSON 통합)...")
        translated = self.gemini.translate_article(article["title"], body_text)

        if not translated or not translated.get("title") or not translated.get("content"):
            log("❌ 번역 실패 → 스킵")
            return "failed"

        title_ko = translated["title"]
        content_ko = translated["content"]
        excerpt = translated.get("excerpt", "")
        tldr_html = translated.get("tldr", "")
        log(f"   📌 제목: {title_ko}")

        if self.gemini._has_japanese(content_ko):
            log("   ⚠️ 일본어 잔존 → 재번역 1회 시도...")
            content_ko = self.gemini.retranslate_content(content_ko)
            if self.gemini._has_japanese(content_ko):
                log("   ⚠️ 재번역 후 일부 잔존 → 경고 후 게시 진행")

        # 번역 후 불필요 문구 제거
        remove_phrases = [
            "※이미지를 클릭하여 확대", "※ 이미지를 클릭하여 확대",
            "이미지를 클릭하면 확대됩니다", "클릭하면 확대 표시됩니다",
            "이미지를 클릭하여 확대하세요", "※이미지 클릭으로 확대",
        ]
        for phrase in remove_phrases:
            content_ko = content_ko.replace(phrase, "")

        # 코멘트 도입부만 남고 내용이 없는 패턴 제거
        soup = BeautifulSoup(content_ko, "lxml")
        comment_patterns = re.compile(
            r".{0,30}(다음과 같이 말했다|이렇게 말했다|다음과 같이 밝혔다|아래와 같이 코멘트했다"
            r"|다음과 같이 코멘트|이와 같이 말했다|다음과 같이 전했다)\s*[\.。]?\s*$"
        )
        for tag in soup.find_all(["p", "div"]):
            text = tag.get_text(strip=True)
            if comment_patterns.search(text) and len(text) < 80:
                tag.decompose()
        # <body> 태그 누수 수정: str(soup.body)는 <body>…</body>까지 포함하므로
        # decode_contents()로 안쪽 HTML만 쓴다.
        content_ko = soup.body.decode_contents() if soup.body is not None else str(soup)

        # 번역 후 글자수 체크 (안전망 — 번역 전 검사 통과 후에도 짧아지면 스킵 + 기록)
        plain_length = len(self._strip_html(content_ko))
        if plain_length < MIN_TRANSLATED_CHARS:
            log(f"⚠️ 번역 본문 너무 짧음 ({plain_length}자 < {MIN_TRANSLATED_CHARS}자) → 스킵")
            self.mark_skipped(article["link"], f"번역본 {plain_length}자")
            return "skipped"
        log(f"   ✅ 번역 본문 길이: {plain_length}자")

        slug = self.generate_seo_slug(title_ko, article["date"], title_ja=article.get("title", ""))
        log(f"🔗 Slug: {slug}")

        log("🔍 특성 이미지(Featured Image) 처리 중...")
        featured_id = 0
        img_url = self.get_main_image_url(article["link"])
        if img_url:
            local_img = self.download_image(img_url)
            if local_img:
                media_info = self.upload_media(local_img)
                if media_info:
                    featured_id = media_info["id"]
                try:
                    local_img.unlink()
                except Exception:
                    pass

        # ── SEO 보강: 2~3문장 요약 + 내부링크 ──
        lede_summary = self.build_lede_summary(excerpt, tldr_html)
        internal_links_html = self.build_internal_links_html(title_ko, limit=3)

        final_content = ""
        if lede_summary:
            final_content += (
                "<p style='font-size:15px;line-height:1.7;color:#222;margin:0 0 18px 0;'>"
                f"{lede_summary}</p>\n"
            )

        if tldr_html:
            final_content += (
                '<div style="background:#f8f9fa;padding:20px;border-radius:8px;'
                'border-left:5px solid #0056b3;margin-bottom:30px;">\n'
                '<h3 style="margin-top:0;color:#0056b3;">💡 핵심 요약</h3>\n'
                f"{tldr_html}\n</div>\n\n"
            )

        final_content += content_ko
        final_content += "\n\n" + internal_links_html
        final_content += (
            "\n\n<hr style='margin:40px 0 20px 0;border:0;border-top:1px solid #e0e0e0;'>\n"
            f"<p style='font-size:13px;color:#777;'><strong>원문:</strong> "
            f"<a href='{article['link']}' target='_blank' rel='noopener'>{article['title']}</a></p>"
        )

        label = "draft(임시저장)" if POST_STATUS == "draft" else "publish(즉시공개)"
        log(f"📤 [2단계] WordPress {label} 중...")

        post = self.post_to_wordpress(title_ko, final_content, slug, featured_id,
                                      article["date"], excerpt=excerpt, status=POST_STATUS)
        if post:
            # C1: publish 모드일 때만 공개 URL 검증 (draft URL은 익명으로 200이 안 됨).
            # 검증에 실패하면 게시 기록을 남기지 않고 실패 처리 — 다음 런 WP 2차 검사가 회수한다.
            if POST_STATUS == "publish":
                post_link = post.get("link", "")
                if not post_link or not self.verify_published_url(post_link):
                    log("   ❌ 배포 검증 실패 → 게시 기록을 남기지 않고 실패 처리")
                    return "failed"
            # [신규] R2 이관 검증 (경고만, 실패시켜지 않음)
            self.verify_r2_offload(featured_id)
            if not FORCE_UPDATE:
                if POST_STATUS == "draft":
                    # B-3(a): draft 모드에서는 테스트 기록 파일에만 남긴다.
                    self.posted_articles_draft.append({
                        "url": article["link"],
                        "wp_post_id": post.get("id"),
                        "slug": slug,
                        "date": datetime.now().strftime("%Y-%m-%d"),
                    })
                    self.save_posted_articles_draft()
                    self.posted_draft_dirty = True
                    self._clear_skipped(article["link"])
                else:
                    self.posted_articles.append(article["link"])
                    self.save_posted_articles()
                    self.posted_dirty = True
                    self._clear_skipped(article["link"])
            return "published"
        return "failed"

    def verify_published_url(self, url: str) -> bool:
        """C1: 발행한 글의 공개 URL이 HTTP 200을 돌려주는지 확인한다.
        WP·캐시 반영 지연을 감안해 DEPLOY_VERIFY_TIMEOUT까지 재시도한다."""
        deadline = time.time() + DEPLOY_VERIFY_TIMEOUT
        while True:
            try:
                res = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=SCRAPE_TIMEOUT)
                if res.status_code == 200:
                    log(f"   ✅ 배포 검증 통과 (HTTP 200): {url}")
                    return True
                log(f"   ⚠️ 배포 검증 대기 (HTTP {res.status_code}): {url}")
            except Exception as e:
                log(f"   ⚠️ 배포 검증 대기 (오류): {e}")
            if time.time() >= deadline:
                log(f"   ❌ 배포 검증 실패 ({DEPLOY_VERIFY_TIMEOUT}초 내 200 없음): {url}")
                return False
            time.sleep(DEPLOY_VERIFY_INTERVAL)

    # ---------- 실행 ----------

    def cleanup_test_drafts(self) -> int:
        """B-3(c): 테스트 draft 정리. posted_articles_draft.json의 각 항목을
        REST API로 확인해 draft 상태인 것만 휴지통으로 이동한다.
        draft가 아닌 글은 절대 건드리지 않는다. 정리 결과를 표로 출력하고
        파일을 갱신·커밋한 뒤 종료한다."""
        entries = list(self.posted_articles_draft)
        if not entries:
            log("🧹 정리할 테스트 draft 없음")
            return 0
        rows = []  # (id, slug, action)
        remaining = []
        for entry in entries:
            wp_id = entry.get("wp_post_id") if isinstance(entry, dict) else None
            slug = entry.get("slug", "") if isinstance(entry, dict) else ""
            if not wp_id:
                rows.append((wp_id, slug, "skipped-not-draft"))
                remaining.append(entry)
                continue
            try:
                res = requests.get(
                    f"{self.wordpress_api}/posts/{wp_id}",
                    auth=(WORDPRESS_USER, WORDPRESS_APP_PASSWORD),
                    timeout=WP_TIMEOUT,
                )
            except Exception as e:
                log(f"⚠️ draft {wp_id} 확인 실패: {e}")
                rows.append((wp_id, slug, "error"))
                remaining.append(entry)
                continue
            if res.status_code == 404:
                rows.append((wp_id, slug, "not-found"))
                continue  # 이미 없음 → 파일에서 제거
            if res.status_code != 200:
                rows.append((wp_id, slug, "error"))
                remaining.append(entry)
                continue
            post = res.json()
            if post.get("status") != "draft":
                rows.append((wp_id, slug, "skipped-not-draft"))
                remaining.append(entry)
                continue
            # draft 확인됨 → 휴지통으로 이동 (force 없이 DELETE)
            try:
                del_res = requests.delete(
                    f"{self.wordpress_api}/posts/{wp_id}",
                    auth=(WORDPRESS_USER, WORDPRESS_APP_PASSWORD),
                    timeout=WP_TIMEOUT,
                )
                if del_res.status_code in (200, 204):
                    rows.append((wp_id, slug, "trashed"))
                else:
                    log(f"⚠️ draft {wp_id} 휴지통 이동 실패 (HTTP {del_res.status_code})")
                    rows.append((wp_id, slug, "error"))
                    remaining.append(entry)
            except Exception as e:
                log(f"⚠️ draft {wp_id} 휴지통 이동 실패: {e}")
                rows.append((wp_id, slug, "error"))
                remaining.append(entry)
        log("\n🧹 테스트 draft 정리 결과:")
        log(f"{'id':>8}  {'slug':<40}  action")
        for wp_id, slug, action in rows:
            log(f"{str(wp_id):>8}  {slug:<40}  {action}")
        self.posted_articles_draft = remaining
        self._atomic_write_json(POSTED_ARTICLES_DRAFT_FILE, remaining)
        self.posted_draft_dirty = True
        if not self.commit_posted_articles():
            log("❌ 정리 기록 커밋 실패")
            return 1
        self.posted_draft_dirty = False
        if any(action == "error" for _, _, action in rows):
            log("❌ 정리 중 오류 발생 (error 항목 있음)")
            return 1
        return 0

    def run(self) -> int:
        """실행하고 종료 코드를 반환한다. 0=성공, 1=실패. (§3-3)"""
        log(f"\n{'=' * 60}")
        log(f"pronews.jp → prodg.kr 자동 번역 v{VERSION}")
        log(f"엔진: {GEMINI_MODEL} | 호출: 기사당 1회 JSON 통합")
        log(f"모드: {'자동 (최신→아카이브 보충)' if IS_SCHEDULED else '수동 (아카이브 오래된 순)'}")
        log(f"실행 모드: {EFFECTIVE_EVENT} (override={os.environ.get('RUN_MODE_OVERRIDE', '').strip() or 'none'})")
        log(f"게시: {POST_STATUS.upper()} | 일일 한도: {DAILY_LIMIT}건")
        log(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        log(f"{'=' * 60}\n")

        if not WORDPRESS_USER or not WORDPRESS_APP_PASSWORD:
            log("❌ WP_USER / WP_APP_PASSWORD 환경변수 필요")
            return 1

        if CLEANUP_TEST_DRAFTS:
            # B-3(c): 테스트 draft 정리만 수행하고 종료한다 (Gemini 불필요).
            return self.cleanup_test_drafts()

        log("🔑 Gemini API 키 검증...")
        test = self.gemini._call_api("テスト를 한국어로 번역:", max_tokens=30)
        if not test:
            log("❌ Gemini API 키 오류 → 종료")
            return 1
        log(f"   ✅ API 정상: '{test}'")

        articles, fetch_failed = self.get_articles_to_process()
        if fetch_failed:
            log("❌ 수집 소스(RSS+아카이브) 전부 실패 → 런 실패 처리")
            return 1
        if not articles:
            log("✅ 처리할 기사 없음 (신규 기사 없음 — 정상 종료)")
            return 0

        self.skipped_this_run = 0
        counts = {"published": 0, "duplicate": 0, "skipped": 0, "failed": 0}
        half_skipped = False
        commit_ok = True
        try:
            for i, article in enumerate(articles, 1):
                if self.gemini.rate_limit_hit:
                    log(f"\n🛑 429 런 종료 → 남은 {len(articles) - i + 1}건 다음 런 이월")
                    break
                log(f"\n[{i}/{len(articles)}]")
                # #7: 기사 단위 try/except — 한 기사의 예상 못 한 예외가 런 전체를 죽이지 않게.
                try:
                    outcome = self.process_article(article)
                except Exception as e:
                    log(f"❌ 기사 처리 중 예상 못 한 예외 ({article.get('link', '?')}): {e}")
                    outcome = "failed"
                if outcome not in counts:
                    outcome = "failed"
                counts[outcome] += 1
                if i < len(articles):
                    time.sleep(10)
        except Exception as e:
            log(f"❌ 런 루프 중 예상 못 한 예외: {e}")
            counts["failed"] += 1
        finally:
            # #7: 상태 커밋은 finally 안에서 — 루프 중 예외가 나도 게시 기록을 남긴다.
            log(f"\n{'=' * 60}")
            log(f"🏁 완료: 게시 {counts['published']} / 중복 {counts['duplicate']} / "
                f"스킵 {counts['skipped']} / 실패 {counts['failed']} (대상 {len(articles)}건)")
            log(f"{'=' * 60}\n")
            # #4: 대상의 절반 이상이 스킵되면 skipped를 저장하지 않는다
            # (일시적 문제로 대량 스킵이 영구 블랙리스트가 되는 것을 방지).
            # (재검수 2번) 소규모 런(1/1, 2/2)의 오탐 방지: 스킵이 3건 이상일 때만 적용한다.
            half_skipped = self.skipped_this_run >= 3 and self.skipped_this_run > len(articles) / 2
            if half_skipped:
                log(f"❌ 스킵 {self.skipped_this_run}건이 대상 {len(articles)}건의 절반 초과 "
                    f"→ skipped 목록을 저장하지 않고 런 실패 처리")
            # 커밋 여부 판단 (save가 dirty 플래그를 지우기 전에 판단한다).
            save_skipped = self.skipped_dirty and not half_skipped
            need_commit = self.posted_dirty or self.posted_draft_dirty or save_skipped
            if save_skipped:
                self.save_skipped_articles()
            if need_commit:
                commit_ok = self.commit_posted_articles()
                if commit_ok:
                    self.posted_dirty = False
                    self.posted_draft_dirty = False
                else:
                    log("❌ 상태 커밋 실패 → 런 실패 처리 (게시 기록 유실 방지)")

        if half_skipped:
            return 1
        if not commit_ok:
            return 1
        # #6: 실제 실패가 있고 게시 0건일 때만 exit 1.
        # 전부 중복/스킵이면 정상 종료(0) — 이미 게시됐거나 정당한 스킵이다.
        if counts["failed"] > 0 and counts["published"] == 0:
            log(f"❌ 실제 실패 {counts['failed']}건, 게시 0건 → 런 실패 처리")
            return 1
        return 0


def main() -> int:
    bot = NewsTranslator()
    return bot.run()


if __name__ == "__main__":
    sys.exit(main())
