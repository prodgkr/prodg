#!/usr/bin/env python3
"""Offline tests for the Japan/Korea translation-fidelity rules (PR: fix/japan-korea-translation).

No network access: GeminiEngine._call_api is monkeypatched to capture the
prompt and return canned output, and requests.post is patched to fail loudly
if anything ever tries real HTTP. Run with the repo venv python:

    python3 -m unittest -v test_translation_rules.py

Background (WP 5337, 2026-11-25): the DeviantArt article rendered source
"日本上陸 / 日本語" as "한국 시장 진출 / 한국어 지원" throughout, because the
translate prompt said "write like a Korean professional reporter" with no rule
keeping countries/markets/languages as in the source. These tests lock the new
rules into the prompts.
"""

import json
import os
import sys
import unittest
from unittest import mock

# Dummy key so the module import does not sys.exit; never a real credential.
os.environ.setdefault("GEMINI_API_KEY", "dummy-offline-test-key")

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import translate_and_post  # noqa: E402


CANNED_JSON = json.dumps(
    {
        "title": "테스트 제목",
        "content": "<p>테스트 본문</p>",
        "excerpt": "테스트 요약문이다.",
        "tldr": "<ul><li>요약1</li></ul>",
    },
    ensure_ascii=False,
)


class TestTranslationFidelityRules(unittest.TestCase):
    def setUp(self):
        self.captured_prompts = []

        def fake_call_api(_self, prompt, max_tokens=8192, response_mime_type=None):
            self.captured_prompts.append(prompt)
            return CANNED_JSON

        self._api_patch = mock.patch.object(
            translate_and_post.GeminiEngine, "_call_api", fake_call_api
        )
        self._api_patch.start()
        # Any real HTTP attempt must fail the test, not the network.
        self._http_patch = mock.patch.object(
            translate_and_post.requests,
            "post",
            side_effect=AssertionError("offline test must not touch the network"),
        )
        self._http_patch.start()
        self.engine = translate_and_post.GeminiEngine()

    def tearDown(self):
        self._http_patch.stop()
        self._api_patch.stop()

    def test_translate_article_prompt_keeps_japan(self):
        """Rule 7: countries/markets/languages stay as in the source."""
        result = self.engine.translate_article(
            "アートコミュニティ「DeviantArt」が日本上陸！",
            "<p>DeviantArtが日本市場に参入し、日本語編集ツールを提供する。国内の登録者は約140万人。</p>",
        )
        self.assertEqual(result["title"], "테스트 제목")
        self.assertEqual(len(self.captured_prompts), 1)
        prompt = self.captured_prompts[0]
        for required in (
            "日本→일본",
            "日本語→일본어",
            "日本市場→일본 시장",
            "한국으로 바꾸",
            "현지화하지 말 것",
        ):
            self.assertIn(required, prompt, f"missing from prompt: {required}")

    def test_translate_article_prompt_domestic_means_japan(self):
        """国内 (Japan domestic) must become '일본 내' / '일본 국내', never bare '국내'."""
        self.engine.translate_article("タイトル", "<p>国内の登録者。</p>")
        prompt = self.captured_prompts[0]
        self.assertIn('国内(일본 국내를 뜻함)→"일본 내" / "일본 국내"', prompt)
        self.assertIn('단독 "국내" 금지', prompt)

    def test_translate_article_prompt_keeps_yen(self):
        """Prices stay in yen: 円→엔, no conversion to won."""
        self.engine.translate_article("タイトル", "<p>価格は5,000円。</p>")
        prompt = self.captured_prompts[0]
        self.assertIn("円→엔", prompt)
        self.assertIn("원화로 환산 금지", prompt)

    def test_rule6_cross_references_rule7(self):
        """The 'Korean professional reporter' line must not override rule 7."""
        self.engine.translate_article("タイトル", "<p>本文</p>")
        prompt = self.captured_prompts[0]
        self.assertIn("한국 전문 기자가 직접 쓴 것처럼", prompt)
        self.assertIn("규칙 7의 국가·시장·언어 표기는 원문 그대로", prompt)

    def test_retranslate_content_prompt_keeps_japan(self):
        """The second-pass (leftover Japanese) prompt needs the same guard."""
        out = self.engine.retranslate_content("<p>日本語の部分が残っている。</p>")
        self.assertEqual(out, CANNED_JSON)
        prompt = self.captured_prompts[0]
        for required in ("日本→일본", "日本語→일본어", "日本市場→일본 시장", '国内→"일본 내"', "円→엔"):
            self.assertIn(required, prompt, f"missing from retranslate prompt: {required}")


if __name__ == "__main__":
    unittest.main()
