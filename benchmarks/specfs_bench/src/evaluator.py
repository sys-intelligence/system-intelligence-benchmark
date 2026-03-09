"""LLM-as-a-judge evaluator for SpecFS benchmark."""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from typing import Any

from sdk.llm import LLM


@dataclass
class JudgeResult:
    """Single judge result."""

    score: float
    verdict: str
    summary: str
    differences: list[str]
    raw_judge_response: str


class JudgeEvaluator:
    """Evaluate generated C code against ground truth using an LLM judge."""

    def __init__(self, model_name: str, prompt_template: str) -> None:
        self.model_name = model_name
        self.prompt_template = prompt_template

    def _build_prompt(self, spec_text: str, generated_code: str, ground_truth_code: str) -> str:
        return (
            self.prompt_template.replace('{{SPEC_CONTENT}}', spec_text)
            .replace('{{GENERATED_CODE}}', generated_code)
            .replace('{{GROUND_TRUTH_CODE}}', ground_truth_code)
        )

    def _parse_json(self, text: str) -> dict[str, Any]:
        """Parse JSON from plain text or fenced code block."""
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            pass

        match = re.search(r'```json\s*(\{.*?\})\s*```', text, re.DOTALL)
        if match:
            try:
                return json.loads(match.group(1))
            except json.JSONDecodeError:
                return {}
        return {}

    @staticmethod
    def _normalize_score(score: Any) -> float:
        try:
            value = float(score)
        except (TypeError, ValueError):
            return 0.0
        return max(0.0, min(10.0, value))

    def eval_case(self, spec_text: str, generated_code: str, ground_truth_code: str) -> JudgeResult:
        """Judge one generated file."""
        llm = LLM(engine=self.model_name, temperature=0.0, json_format=True)
        prompt = self._build_prompt(spec_text=spec_text, generated_code=generated_code, ground_truth_code=ground_truth_code)
        raw_response = llm.query(prompt)

        parsed = self._parse_json(raw_response)
        score = self._normalize_score(parsed.get('score'))
        verdict = str(parsed.get('verdict', 'unknown')).strip() or 'unknown'
        summary = str(parsed.get('summary', '')).strip()

        diffs = parsed.get('differences', [])
        if not isinstance(diffs, list):
            diffs = [str(diffs)]
        differences = [str(item).strip() for item in diffs if str(item).strip()]

        return JudgeResult(
            score=score,
            verdict=verdict,
            summary=summary,
            differences=differences,
            raw_judge_response=raw_response,
        )
