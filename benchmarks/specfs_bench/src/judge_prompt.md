[TASK]
You are an impartial judge for C code generation benchmark.
Compare `GENERATED_CODE` against `GROUND_TRUTH_CODE` under the same `SPEC_CONTENT`.

[SCORING]
- score: 0-10 (10 = fully equivalent and correct)
- Focus on functional correctness first; style is secondary.
- Penalize missing edge-case handling, contract violations, unsafe memory handling, incorrect return behavior, and broken API usage.

[OUTPUT_FORMAT]
Return JSON ONLY (no markdown, no extra text):
{
	"score": <number 0-10>,
	"verdict": "pass" | "partial" | "fail",
	"summary": "short rationale",
	"differences": ["difference 1", "difference 2"]
}

[SPEC_CONTENT]
{{SPEC_CONTENT}}

[GENERATED_CODE]
{{GENERATED_CODE}}

[GROUND_TRUTH_CODE]
{{GROUND_TRUTH_CODE}}
