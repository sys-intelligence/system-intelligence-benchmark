from __future__ import annotations

import argparse
import json
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))

from sdk.executor import SimpleExecutor
from sdk.logger import logger
from sdk.utils import set_llm_endpoint_from_config

from evaluator import SpecFsJudgeEvaluator

GEN_DEFAULT_SYSTEM_PROMPT = 'You are an expert C systems programmer. Return robust, compilable C code only.'
JUDGE_DEFAULT_SYSTEM_PROMPT = 'You are a strict and fair C code reviewer and benchmark judge.'


def resolve_config_path(benchmark_root: Path) -> Path | None:
    """Resolve env config path, preferring local benchmark config."""
    local_config = benchmark_root / 'env.toml'
    workspace_config = benchmark_root.parent / 'env.toml'
    if local_config.exists():
        return local_config
    if workspace_config.exists():
        return workspace_config
    return None


def read_text(path: Path) -> str:
    """Read UTF-8 text."""
    return path.read_text(encoding='utf-8')


def discover_spec_files(spec_root: Path) -> list[Path]:
    """Discover all .spec files recursively."""
    return sorted(spec_root.rglob('*.spec'))


def make_default_output_dir(model_name: str, judge_model_name: str) -> Path:
    """Build default output directory with benchmark convention."""
    timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
    safe_model = model_name.replace('/', '_')
    safe_judge_model = judge_model_name.replace('/', '_')
    return Path('./outputs') / f'specfsbench__{safe_model}__judge_{safe_judge_model}__{timestamp}'


def rel_code_path_for_spec(spec_root: Path, spec_path: Path) -> Path:
    """Map spec file path to expected relative code path under data/code."""
    rel = spec_path.relative_to(spec_root)
    return rel.with_suffix('.c')


def load_prompt(prompt_file: Path) -> str:
    """Load prompt template."""
    text = read_text(prompt_file).strip()
    if text:
        return text
    raise ValueError(f'Prompt template is empty. Please provide a valid prompt in {prompt_file}.')


def run_generation(
    spec_files: list[Path],
    spec_root: Path,
    output_dir: Path,
    model_name: str,
    generation_user_template: str,
) -> list[dict[str, Any]]:
    """Run spec-to-code generation for each spec file."""
    generated_root = output_dir / 'generated'
    generated_root.mkdir(parents=True, exist_ok=True)

    executor = SimpleExecutor(model_name, GEN_DEFAULT_SYSTEM_PROMPT)
    results: list[dict[str, Any]] = []

    for index, spec_path in enumerate(spec_files, start=1):
        rel_code_path = rel_code_path_for_spec(spec_root, spec_path)
        output_code_path = generated_root / rel_code_path
        output_code_path.parent.mkdir(parents=True, exist_ok=True)

        spec_text = read_text(spec_path)
        prompt = generation_user_template.replace('{{SPEC_CONTENT}}', spec_text)

        record: dict[str, Any] = {
            'index': index,
            'spec_path': str(spec_path),
            'relative_code_path': str(rel_code_path),
            'generated_code_path': str(output_code_path),
            'status': 'success',
        }

        try:
            generated_code = executor.run(prompt, lang='c')
            output_code_path.write_text(generated_code, encoding='utf-8')
            record['generated_chars'] = len(generated_code)
        except Exception as exc:  # noqa: BLE001
            record['status'] = 'generation_error'
            record['error'] = str(exc)
            logger.error('Generation failed for %s: %s', spec_path, exc)

        results.append(record)

    return results


def run_judging(
    generation_results: list[dict[str, Any]],
    code_root: Path,
    judge_model_name: str,
    judge_user_template: str,
) -> list[dict[str, Any]]:
    """Run LLM judge over generated code and ground truth code."""
    evaluator = SpecFsJudgeEvaluator(
        model_name=judge_model_name,
        system_prompt=JUDGE_DEFAULT_SYSTEM_PROMPT,
        user_template=judge_user_template,
    )

    judge_results: list[dict[str, Any]] = []
    for item in generation_results:
        spec_path = Path(item['spec_path'])
        rel_code_path = Path(item['relative_code_path'])
        generated_code_path = Path(item['generated_code_path'])
        ground_truth_path = code_root / rel_code_path

        result: dict[str, Any] = {
            'spec_path': str(spec_path),
            'relative_code_path': str(rel_code_path),
            'generated_code_path': str(generated_code_path),
            'ground_truth_path': str(ground_truth_path),
            'status': 'success',
            'score': None,
            'verdict': None,
            'summary': None,
            'differences': [],
        }

        if item.get('status') != 'success':
            result['status'] = 'skip_generation_error'
            judge_results.append(result)
            continue

        if not generated_code_path.exists():
            result['status'] = 'missing_generated'
            judge_results.append(result)
            continue

        if not ground_truth_path.exists():
            result['status'] = 'missing_ground_truth'
            judge_results.append(result)
            continue

        try:
            spec_text = read_text(spec_path)
            generated_code = read_text(generated_code_path)
            ground_truth_code = read_text(ground_truth_path)
            judge_out = evaluator.eval_case(spec_text=spec_text, generated_code=generated_code, ground_truth_code=ground_truth_code)

            result['score'] = judge_out.score
            result['verdict'] = judge_out.verdict
            result['summary'] = judge_out.summary
            result['differences'] = judge_out.differences
            result['raw_judge_response'] = judge_out.raw_judge_response
        except Exception as exc:  # noqa: BLE001
            result['status'] = 'judge_error'
            result['error'] = str(exc)
            logger.error('Judge failed for %s: %s', spec_path, exc)

        judge_results.append(result)

    return judge_results


def write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    """Write records to jsonl."""
    with path.open('w', encoding='utf-8') as output_file:
        for item in records:
            output_file.write(json.dumps(item, ensure_ascii=False) + '\\n')


def build_summary(
    model_name: str,
    judge_model_name: str,
    generation_results: list[dict[str, Any]],
    judge_results: list[dict[str, Any]],
) -> dict[str, Any]:
    """Build summary stats."""
    generation_success = [item for item in generation_results if item.get('status') == 'success']
    generation_errors = [item for item in generation_results if item.get('status') != 'success']

    judged = [item for item in judge_results if item.get('status') == 'success' and isinstance(item.get('score'), (int, float))]
    missing_ground_truth = [item for item in judge_results if item.get('status') == 'missing_ground_truth']
    judge_errors = [item for item in judge_results if item.get('status') == 'judge_error']
    skipped_generation = [item for item in judge_results if item.get('status') == 'skip_generation_error']

    avg_score = sum(float(item['score']) for item in judged) / len(judged) if judged else 0.0

    summary = {
        'model_name': model_name,
        'judge_model_name': judge_model_name,
        'timestamp': datetime.now().isoformat(),
        'generation': {
            'total_specs': len(generation_results),
            'success_count': len(generation_success),
            'error_count': len(generation_errors),
        },
        'judge': {
            'total_cases': len(judge_results),
            'judged_count': len(judged),
            'missing_ground_truth_count': len(missing_ground_truth),
            'judge_error_count': len(judge_errors),
            'skipped_generation_error_count': len(skipped_generation),
            'avg_score_10': round(avg_score, 4),
            'avg_score_100': round(avg_score * 10, 2),
        },
    }
    return summary


def main(args: argparse.Namespace) -> None:
    """Run benchmark pipeline."""
    current_dir = Path(__file__).resolve().parent
    benchmark_root = current_dir.parent

    config_path = resolve_config_path(benchmark_root)
    if config_path is not None:
        logger.info('Loading config from: %s', config_path)
        set_llm_endpoint_from_config(str(config_path))
    else:
        logger.warning('No env.toml found. Relying on environment variables only.')

    spec_root = (benchmark_root / args.spec_dir).resolve()
    code_root = (benchmark_root / args.code_dir).resolve()

    if not spec_root.exists():
        raise FileNotFoundError(f'Spec directory not found: {spec_root}')

    output_dir = Path(args.output_dir).resolve() if args.output_dir else make_default_output_dir(args.model_name, args.judge_model_name).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    spec_files = discover_spec_files(spec_root)
    if args.max_cases is not None and args.max_cases > 0:
        spec_files = spec_files[: args.max_cases]

    generation_prompt_file = current_dir / 'genspec_prompt.md'
    judge_prompt_file = current_dir / 'judge_prompt.md'
    generation_user_template = load_prompt(generation_prompt_file)
    judge_user_template = load_prompt(judge_prompt_file)

    logger.info('Discovered %s spec files.', len(spec_files))

    generation_results = run_generation(
        spec_files=spec_files,
        spec_root=spec_root,
        output_dir=output_dir,
        model_name=args.model_name,
        generation_user_template=generation_user_template,
    )
    write_jsonl(output_dir / 'generation_results.jsonl', generation_results)

    judge_results: list[dict[str, Any]] = []
    if not args.skip_judge:
        judge_results = run_judging(
            generation_results=generation_results,
            code_root=code_root,
            judge_model_name=args.judge_model_name,
            judge_user_template=judge_user_template,
        )
        write_jsonl(output_dir / 'judge_results.jsonl', judge_results)

    summary = build_summary(
        model_name=args.model_name,
        judge_model_name=args.judge_model_name,
        generation_results=generation_results,
        judge_results=judge_results,
    )

    with (output_dir / 'summary.json').open('w', encoding='utf-8') as summary_file:
        json.dump(summary, summary_file, ensure_ascii=False, indent=2)

    logger.info('SpecFS benchmark finished.')
    logger.info('Outputs: %s', output_dir)
    logger.info('Summary: %s', summary)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='SpecFS Benchmark')
    parser.add_argument('-m', '--model_name', required=True, help='Model name for code generation')
    parser.add_argument('--judge_model_name', default=None, help='Model name for judge (default: same as model_name)')
    parser.add_argument('-o', '--output_dir', default=None, help='Output directory path')
    parser.add_argument('--spec_dir', default='data/spec', help='Relative path to spec directory')
    parser.add_argument('--code_dir', default='data/code', help='Relative path to ground-truth code directory')
    parser.add_argument('--max_cases', type=int, default=None, help='Optional max number of specs to run')
    parser.add_argument('--skip_judge', action='store_true', help='Skip judge stage')

    args = parser.parse_args()
    if args.judge_model_name is None:
        args.judge_model_name = args.model_name

    main(args)
