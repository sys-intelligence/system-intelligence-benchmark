"""Tests for the example benchmark."""

import json
import unittest
from pathlib import Path


class TestExampleBenchmark(unittest.TestCase):
    def test_data_format(self):
        """Test that benchmark data is in the correct format."""
        data_path = (
            Path(__file__).parent.parent
            / "data"
            / "benchmark"
            / "example_bench_benchmark_timestamp.jsonl"
        )

        self.assertTrue(
            data_path.exists(), f"Benchmark data file not found: {data_path}"
        )

        with open(data_path, encoding="utf-8") as f:
            for line_num, line in enumerate(f, 1):
                data = json.loads(line)

                # Check required fields
                self.assertIn("id", data, f'Line {line_num}: missing "id" field')
                self.assertIn(
                    "sys_prompt", data, f'Line {line_num}: missing "sys_prompt" field'
                )
                self.assertIn(
                    "user_prompt", data, f'Line {line_num}: missing "user_prompt" field'
                )
                self.assertIn(
                    "response", data, f'Line {line_num}: missing "response" field'
                )

                # Check field types
                self.assertIsInstance(
                    data["id"], str, f'Line {line_num}: "id" must be a string'
                )
                self.assertIsInstance(
                    data["sys_prompt"],
                    str,
                    f'Line {line_num}: "sys_prompt" must be a string',
                )
                self.assertIsInstance(
                    data["user_prompt"],
                    str,
                    f'Line {line_num}: "user_prompt" must be a string',
                )
                self.assertIsInstance(
                    data["response"],
                    str,
                    f'Line {line_num}: "response" must be a string',
                )


if __name__ == "__main__":
    unittest.main()
