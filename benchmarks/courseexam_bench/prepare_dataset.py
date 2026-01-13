#!/usr/bin/env python3
from pathlib import Path

from courseexam.prepare import prepare_dataset


def main():
    script_dir = Path(__file__).parent
    data_dir = script_dir / "data"

    if not (data_dir / "raw").exists():
        raise FileNotFoundError(f"data/raw directory not found at {data_dir / 'raw'}")

    try:
        prepare_dataset(data_dir)
        return 0
    except Exception as e:
        print(f"Error: {e}")
        return 1


if __name__ == "__main__":
    exit(main())
