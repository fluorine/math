#!/usr/bin/env python3
"""Set the data-file size while preserving the pinned upstream generator.

All remaining arguments are passed to cards2lean.py unchanged. Only its
PER_FILE grouping constant is overridden; card data and proof rules are not.
"""
import argparse
from pathlib import Path
import runpy
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-cards", type=int, required=True)
    args, remaining = parser.parse_known_args()
    if args.data_cards < 1:
        parser.error("--data-cards must be positive")
    upstream = Path(__file__).with_name("cards2lean.py")
    namespace = runpy.run_path(str(upstream), run_name="snaky_sized_generator")
    namespace["main"].__globals__["PER_FILE"] = args.data_cards
    sys.argv = [str(upstream), *remaining]
    namespace["main"]()


if __name__ == "__main__":
    main()
