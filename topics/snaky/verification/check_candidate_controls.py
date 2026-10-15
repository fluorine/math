#!/usr/bin/env python3
"""Corrupt a candidate's root in memory and require local obligations to reject it.

The original whole certificate is checked separately by verify_cards.py.
"""

import argparse
from dataclasses import replace
import hashlib
import json
from pathlib import Path

from verify_cards import InvalidCertificate, check_card, parse_text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    data = args.certificate.read_bytes()
    certificate = parse_text(data.decode("ascii"))
    index = certificate.root.card
    root = certificate.cards[index]
    if root.height < 2:
        raise SystemExit("The controls require a nonterminal root of height at least two")
    white = min(set(root.support) - set(root.required) - {root.pivot})
    cases = (
        ("root_height_reduced_by_one", replace(root, height=root.height - 1), "height-descent"),
        ("root_response_removed", replace(root, responses=tuple(
            entry for entry in root.responses if entry[0] != white)), "missing-response"),
    )
    results = []
    for name, corrupted, expected in cases:
        cards = certificate.cards[:index] + (corrupted,) + certificate.cards[index + 1:]
        try:
            check_card(cards, index)
        except InvalidCertificate as error:
            if error.code != expected:
                raise SystemExit(f"Unexpected rejection for {name}: {error}")
            results.append({"control": name, "status": "rejected", "error": str(error)})
        else:
            raise SystemExit(f"Corruption was accepted: {name}")
    print(json.dumps({"status": "controls_passed", "root_index": index,
                      "original_root_height": root.height, "corrupted_root_height": root.height - 1,
                      "removed_response": list(white), "controls": results,
                      "certificate_sha256": hashlib.sha256(data).hexdigest(),
                      "verifier_sha256": hashlib.sha256(Path(__file__).with_name("verify_cards.py").read_bytes()).hexdigest()},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
