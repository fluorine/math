#!/usr/bin/env python3
"""Extract two accepted conditional dependency closures for kernel checking.

Only exact structural equality after dependency renumbering is deduplicated.
Coordinates, support/requirement order, first-match reply order and all
transforms are retained. The source board headers remain provenance; the
actual theorem uses the explicit 14 by 14 positions and translated frames.
No empty-root obligation is generated for these nonempty positions.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

import cards2lean

FORMAL = Path(__file__).resolve().parents[1]
BOARD = FORMAL.parent / "board_size"
GEN = FORMAL / "Snaky/GenMakerOpening"
AUDIT_PINS = {
    "verification/cover-empty14-d8-b16-conditional-library-audit.json":
        "8c459ce2c856fecfff4f31463cae22367190ee35a0202227f68ba48e5123ab08",
    "verification/opening-b7-10-audit.json":
        "174762c1e2fa24c9c07cc7896ad548255c7ad506816d7ce6c7cc874b9442d4d3",
}
SOURCES = (
    ("cover-empty14-d8-b16.cards.txt",
     "0562d22136cd204c985f6b9530cefba3d16185ca3448f81ef8c509892428e6d3",
     "verification/cover-empty14-d8-b16-conditional-library-audit.json",
     28628, 1686, (6, 6), 19),
    ("opening-cover-initial-b7-10.cards.txt",
     "b30f0615135a0265cd64d5b8a809ce7eb567a8c55c192a0b889bd33ab6928f60",
     "verification/opening-b7-10-audit.json",
     20870, 350, (7, 10), 15),
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependencies(card):
    return ([card["pass"]] if card["pass"] is not None else []) + [h for _, h in card["replies"]]


def serialize(cards, root):
    lines = [f"snaky-cards-txt-v1 17 17 {root} 0 0 0"]
    for card in cards:
        row = [card["h"], *card["p"]]
        for field in ("A", "S"):
            row += [len(card[field]), *(v for point in card[field] for v in point)]
        row += list(card["pass"]) if card["pass"] is not None else [-1]
        row += [len(card["replies"])]
        for point, hint in card["replies"]:
            row += [*point, *hint]
        lines.append(" ".join(map(str, row)))
    return "\n".join(lines) + "\n"


def extract():
    cards_out, keys, maps, source_reports, roots = [], {}, [], [], []
    for name, digest, audit_name, expected_root, expected_count, breaker, height in SOURCES:
        path, audit_path = BOARD / name, BOARD / audit_name
        if sha(path) != digest or sha(audit_path) != AUDIT_PINS[audit_name]:
            raise ValueError("changed accepted input: " + name)
        header, cards = cards2lean.parse(path)
        audit = json.loads(audit_path.read_text())
        if (header[2] != expected_root or audit["certificate_sha256"] != digest
                or audit["status"] != "independently_verified_conditional_tactic"
                or audit["maker"] != [[7, 7]] or audit["breaker"] != [list(breaker)]
                or audit["board"] != [1, 1, 14, 14] or audit["root_height"] != height):
            raise ValueError("conditional state/audit binding changed")
        reachable, todo = set(), [expected_root]
        while todo:
            old = todo.pop()
            if old in reachable:
                continue
            reachable.add(old)
            for child, *_ in dependencies(cards[old]):
                if not 0 <= child < len(cards) or cards[child]["h"] >= cards[old]["h"]:
                    raise ValueError("invalid strict dependency height")
                todo.append(child)
        if len(reachable) != expected_count:
            raise ValueError("unexpected reachable closure")
        mapping = {}
        for old in sorted(reachable, key=lambda i: (cards[i]["h"], i)):
            card = cards[old]
            def remap(h):
                return None if h is None else (mapping[h[0]], *h[1:])
            clone = dict(card, **{"pass": remap(card["pass"]),
                                 "replies": [(w, remap(h)) for w, h in card["replies"]]})
            key = json.dumps(clone, sort_keys=True, separators=(",", ":"))
            if key not in keys:
                keys[key] = len(cards_out)
                cards_out.append(clone)
            mapping[old] = keys[key]
        # Recheck every source row through its full transformed dependency map.
        for old, new in mapping.items():
            c, d = cards[old], cards_out[new]
            assert all(c[k] == d[k] for k in ("A", "S", "p", "h"))
            assert remap(c["pass"]) == d["pass"]
            assert [(w, remap(h)) for w, h in c["replies"]] == d["replies"]
        k, dx, dy = header[3]
        a, b, c, d = cards2lean.ORIENT[k]
        def placed(point):
            x, y = point
            return a*x+b*y+dx, c*x+d*y+dy
        root = cards[expected_root]
        support = [placed(p) for p in root["S"]]
        assert [placed(p) for p in root["A"]] == [(7, 7)]
        assert breaker not in support and all(1 <= x <= 14 and 1 <= y <= 14 for x, y in support)
        roots.append(dict(source=name, source_root=expected_root, merged_root=mapping[expected_root],
            source_transform=list(header[3]), physical_zero_based_transform=[k, dx-1, dy-1],
            maker=[[7, 7]], breaker=[list(breaker)], board=[1, 1, 14, 14],
            maker_ids=[90], breaker_ids=[14*(breaker[1]-1)+breaker[0]-1],
            height=height, required=root["A"], support=root["S"], pivot=root["p"],
            placed_support=support, placed_pivot=placed(root["p"])))
        maps.append(dict(source=name, source_to_merged={str(k): v for k, v in sorted(mapping.items())}))
        source_reports.append(dict(path=name, sha256=digest, header=header,
            reachable_cards=len(reachable), audit=audit_name, audit_sha256=sha(audit_path)))
    GEN.mkdir(parents=True, exist_ok=True)
    deck = GEN / "opening-closures.cards.txt"
    deck.write_text(serialize(cards_out, roots[0]["merged_root"]))
    parsed_header, parsed_cards = cards2lean.parse(deck)
    assert parsed_cards == cards_out and parsed_header[2] == roots[0]["merged_root"]
    estimates = []
    for cap in (5000, 10000, 25000):
        chunks = cards2lean.chunks(cards_out, cap, 15)
        pieces = sum(1 if len(chunk)>1 or cards2lean.units(cards_out[chunk[0]], cards_out)<=cap
            else 2+len(cards2lean.reply_parts(cards_out[chunk[0]], cards_out, cap, 2)) for chunk in chunks)
        estimates.append(dict(units=cap, max_cards=15, max_cells=2, chunks=len(chunks), proof_modules=pieces))
    report = dict(schema="snaky-conditional-opening-closures-v1", status="extracted_for_kernel_check",
        generator_sha256=sha(Path(__file__)), parser_generator_sha256=sha(Path(cards2lean.__file__)),
        sources=source_reports, roots=roots, mappings=maps, cards=len(cards_out),
        input_closure_cards=sum(s["reachable_cards"] for s in source_reports),
        exact_duplicates_removed=sum(s["reachable_cards"] for s in source_reports)-len(cards_out),
        output_sha256=sha(deck), proof_estimates=estimates,
        scope="Two exact nonempty 14x14 opening states. Heights count further Maker claims. No empty-board result.")
    (GEN / "closure-map.json").write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    return report


def generate(report, units, max_cells):
    _, cards = cards2lean.parse(GEN / "opening-closures.cards.txt")
    header = "-- Generated by tools/maker_opening_data.py; every proof is kernel checked.\n"
    namespace = "Snaky.GenMakerOpening"
    def write(name, imports, body):
        (GEN / name).write_text(header + imports + f"\nnamespace {namespace}\n\n"
            + body + f"\n\nend {namespace}\n")
    data_modules = []
    for start in range(0, len(cards), 15):
        number = start // 15
        data_modules.append(f"{namespace}.Data{number:03}")
        body = "\n".join(f"def c{i} : Card := {cards2lean.card(cards[i])}"
                         for i in range(start, min(start+15, len(cards))))
        write(f"Data{number:03}.lean", "import Snaky.Cards\n", body)
    tree = cards2lean.balanced([(i, i+1, None) for i in range(len(cards))],
                              lambda it: f"(.leaf {it[0]} c{it[0]})")
    write("Tree.lean", "".join(f"import {m}\n" for m in data_modules),
          f"set_option maxRecDepth 100000\n\ndef tree : CTree := {tree}\ndef getK : Nat → Option Card := tree.get")
    proof_modules = []
    for i, card in enumerate(cards):
        lines = ["open Snaky.MakerOpeningCheck", "set_option maxHeartbeats 0",
                 "set_option maxRecDepth 4096", ""]
        if card["pass"] is None:
            lines.append(f"theorem c{i}_ok : cardOK getK c{i} = true := by decide +kernel")
        else:
            hints = list(dict.fromkeys(dependencies(card)))
            for n, hn in enumerate(hints):
                child = hn[0]
                rendered = cards2lean.hint(hn)
                xf = cards2lean.xf(*hn[1:])
                parts = []
                for start in range(0, len(cards[child]["S"]), max_cells):
                    part = start // max_cells
                    ps = cards[child]["S"][start:start+max_cells]
                    pn = f"c{i}_h{n}_s{part}"
                    parts.append(pn)
                    lines.append(f"def {pn} : List Pt := [{', '.join(map(cards2lean.pt, ps))}]")
                    lines.append(f"theorem {pn}_ok : {pn}.all (fun s => c{i}.S.contains (({xf} : Xf).app s)) = true := by decide +kernel")
                combined = " ++ ".join(parts)
                names = ", ".join(p+"_ok" for p in parts)
                lines.append(f"theorem c{i}_h{n} : hintOK getK c{i}.h (c{i}.p :: c{i}.A) (fun s => c{i}.S.contains s) {rendered} = true :=\n"
                    f"  hint_of_parts (d := c{child}) (by rfl) (by decide +kernel) (by decide +kernel)\n"
                    f"    (by decide +kernel)\n"
                    f"    (all_of_parts (ys := {combined}) _ (by rfl)\n"
                    f"      (by simp only [List.all_append, {names}, Bool.and_self]))")
            outside = hints.index(card["pass"])
            lines.append(f"theorem c{i}_head : cardHead getK c{i} = true := by\n"
                f"  change (decide (1 ≤ c{i}.h) && c{i}.S.contains c{i}.p) &&\n"
                f"    hintOK getK c{i}.h (c{i}.p :: c{i}.A) (fun s => c{i}.S.contains s) {cards2lean.hint(card['pass'])} = true\n"
                f"  rw [c{i}_h{outside}]\n  decide +kernel")
            owned = set(card["A"]) | {card["p"]}
            first_reply = {}
            for w, hn in card["replies"]:
                first_reply.setdefault(w, hn)
            for n, w in enumerate(card["S"]):
                goal = f"theorem c{i}_r{n} : replyOK getK c{i} {cards2lean.pt(w)} = true := "
                if w in owned:
                    lines.append(goal + "by decide +kernel")
                else:
                    hn = first_reply[w]
                    lines.append(goal + f"\n  reply_of_hint (d := c{hn[0]}) (by rfl) (by rfl) c{i}_h{hints.index(hn)} (by decide +kernel)")
            support = "[" + ", ".join(map(cards2lean.pt, card["S"])) + "]"
            replies = ", ".join(f"c{i}_r{n}" for n in range(len(card["S"])))
            lines.append(f"theorem c{i}_all : c{i}.S.all (replyOK getK c{i}) = true :=\n"
                f"  all_of_parts (ys := {support}) _ (by rfl)\n"
                f"    (by simp only [List.all_cons, List.all_nil, {replies}, Bool.and_self])")
            lines.append(f"theorem c{i}_ok : cardOK getK c{i} = true :=\n"
                f"  cardOK_of_split c{i}.S c{i}_head (self_cover _) c{i}_all")
        name = f"Card{i:04}"
        proof_modules.append(namespace + "." + name)
        write(name+".lean", f"import {namespace}.Tree\nimport Snaky.MakerOpeningCheck\n", "\n".join(lines))
    # balanced() emits tree constructors; the identical split shape is reused
    # with the already proved Boolean conjunction constructor.
    def glue(lo, hi):
        if hi-lo == 1:
            return f"(CTree.all_leaf c{lo}_ok)"
        mid = (lo+hi)//2
        return f"(CTree.all_node {glue(lo, mid)} {glue(mid, hi)})"
    write("All.lean", "".join(f"import {m}\n" for m in proof_modules),
          f"set_option maxRecDepth 100000\n\ntheorem tree_ok : tree.all (cardOK getK) = true := {glue(0, len(cards))}")
    modules = [*data_modules, namespace+".Tree", *proof_modules, namespace+".All"]
    (GEN / "modules.json").write_text(json.dumps(modules, indent=2)+"\n")
    report["generation"] = dict(data_cards_per_module=15, proof_cards_per_module=1,
        reused_hint_support_inclusions=True, support_cells_per_kernel_decision=max_cells,
        empty_root_obligation_emitted=False, modules=len(modules))
    (GEN / "closure-map.json").write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    for root, label in zip(report["roots"], ("66", "710"), strict=True):
        i = root["merged_root"]
        xf = cards2lean.xf(*root["physical_zero_based_transform"])
        blocker = root["breaker_ids"][0]
        lines = [f"def opening{label} : Card := GenMakerOpening.c{i}",
                 f"def frame{label} : Xf := {xf}", ""]
        parts = []
        for start in range(0, len(cards[i]["S"]), 6):
            n = start // 6
            name = f"support{label}_{n}"
            parts.append(name)
            literal = ", ".join(map(cards2lean.pt, cards[i]["S"][start:start+6]))
            lines.append(f"private def {name} : List Pt := [{literal}]")
            lines.append(f"private theorem {name}_ok : {name}.all (fun s => decide\n"
                f"  (onBoard 14 14 (frame{label}.app s) ∧ idx 14 (frame{label}.app s) ∉ [{blocker}])) = true := by decide +kernel")
        combined, names = " ++ ".join(parts), ", ".join(p+"_ok" for p in parts)
        lines.append(f"theorem opening{label}_placed : Placed 14 14 opening{label} frame{label} [90] [{blocker}] := by\n"
            f"  refine ⟨by decide +kernel, ?_, by decide +kernel⟩\n"
            f"  have hs : opening{label}.S.all (fun s => decide\n"
            f"      (onBoard 14 14 (frame{label}.app s) ∧ idx 14 (frame{label}.app s) ∉ [{blocker}])) = true :=\n"
            f"    MakerOpeningCheck.all_of_parts (ys := {combined}) _ (by rfl)\n"
            f"      (by simp only [List.all_append, {names}, Bool.and_self])\n"
            f"  intro s hmem\n  exact of_decide_eq_true ((List.all_eq_true.mp hs) s hmem)")
        (FORMAL / f"Snaky/MakerOpeningPlaced{label}.lean").write_text(header +
            "import Snaky.GenMakerOpening.Tree\nimport Snaky.MakerOpeningCheck\n\n"
            "namespace Snaky.MakerOpening\n\nset_option maxRecDepth 4096\n\n" +
            "\n".join(lines) + "\n\nend Snaky.MakerOpening\n")


def main():
    global FORMAL, GEN
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extract-only", action="store_true")
    parser.add_argument("--from-extracted", action="store_true",
                        help="regenerate from the published compact deck and closure map")
    parser.add_argument("--output-dir", type=Path,
                        help="write regenerated sources into a separate formal directory")
    parser.add_argument("--units", type=int, default=10000,
                        help="retained for the recorded conventional-generator estimate")
    parser.add_argument("--max-cells", type=int, default=6)
    args = parser.parse_args()
    if args.max_cells < 1:
        parser.error("--max-cells must be positive")
    if args.from_extracted:
        if args.extract_only:
            parser.error("--from-extracted and --extract-only are mutually exclusive")
        report = json.loads((GEN / "closure-map.json").read_text())
        digest = sha(GEN / "opening-closures.cards.txt")
        if digest != "0d540ec2646a07d0de25b42e20a2000c8fb4ed6dfff92b91289ab4537978f20b":
            raise ValueError("published opening deck changed")
        if report["output_sha256"] != digest or report["cards"] != 1647:
            raise ValueError("closure map does not bind the published deck")
        expected = [(1598, [0, -1, -1], [90], [75], 19),
                    (1646, [5, 1, 12], [90], [132], 15)]
        actual = [(r["merged_root"], r["physical_zero_based_transform"],
                   r["maker_ids"], r["breaker_ids"], r["height"])
                  for r in report["roots"]]
        if actual != expected:
            raise ValueError("conditional opening states changed")
    else:
        report = extract()
    if args.output_dir:
        original_gen = GEN
        FORMAL = args.output_dir.resolve()
        GEN = FORMAL / "Snaky/GenMakerOpening"
        GEN.mkdir(parents=True, exist_ok=True)
        if GEN != original_gen:
            for name in ("opening-closures.cards.txt", "closure-map.json"):
                shutil.copy2(original_gen / name, GEN / name)
    if not args.extract_only:
        generate(report, args.units, args.max_cells)
    print(json.dumps({k: report[k] for k in ("cards", "exact_duplicates_removed", "output_sha256", "proof_estimates")}, indent=2))


if __name__ == "__main__":
    main()
