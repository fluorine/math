#!/usr/bin/env python3
"""Independent full physical four-claim Maker strategy at the exact S12.

No constructor, search, projection, or matching solver is imported. The
previously checked S13 pairing pins the full physical history; deleting only
its final M32/B1 gives S12. Every legal physical Breaker reply is enumerated.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import struct
import sys
import time

BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BASE / 'breaker'))
from check_pairing import check, winning_sets


ACCEPTED = 'verification/browser-eighteenth-full-pairing05-01.json'
CERTIFICATE = 'verification/browser-eighteenth-full-pairing05-01.pairing.json'
PINS = {
    ACCEPTED: 'c8679a8fab93fdbbbd749981d7ec89fbcf43441b617e55fa94cd9ae554e5cbd0',
    CERTIFICATE: '315547489b51a54b1ec79ede7a47fa6c8fca9d025f043d80531c6b37237c2130',
    'verification/browser_eighteenth_full_pairing05.py':
        '94b7252d34d43048b1877606921d8774a914de9fae1a94e7bec3212cb9a1a164',
    'verification/browser-seventeenth-composition05-01.json':
        '2263c092bb013af533132927cffb76d76e536f2dfb0b38c10475276d4588d4a8',
    'verification/browser_seventeenth_composition05.py':
        'eb3d8b705f0e52cf55f04020a10d0097ac7150c7819520b7246ac82f316937b8',
    'verification/check_repaired13_physical_matching.py':
        '05bf0a9a7006fab493befd1bb1e5f1f38a3e749df0551b0e9bdb9bd63547987b',
    'browser/05-eighteenth-final.txt':
        '58a32fc2329febfec52fe37755913b4352f7f8f70969e275399ca0f8a9a266b0',
    'breaker/check_pairing.py':
        'f24d5a389197f5010afc88036e0b849c3f31caadb60c142f29c1b3c684191056',
    'browser/05-nineteenth-final.txt':
        '94d3bf62b1556e3c8fb5c1e79ae339068ad22bcffeca660ae66a13b03fb4a180',
    'browser/05-nineteenth-final-section.txt':
        'a5689231df0ce2fa892c9c821eae3ae09afc2008201b4a84a33649ecba9f34b8',
}
GEOMETRY_SHA = '06b3a966ff46af6b36a59e88f562e985f752690959a4a1f27dd17a657ca282ed'
BOARD = frozenset(range(100))
FULL = (1 << 100) - 1
STRIP = frozenset(10*y+x for y in range(7) for x in range(3))
M0 = frozenset((37, 44, 45, 46, 47, 57, 67, 75, 84))
B0 = frozenset((34, 36, 38, 55, 56, 58, 74, 77, 94))
PREFIX = ((11, 14), (21, 43), (31, 24), (32, 1))
# Rows are (left, centre, right), literal left Snaky, literal right Snaky.
FOUR_FORKS = (
    ((0, 10, 20), (0, 10, 11, 21, 31, 41), (10, 20, 21, 31, 41, 51)),
    ((2, 12, 22), (2, 11, 12, 21, 31, 41), (12, 21, 22, 31, 41, 51)),
    ((40, 50, 60), (11, 21, 31, 40, 41, 50), (21, 31, 41, 50, 51, 60)),
    ((42, 52, 62), (11, 21, 31, 41, 42, 52), (21, 31, 41, 51, 52, 62)),
)
TWO_FORKS = (
    ((30, 40, 50), (1, 11, 21, 30, 31, 40), (11, 21, 31, 40, 41, 50)),
    ((32, 42, 52), (1, 11, 21, 31, 32, 42), (11, 21, 31, 41, 42, 52)),
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def mask(cells):
    return sum(1 << cell for cell in cells)


def cells(bits):
    while bits:
        bit = bits & -bits
        yield bit.bit_length() - 1
        bits ^= bit


def claim(cell, maker, breaker):
    need(type(cell) is int and 0 <= cell < 100 and not (maker | breaker) & (1 << cell),
         'prescribed claim is not a fresh physical cell')
    return maker | (1 << cell)


def reply_domain(replies, maker, breaker):
    need(tuple(replies) == tuple(cells(FULL & ~(maker | breaker))),
         'reply list omits or duplicates a legal full-board reply')


def terminal(maker, breaker, target_mask, wins):
    need(not maker & breaker and target_mask & maker == target_mask
         and not target_mask & breaker and bool(wins(maker)),
         'terminal claim does not complete the declared full physical Snaky')


def source_state(accepted, certificate, edges):
    original = dict(maker=sorted(M0), breaker=sorted(B0), turn='Maker')
    need(accepted['status'] == 'verified_full_conditional_repaired13_pairing'
         and accepted['checker_sha256'] == PINS['verification/browser_eighteenth_full_pairing05.py']
         and accepted['original_state'] == original
         and accepted['actual_prefix'] == [dict(maker=u, breaker=v) for u, v in PREFIX]
         and accepted['certificate'] == certificate
         and accepted['full_conditional_game_leaf'] is True
         and accepted['empty10_result'] is False and accepted['upstream_root_proved'] is False,
         'accepted complete physical history differs')
    maker, breaker = set(M0), set(B0)
    need(not any(e <= maker for e in edges), 'source already contains a Maker Snaky')
    for u, v in PREFIX:
        need(u in BOARD-maker-breaker and v in BOARD-maker-breaker-{u},
             'actual prefix contains an occupied claim')
        maker.add(u)
        need(not any(e <= maker for e in edges), 'actual prefix continued after a physical win')
        breaker.add(v)
    successor = dict(maker=sorted(maker), breaker=sorted(breaker), turn='Maker')
    need(accepted['physical_state'] == successor
         and certificate['schema'] == 'snaky-static-pairing-v1' and certificate['size'] == 10
         and certificate['maker'] == successor['maker'] and certificate['breaker'] == successor['breaker'],
         'accepted S13 colors differ')
    old = check(10, certificate['pairs'], maker, breaker)
    need(old['live_placements'] == 127 and old['pairs'] == 31, 'accepted S13 pairing differs')
    maker.remove(32); breaker.remove(1)
    need(len(maker) == len(breaker) == 12 and len(BOARD-maker-breaker) == 76
         and not maker & breaker and maker & STRIP == {11, 21, 31}
         and not breaker & STRIP, 'full S12 ownership or initially fresh strip differs')
    need(sum(not e & breaker for e in edges) == 132, 'S12 live target count differs')
    return dict(original_state=original, actual_prefix=accepted['actual_prefix'][:-1],
        accepted_successor=successor, removed_final_claims=dict(maker=[32], breaker=[1]),
        state=dict(maker=sorted(maker), breaker=sorted(breaker), turn='Maker'),
        free_cells=sorted(BOARD-maker-breaker), live_target_count=132,
        strip=sorted(STRIP), strip_maker=[11, 21, 31], strip_breaker=[])


def table_check(table, spine, initial_maker, initial_breaker, edges):
    used = set()
    for triple, left_target, right_target in table:
        need(len(triple) == len(set(triple)) == 3 and not set(triple) & used,
             'fork triples are not pairwise disjoint')
        need(set(triple) <= STRIP-initial_maker-initial_breaker-spine,
             'fork triple is not initially free and outside its Maker spine')
        used.update(triple)
        left, centre, right = triple
        for target, remainder in ((left_target, {left, centre}), (right_target, {centre, right})):
            target = frozenset(target)
            need(target in edges and target <= STRIP and target-spine == remainder,
                 'fork witness is not the declared full literal Snaky with its exact two-cell remainder')


def controls(accepted, certificate, edges, wins):
    outcomes = []
    def reject(name, operation):
        try:
            operation()
        except ValueError as error:
            outcomes.append(dict(name=name, rejected=True, reason=str(error)))
        else:
            raise ValueError('negative control accepted: ' + name)
    changed = deepcopy(accepted)
    changed['physical_state']['breaker'].remove(1)
    changed['physical_state']['breaker'].append(33)
    reject('nominal_B33_replaces_actual_B1', lambda: source_state(changed, certificate, edges))
    maker, breaker = M0 | {11, 21, 31}, B0 | {14, 43, 24}
    spine = frozenset((11, 21, 31, 41, 51))
    overlap = (FOUR_FORKS[0], FOUR_FORKS[0], *FOUR_FORKS[2:])
    reject('overlapping_fork_triples', lambda: table_check(overlap, spine, maker, breaker, edges))
    wrong = ((FOUR_FORKS[0][0], (0, 10, 11, 21, 31, 99), FOUR_FORKS[0][2]), *FOUR_FORKS[1:])
    reject('nonliteral_six_cell_witness', lambda: table_check(wrong, spine, maker, breaker, edges))
    reject('second_M51_after_first_B51', lambda: claim(51, mask(maker | {41}), mask(breaker | {51})))
    before = maker | {41, 51, 10}
    reject('blocked_left_endpoint', lambda: claim(0, mask(before), mask(breaker | {0})))
    target = mask(FOUR_FORKS[0][1])
    reject('projection_omits_owned_body_requirement',
           lambda: terminal(mask((before | {0})-{21}), mask(breaker), target, wins))
    first_maker = mask(maker | {41}); first_breaker = mask(breaker)
    replies = tuple(cells(FULL & ~(first_maker | first_breaker)))
    reject('omitted_legal_exterior_B_reply', lambda: reply_domain(replies[:-1], first_maker, first_breaker))
    terminal(mask(before | {0}), mask(breaker), target, wins)
    outcomes.append(dict(name='full_target_checked_on_final_Maker_claim_before_any_B_reply', passed=True))
    return outcomes


def audit(tick):
    for name, expected in PINS.items():
        tick(); need(sha((BASE/name).read_bytes()) == expected, 'changed input: ' + name)
    edges = tuple(sorted(winning_sets(10), key=lambda e: tuple(sorted(e))))
    geometry_raw = (json.dumps([sorted(e) for e in edges], separators=(',', ':'))+'\n').encode()
    need(len(edges) == 432 and sha(geometry_raw) == GEOMETRY_SHA, 'independent literal geometry differs')
    accepted = json.loads((BASE/ACCEPTED).read_text())
    certificate = json.loads((BASE/CERTIFICATE).read_text())
    binding = source_state(accepted, certificate, edges)
    maker_set, breaker_set = map(frozenset, (binding['state']['maker'], binding['state']['breaker']))
    maker0, breaker0 = mask(maker_set), mask(breaker_set)
    edge_masks = tuple(map(mask, edges))
    @lru_cache(maxsize=None)
    def wins(maker):
        return tuple(i for i, target in enumerate(edge_masks) if target & maker == target)
    table_check(FOUR_FORKS, frozenset((11, 21, 31, 41, 51)), maker_set, breaker_set, edges)
    table_check(TWO_FORKS, frozenset((1, 11, 21, 31, 41)), maker_set, breaker_set, edges)
    need(all(51 not in triple for triple, _, _ in TWO_FORKS), 'first B51 touches a special-case fork')
    witnesses = sorted({tuple(target) for table in (FOUR_FORKS, TWO_FORKS)
                        for _, left, right in table for target in (left, right)})
    need(len(witnesses) == 10, 'the two fork tables do not have exactly ten distinct witnesses')
    compiled = tuple(tuple((triple, mask(triple), edges.index(frozenset(left)),
                            edges.index(frozenset(right))) for triple, left, right in table)
                     for table in (FOUR_FORKS, TWO_FORKS))
    rows = []; terminals = 0; second_reply_count = 0
    fork_uses = Counter(); minimum_untouched = {1: 2, 51: 4}
    digest = hashlib.sha256()
    first_maker = claim(41, maker0, breaker0)
    need(not wins(first_maker), 'unexpected earlier physical win after M41; stop before any reply')
    first_replies = tuple(cells(FULL & ~(first_maker | breaker0)))
    reply_domain(first_replies, first_maker, breaker0)
    need(len(first_replies) == 75, 'first full-board reply count differs')
    for first in first_replies:
        tick(); b1 = breaker0 | (1 << first)
        second = 1 if first == 51 else 51
        m2 = claim(second, first_maker, b1)
        need(not wins(m2), 'unexpected earlier physical win after second claim; stop before any reply')
        table = compiled[first == 51]
        second_replies = tuple(cells(FULL & ~(m2 | b1)))
        reply_domain(second_replies, m2, b1)
        need(len(second_replies) == 73, 'second full-board reply count differs')
        for second_reply in second_replies:
            tick(); second_reply_count += 1; b2 = b1 | (1 << second_reply)
            untouched = [i for i, (_, triple_mask, _, _) in enumerate(table)
                         if not triple_mask & (m2 | b2)]
            need(len(untouched) >= (1 if first == 51 else 2), 'too few untouched physical forks')
            minimum_untouched[second] = min(minimum_untouched[second], len(untouched))
            chosen = untouched[0]; (left, centre, right), _, left_index, right_index = table[chosen]
            m3 = claim(centre, m2, b2)
            need(not wins(m3), 'unexpected earlier physical win after centre; stop before any reply')
            third_replies = tuple(cells(FULL & ~(m3 | b2)))
            reply_domain(third_replies, m3, b2)
            need(len(third_replies) == 71, 'third full-board reply count differs')
            use = Counter()
            for third in third_replies:
                b3 = b2 | (1 << third)
                endpoint, target_index = (right, right_index) if third == left else (left, left_index)
                final_maker = claim(endpoint, m3, b3)
                terminal(final_maker, b3, edge_masks[target_index], wins)
                need(maker0 & final_maker == maker0 and breaker0 & b3 == breaker0
                     and final_maker.bit_count() == 16 and b3.bit_count() == 15
                     and (FULL & ~(final_maker | b3)).bit_count() == 69,
                     'old ownership, turn counts, or terminal free-cell count changed')
                digest.update(struct.pack('>BBBBBBH', first, second_reply, third,
                                          second, centre, endpoint, target_index))
                terminals += 1; use[endpoint] += 1
            fork_uses[(second, chosen)] += 1
            rows.append(dict(first_breaker=first, second_maker=second, second_breaker=second_reply,
                untouched_fork_indices=untouched, chosen_fork_index=chosen, third_maker=centre,
                third_reply_count=len(third_replies), left_terminal_count=use[left],
                right_terminal_count=use[right], left_target_index=left_index,
                right_target_index=right_index))
    need(second_reply_count == 75*73 and terminals == 75*73*71,
         'complete physical reply tree is not covered')
    checked_controls = controls(accepted, certificate, edges, wins)
    tick()
    return dict(status='verified_conditional_S12_physical_Maker_win_in_four', binding=binding,
        literal_target_count=432, literal_target_sha256=GEOMETRY_SHA,
        full_witnesses=[dict(target=list(w), literal_target_index=edges.index(frozenset(w))) for w in witnesses],
        fork_tables=dict(second_M51=FOUR_FORKS, second_M1=TWO_FORKS),
        first_maker=41, first_reply_count=len(first_replies), second_reply_count=second_reply_count,
        third_reply_count=terminals, terminal_count=terminals, max_additional_Maker_claims=4,
        immediate_wins_on_claim4=terminals, earlier_wins=0, terminal_free_cells=69,
        minimum_untouched_forks={str(k): v for k, v in sorted(minimum_untouched.items())},
        chosen_fork_counts=[dict(second_maker=m, fork_index=i, count=n)
                            for (m, i), n in sorted(fork_uses.items())],
        second_reply_rows=rows, terminal_stream_sha256=digest.hexdigest(),
        terminal_stream_format='Concatenate big-endian >BBBBBBH rows: first B, second B, third B, second M, third M, fourth M, target index. Full-board B replies are in increasing order at each node.',
        cached_Maker_masks_checked=wins.cache_info().currsize, focused_controls=checked_controls,
        projected_away_cells=[], prescribed_B_restrictions=[], physical_conditional_result=True,
        upstream_S9_result=None, empty10_result=None,
        conclusion='Maker wins in four further claims at the exact S12 Maker turn, against all physical Breaker replies. The accepted S13 leaf remains valid; different earlier Breaker choices and the empty10 game are unresolved.')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(argv)
    need(not args.output.exists(), 'fresh output required; preserve previous attempts')
    cpu, wall = time.process_time(), time.monotonic()
    def tick():
        if time.process_time()-cpu >= 8 or time.monotonic()-wall >= 25:
            raise TimeoutError('finite S12 physical strategy audit budget')
    report = dict(schema='snaky-browser-nineteenth-physical12-independent-v1', status='UNKNOWN',
        checker_sha256=sha(Path(__file__).read_bytes()), input_sha256=PINS,
        limits=dict(internal_cpu_seconds=8, internal_wall_seconds=25),
        scope='Exact physical12M/12B Maker turn only, no projection and no empty10 or upstream S9 conclusion.')
    try:
        report.update(audit(tick))
    except TimeoutError as error:
        report.update(status='UNKNOWN', reason=str(error))
    except (ValueError, KeyError, TypeError, IndexError, OSError) as error:
        report.update(status='rejected', reason=f'{type(error).__name__}: {error}')
    report.update(created_utc=datetime.now(timezone.utc).isoformat(),
                  process_cpu_seconds=time.process_time()-cpu,
                  elapsed_seconds=time.monotonic()-wall)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as stream:
        stream.write(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: report.get(k) for k in ('status', 'reason', 'terminal_count',
        'max_additional_Maker_claims', 'process_cpu_seconds', 'elapsed_seconds')}))
    return int(report['status'] != 'verified_conditional_S12_physical_Maker_win_in_four')


if __name__ == '__main__':
    raise SystemExit(main())
