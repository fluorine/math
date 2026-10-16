#!/usr/bin/env python3
"""Check two literal pairing obstructions at the saved physical descendants.

This finite audit uses only full six-cell Snakies and retained physical colors.
It imports no constructor, search, catalog or solver code. Neither pairing is
claimed to be a complete physical Breaker strategy.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import time


BASE = Path(__file__).resolve().parents[1]
PINS = {
    'browser/01-eighteenth-final-section.txt':
        'a0293a8664ab21261d4534a55c4f23e4072b1df973743b6c3eba728480f308da',
    'browser/02-eighteenth-final-section.txt':
        '65ddcd1b3f4d217e976af3d822ae032700d34912b887e48536783dafeb11f382',
    'verification/browser_seventeenth_maker02.json':
        'deb1d35610621f7eba9c16e6a608d166bd6dc3a9bd17794b7d6fee04a577e0ca',
    'verification/browser_seventeenth_maker02.py':
        'd19f142d05794dbf29bb4e820c3c40d224e106fa63300c96ad2c9b9a257fe33d',
}
V = frozenset((x, y) for x in range(1, 15) for y in range(1, 15))


def cells(rows):
    return frozenset(map(tuple, rows))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(edges):
    return sorted(sorted(edge) for edge in edges)


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def literal_geometry(guard):
    # A four-cell horizontal body has a two-cell hook on either side of
    # either endpoint, overlapping the endpoint's column and extending one
    # column. Transposition supplies the vertical bodies: all eight D4 forms.
    result = {}
    for vertical in (False, True):
        point = (lambda t, f: (f, t)) if vertical else (lambda t, f: (t, f))
        for fixed in range(1, 15):
            for start in range(1, 12):
                guard()
                body = frozenset(point(t, fixed) for t in range(start, start + 4))
                for side in (-1, 1):
                    for tail_start in (start - 1, start + 3):
                        hook = frozenset(point(t, fixed + side)
                                         for t in (tail_start, tail_start + 1))
                        edge = body | hook
                        if edge <= V:
                            need(len(edge) == 6, 'degenerate geometry')
                            need(edge not in result or result[edge] == (body, hook),
                                 'nonunique body decomposition')
                            result[edge] = (body, hook)
    need(len(result) == 1040, 'incomplete literal geometry')
    return result


BLOCKED_M = cells([
    (4,10),(5,5),(5,7),(5,8),(5,9),(5,10),(6,5),(6,6),(6,8),
    (7,4),(7,5),(7,6),(7,7),(7,8),(8,4),(8,6),(8,8),(8,10),(8,11),
    (9,8),(9,11),(10,4),(10,6),(10,7),(10,8),(10,9),(10,10),(10,11),
    (11,5),(11,10),(12,8),(12,9),(12,10),(13,6),(13,7),(13,8)])
BLOCKED_B = cells([
    (4,5),(4,7),(4,8),(4,9),(4,11),(5,6),(5,11),(6,4),(6,7),(6,9),
    (6,10),(7,3),(7,9),(7,11),(8,3),(8,5),(8,7),(8,9),(9,4),(9,6),
    (9,7),(9,9),(9,10),(9,12),(10,5),(11,6),(11,7),(11,9),(11,11),
    (11,12),(12,2),(12,7),(12,11),(13,5),(13,9),(13,10)])
CROSS_M = cells([
    (4,10),(5,5),(5,7),(5,8),(5,9),(5,10),(6,5),(6,6),(6,8),
    (7,4),(7,5),(7,6),(7,7),(7,8),(8,4),(8,6),(8,8),(8,10),(8,11),
    (9,8),(9,11),(10,4),(10,6),(10,7),(10,8),(10,9),(10,10),(10,11),
    (11,5),(11,8),(11,10),(12,8),(12,10),(13,6),(13,7),(13,8),(13,9)])
CROSS_B = cells([
    (4,5),(4,7),(4,8),(4,9),(4,11),(5,6),(5,11),(6,4),(6,7),(6,9),
    (6,10),(7,3),(7,9),(7,11),(8,3),(8,5),(8,7),(8,9),(9,4),(9,6),
    (9,7),(9,9),(9,10),(9,12),(10,5),(11,6),(11,7),(11,9),(11,11),
    (11,12),(12,2),(12,7),(12,9),(13,5),(13,10),(14,7),(14,9)])

BLOCKED_PAIRS = tuple(cells(p) for p in [
    [(4,4),(5,4)], [(5,2),(5,3)], [(11,3),(12,3)],
    [(12,4),(13,4)], [(10,1),(10,2)], [(12,5),(12,6)],
    [(11,8),(14,7)], [(2,10),(3,10)], [(6,12),(7,12)],
    [(8,12),(8,13)], [(10,12),(10,13)], [(14,4),(14,5)],
    [(14,8),(14,9)]])

# Each row specifies orientation, fixed coordinate, body start, full hook,
# and the one-based index of the claimed contained pair.
BLOCKED_OLD_ROWS = (
    ('H',3,11,((10,4),(11,4)),3),
    ('H',4,10,((9,3),(10,3)),4), ('H',4,10,((13,3),(14,3)),4),
    ('H',4,2,((5,5),(6,5)),1), ('H',8,10,((13,7),(14,7)),7),
    ('H',10,2,((1,9),(2,9)),8), ('H',10,2,((1,11),(2,11)),8),
    ('H',12,5,((8,11),(9,11)),9),
    ('V',4,1,((5,4),(5,5)),1),
    ('V',5,2,((4,1),(4,2)),2), ('V',5,2,((6,1),(6,2)),2),
    ('V',5,2,((6,5),(6,6)),2),
    ('V',8,10,((7,13),(7,14)),10), ('V',8,10,((9,13),(9,14)),10),
    ('V',10,1,((11,4),(11,5)),5),
    ('V',10,10,((9,13),(9,14)),11), ('V',10,10,((11,13),(11,14)),11),
    ('V',11,2,((10,1),(10,2)),5), ('V',11,2,((12,5),(12,6)),6),
    ('V',12,3,((13,6),(13,7)),6), ('V',14,3,((13,6),(13,7)),12),
    ('V',14,4,((13,7),(13,8)),12), ('V',14,7,((13,6),(13,7)),13),
    ('V',14,8,((13,7),(13,8)),13))
BLOCKED_FRESH_ROWS = (
    ('H',3,9,((12,4),(13,4)),4), ('H',3,10,((13,4),(14,4)),3),
    ('H',3,11,((10,2),(11,2)),3), ('H',4,11,((10,3),(11,3)),4),
    ('V',12,3,((11,2),(11,3)),6), ('V',14,4,((13,3),(13,4)),12),
    ('H',12,5,((8,13),(9,13)),9), ('H',13,7,((6,12),(7,12)),9),
    ('H',13,8,((7,12),(8,12)),10))
SUPPORT_ROWS = {
    1:[4,6,10], 2:[4,5,6,10,11], 3:[4,5,9,10,11,12,13,14],
    4:[2,3,4,5,11,12,13,14], 5:[12,14], 6:[12,14], 7:[14],
    8:[11,14], 9:[1,2,14], 10:[2,3,14], 11:[1,2,14],
    12:[5,6,7,8,10], 13:[7,8,9,10,11], 14:[7,9,11]}
ESCAPES = {
    'left': (cells([(4,1),(4,2),(4,3),(4,4),(3,4),(3,5)]), (3,5)),
    'down': (cells([(7,13),(8,13),(9,13),(10,13),(6,14),(7,14)]), (6,14))}

CROSS_PAIRS = tuple(cells(p) for p in [
    [[12,5],[12,6]], [[14,5],[14,6]], [[5,2],[5,3]], [[4,4],[5,4]],
    [[2,10],[3,10]], [[8,12],[8,13]], [[10,12],[10,13]],
    [[12,11],[12,12]], [[13,11],[13,12]], [[11,4],[12,4]],
    [[13,3],[14,3]], [[10,1],[10,2]], [[6,12],[7,12]],
    [[1,13],[2,13]], [[4,13],[5,13]], [[6,13],[7,13]],
    [[9,13],[11,13]], [[12,13],[13,13]], [[1,14],[2,14]],
    [[3,14],[4,14]], [[6,14],[7,14]], [[8,14],[9,14]],
    [[10,14],[11,14]], [[12,14],[13,14]], [[4,12],[5,12]],
    [[14,10],[14,11]], [[1,5],[1,6]], [[1,8],[1,9]], [[1,11],[1,12]],
    [[2,5],[2,6]], [[2,8],[2,9]], [[2,11],[2,12]], [[3,5],[3,6]],
    [[3,8],[3,9]], [[3,11],[3,12]], [[11,1],[11,2]], [[13,1],[13,2]],
    [[2,1],[3,1]], [[6,1],[7,1]], [[8,1],[9,1]], [[6,2],[7,2]],
    [[8,2],[9,2]], [[2,3],[3,3]], [[4,3],[6,3]], [[2,4],[3,4]],
    [[2,2],[3,2]], [[4,1],[4,2]], [[1,2],[1,3]],
    [[9,3],[10,3]], [[11,3],[12,3]]])
CROSS_A = cells([(2,1),(2,2),(2,3),(2,4),(1,4),(1,5)])
CROSS_B_TARGET = cells([(2,2),(2,3),(2,4),(2,5),(1,1),(1,2)])
CROSS_TARGETS = tuple(cells(p) for p in [
    [(13,6),(13,7),(13,8),(13,9),(12,5),(12,6)],
    [(13,6),(13,7),(13,8),(13,9),(14,5),(14,6)],
    [(12,3),(12,4),(12,5),(12,6),(13,6),(13,7)],
    [(14,3),(14,4),(14,5),(14,6),(13,6),(13,7)]])


def bind_state(raw, maker, breaker, count):
    need(raw['board'] == [1,1,14,14] and raw['turn'] == 'Maker', 'state frame/turn')
    need(len(maker) == len(breaker) == count and not maker & breaker
         and maker | breaker <= V, 'literal state ownership')
    need(cells(raw['maker']) == maker and cells(raw['breaker']) == breaker,
         'full accepted state differs')
    need(len(raw['maker']) == len(raw['breaker']) == raw['stones_each'] == count,
         'state count or repeated coordinate')


def pairing(pairs, free):
    endpoints = set()
    for pair in pairs:
        need(len(pair) == 2 and pair <= free, 'pair endpoints not distinct and fresh')
        need(not endpoints & pair, 'pair endpoints overlap')
        endpoints.update(pair)
    return frozenset(endpoints)


def coverage(targets, pairs):
    rows = []
    for edge in sorted(targets, key=lambda edge: sorted(edge)):
        indices = [i+1 for i, pair in enumerate(pairs) if pair <= edge]
        need(indices, 'uncovered target')
        rows.append(dict(target=sorted(edge), pair_indices=indices))
    return rows


def inventory(rows, geometry, pairs):
    targets = set()
    for orientation, fixed, start, tail, pair_index in rows:
        body = frozenset((t, fixed) if orientation == 'H' else (fixed, t)
                         for t in range(start, start + 4))
        hook = cells(tail)
        edge = body | hook
        need(geometry.get(edge) == (body, hook), 'inventory is not a full physical Snaky')
        need(edge not in targets, 'repeated inventory row')
        need(pairs[pair_index-1] <= edge, 'incorrect inventory pair citation')
        targets.add(edge)
    return frozenset(targets)


def check_blocked(geometry, guard):
    maker, breaker = BLOCKED_M, BLOCKED_B
    live = frozenset(edge for edge in geometry if not edge & breaker)
    free = V - maker - breaker
    endpoints = pairing(BLOCKED_PAIRS, free)
    old = frozenset(edge for edge in live if edge & maker)
    expected_old = inventory(BLOCKED_OLD_ROWS, geometry, BLOCKED_PAIRS)
    need(old == expected_old and len(old) == 24, 'incomplete old-stone inventory')
    need(Counter(len(edge & maker) for edge in old) == {1:8, 2:14, 3:1, 4:1},
         'old-stone occupancy histogram')
    support = frozenset().union(*(edge-maker for edge in old))
    stated_support = frozenset((x,y) for y,xs in SUPPORT_ROWS.items() for x in xs)
    need(support == stated_support and len(support) == 53 and support <= free,
         'complete fresh support differs')
    fresh_targets = frozenset(edge for edge in geometry if edge <= support)
    need(fresh_targets == inventory(BLOCKED_FRESH_ROWS, geometry, BLOCKED_PAIRS)
         and len(fresh_targets) == 9, 'incomplete all-fresh support inventory')
    protected = frozenset(edge for edge in geometry if edge <= maker | support)
    need(protected == old | fresh_targets and len(protected) == 33,
         'incomplete support-restricted target family')
    protected_rows = coverage(protected, BLOCKED_PAIRS)
    guard()
    h5 = cells([(10,8),(11,8),(12,8),(13,8),(13,7),(14,7)])
    need({edge for edge in live if (11,8) in edge} == {h5}, '11,8 initial live targets')
    need({p for p in maker if p[0] == 12} == {(12,8),(12,9),(12,10)},
         'old column12 ownership')
    need(not any(edge & {(12,9),(12,10)} for edge in live), 'old column12 dead cells')
    need({(11,8),(14,7)} <= free, 'counterreply not fresh')
    next_m, next_b = maker | {(11,8)}, breaker | {(14,7)}
    need(not any(edge <= next_m for edge in live), 'Maker already won before counterreply')
    next_live = frozenset(edge for edge in geometry if not edge & next_b)
    dead = {(11,8),(12,8),(12,9),(12,10)}
    need(not any(edge & dead for edge in next_live), 'claimed permanent dead cell is live')
    escape_rows = {}
    for name, (edge, outside) in ESCAPES.items():
        need(edge in geometry and edge <= free, 'escape is not an all-fresh physical target')
        need(edge-support == {outside}, 'escape does not use exactly the stated outside cell')
        need(not any(pair <= edge for pair in BLOCKED_PAIRS), 'escape contains a protected pair')
        escape_rows[name] = dict(target=sorted(edge), outside_support=[outside])
    return dict(state=dict(maker=sorted(maker), breaker=sorted(breaker), board=[1,1,14,14]),
        live_targets=len(live), old_stone_targets=canonical(old), fresh_support=sorted(support),
        old_stone_occupancy_histogram=dict(sorted(Counter(len(e&maker) for e in old).items())),
        all_fresh_support_targets=canonical(fresh_targets), pairs=[sorted(p) for p in BLOCKED_PAIRS],
        endpoints=sorted(endpoints), protected_targets=protected_rows, escapes=escape_rows,
        actual_counterreply=dict(maker_claim=[11,8], breaker_claim=[14,7],
            maker=sorted(next_m), breaker=sorted(next_b), permanently_dead_owned_cells=sorted(dead)),
        scope='The physical pairing rule blocks all33 targets in original M union S53, at every horizon. A win against it must use no original Maker cell and must leave S53. This is not a full physical defense.')


def mate_reply(move, maker, breaker, pairs):
    free = V - maker - breaker
    for pair in pairs:
        if move in pair:
            mate = next(iter(pair - {move}))
            if mate in free:
                return mate
            break
    return min(free) if free else None


def fixed_policy_line(geometry, expected_replies):
    maker, breaker = set(CROSS_M), set(CROSS_B)
    moves = [(2,1),(2,2),(2,3),(2,4),(1,5),(1,4)]
    trace = []
    for i, move in enumerate(moves):
        need(move in V-maker-breaker, 'fixed-policy Maker move not fresh')
        maker.add(move)
        wins = {edge for edge in geometry if edge <= maker}
        if i == 5:
            need(CROSS_A in wins, 'sixth Maker move did not complete A')
            trace.append(dict(maker=move, breaker=None, winning_targets=canonical(wins)))
            break
        need(not wins, 'unreported earlier immediate win')
        reply = mate_reply(move, maker, breaker, CROSS_PAIRS)
        need(reply == expected_replies[i] and reply in V-maker-breaker,
             'incorrect fixed-policy reply')
        breaker.add(reply)
        need(all(not pair & maker or pair & breaker for pair in CROSS_PAIRS),
             'pair invariant failed after response')
        trace.append(dict(maker=move, breaker=reply))
    need(maker == CROSS_M | CROSS_A and breaker == CROSS_B | set(expected_replies),
         'terminal ownership differs')
    return dict(trace=trace, maker=sorted(maker), breaker=sorted(breaker),
                scope='Six-claim counterexample to this fixed policy only; not arbitrary-reply Maker strategy.')


def check_cross(geometry, guard):
    maker, breaker = CROSS_M, CROSS_B
    free = V - maker - breaker
    live = frozenset(edge for edge in geometry if not edge & breaker)
    endpoints = pairing(CROSS_PAIRS, free)
    need(len(CROSS_PAIRS) == 50 and len(endpoints) == 100, 'matching size')
    uncovered = frozenset(edge for edge in live if not any(pair <= edge for pair in CROSS_PAIRS))
    need(uncovered == {CROSS_A,CROSS_B_TARGET}, 'exact uncovered family differs')
    need(all(edge <= free for edge in uncovered), 'exceptions are not all fresh')
    need(CROSS_A-endpoints == {(1,4)} and CROSS_B_TARGET-endpoints == {(1,1)},
         'unmatched exception endpoints differ')
    old = frozenset(edge for edge in live if edge & maker)
    coverage(old, CROSS_PAIRS)
    cross = cells([(x,8) for x in range(5,14)] + [(13,6),(13,7),(13,9)])
    need(cross <= maker, 'cross not wholly old Maker-owned')
    cross_live = frozenset(edge for edge in live if edge & cross)
    need(cross_live == set(CROSS_TARGETS), 'complete cross inventory differs')
    coverage(cross_live, CROSS_PAIRS[:2])
    dead = {(x,8) for x in range(5,13)}
    need(not any(edge & dead for edge in live), 'row8 dead-cell claim fails')
    guard()
    line = fixed_policy_line(geometry, [(3,1),(3,2),(3,3),(3,4),(1,6)])
    return dict(state=dict(maker=sorted(maker), breaker=sorted(breaker), board=[1,1,14,14]),
        live_targets=len(live), pairs=[sorted(p) for p in CROSS_PAIRS],
        covered_targets=coverage(live-uncovered, CROSS_PAIRS), uncovered=canonical(uncovered),
        old_stone_targets=canonical(old), cross=sorted(cross), cross_targets=canonical(cross_live),
        permanently_dead_row8=sorted(dead),
        unmatched_exception_cells=dict(A=[[1,4]], B=[[1,1]]),
        fixed_policy_counterexample=line,
        scope='The50 fresh disjoint pairs cover every initially live target except A/B, both wholly fresh. New disjoint pairs cannot cover A/B without changing existing pairs. The given fixed policy is defeated by the checked six-claim line; no full physical defense or Maker strategy is claimed.')


def audit(guard):
    for name, expected in PINS.items():
        guard()
        need(sha(BASE/name) == expected, 'input hash mismatch: ' + name)
    accepted = json.loads((BASE/'verification/browser_seventeenth_maker02.json').read_text())
    need(accepted['status'] == 'verified_conditional_policies_two_open_residuals_and_exact_merger',
         'accepted residual report status')
    bind_state(accepted['residuals']['T_blocked'], BLOCKED_M, BLOCKED_B, 36)
    bind_state(accepted['residuals']['T_cross'], CROSS_M, CROSS_B, 37)
    geometry = literal_geometry(guard)
    need(not any(edge <= BLOCKED_M or edge <= CROSS_M for edge in geometry), 'initial Maker already won')
    blocked = check_blocked(geometry, guard)
    cross = check_cross(geometry, guard)
    controls = []
    def reject(name, action):
        guard()
        try:
            action()
        except ValueError:
            controls.append(name)
            return
        raise ValueError('negative control accepted: ' + name)
    changed = dict(accepted['residuals']['T_blocked'], breaker=sorted(BLOCKED_B-{(13,9)}))
    reject('dropped_old_breaker', lambda: bind_state(changed, BLOCKED_M, BLOCKED_B, 36))
    changed_m = dict(accepted['residuals']['T_cross'], maker=sorted(CROSS_M-{(13,9)}))
    reject('dropped_old_maker', lambda: bind_state(changed_m, CROSS_M, CROSS_B, 37))
    reject('owned_pair_endpoint', lambda: pairing((cells([(4,10),(5,4)]),)+BLOCKED_PAIRS[1:], V-BLOCKED_M-BLOCKED_B))
    reject('overlapping_pairs', lambda: pairing(BLOCKED_PAIRS+(cells([(4,4),(3,5)]),), V-BLOCKED_M-BLOCKED_B))
    protected = [cells(row['target']) for row in blocked['protected_targets']]
    reject('removed_counterreply_pair', lambda: coverage(protected, BLOCKED_PAIRS[:6]+BLOCKED_PAIRS[7:]))
    reject('omitted_live_target', lambda: need(inventory(BLOCKED_OLD_ROWS[:-1], geometry, BLOCKED_PAIRS)
           == {edge for edge in geometry if not edge&BLOCKED_B and edge&BLOCKED_M}, 'old inventory omission'))
    reject('support_cell_deleted', lambda: need(cells(blocked['fresh_support'])-{(4,1)}
           == frozenset().union(*(edge-BLOCKED_M for edge in geometry if not edge&BLOCKED_B and edge&BLOCKED_M)), 'support omission'))
    reject('escape_called_protected', lambda: coverage([ESCAPES['left'][0]], BLOCKED_PAIRS))
    reject('near_cover_called_full_defense', lambda: coverage([CROSS_A], CROSS_PAIRS))
    reject('incorrect_prescribed_mate', lambda: fixed_policy_line(geometry, [(3,2),(3,1),(3,3),(3,4),(1,6)]))
    guard()
    return dict(status='verified_restricted_pairing_obstructions_and_counterexamples',
        geometry_count=len(geometry),
        geometry_sha256=hashlib.sha256(json.dumps(canonical(geometry), separators=(',',':')).encode()).hexdigest(),
        T_blocked=blocked, T_cross=cross, negative_controls=controls,
        pairing_invariant='The pairs start free and are disjoint. After every Breaker response, each pair touched by Maker contains a Breaker endpoint. A fresh Maker move cannot complete a pair: a previously Maker-owned mate would already force this cell to be Breaker-owned. If a newly touched mate is free, claiming it preserves the invariant; otherwise any fresh filler preserves it. A newly touched pair supplies its own legal response, even near exhaustion. Thus pair-covered targets cannot win on any Maker claim, including a final claim. Extra permanent Breaker fillers only remove live targets.',
        scope='Exact T_blocked36+36 and T_cross37+37 only. Unbounded terminal-family/support obstructions, with explicit uncovered physical targets. Both residuals and empty14 remain OPEN. No new ordinary card, full Breaker win, or board-size bound.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cpu-seconds', type=float, default=4)
    parser.add_argument('--seconds', type=float, default=20)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if any(not math.isfinite(t) or t <= 0 for t in (args.cpu_seconds, args.seconds)):
        parser.error('limits must be finite and positive')
    if args.output.exists():
        parser.error('output must be a new path')
    started, cpu = time.monotonic(), time.process_time()
    def guard():
        if time.monotonic()-started >= args.seconds or time.process_time()-cpu >= args.cpu_seconds:
            raise TimeoutError('finite audit limit')
    try:
        result = audit(guard)
    except TimeoutError as error:
        result = dict(status='incomplete', reason=str(error))
    except (ValueError, KeyError) as error:
        result = dict(status='rejected', reason=str(error))
    result.update(schema='snaky-eighteenth-maker-independent-v1',
        source_sha256=sha(Path(__file__)), input_sha256=PINS,
        utc=datetime.now(timezone.utc).isoformat(), cpu_seconds=time.process_time()-cpu,
        elapsed_seconds=time.monotonic()-started,
        limits=dict(cpu_seconds=args.cpu_seconds, wall_seconds=args.seconds))
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({key:result[key] for key in ('status','cpu_seconds','elapsed_seconds')}))
    return 0 if result['status'] == 'verified_restricted_pairing_obstructions_and_counterexamples' else 1


if __name__ == '__main__':
    raise SystemExit(main())
