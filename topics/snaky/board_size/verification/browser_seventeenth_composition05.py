#!/usr/bin/env python3
"""Independent finite audit of the seventeenth browser05 composition claim.

Read the accepted K19 certificate as data; import no controller or constructor.
Enumerate literal geometry and every physical reply in the displayed attacks.
This does not search for, or certify, a complete empty-board strategy.
"""
import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

BASE = Path(__file__).resolve().parents[1]
ACCEPTED = 'verification/controller19-joint-port11-01.json'
PINS = {
    ACCEPTED: '206fffad00e2f1e08a4e2628293e887bc76ef5c7658122e08b0f3c9661d51a1d',
    'verification/controller19_joint_port11.py':
        'baa784bf6da8c4848dd87e65f62fcac88464fe92ad133d1c8e41df28e45c052a',
    'browser/05-seventeenth-final.txt':
        '9f67fbfb7313c5846984e4877edd0fc2884c5a5c32f968e97647225249eb9730',
}
CERTIFICATE_SHA = 'ab36d0949f43692d74a9ced67fda055f90888cbe25b273b8d1e0d99fdd714912'
V = frozenset(range(100))
M0 = frozenset((37, 44, 45, 46, 47, 57, 67, 75, 84))
B0 = frozenset((34, 36, 38, 55, 56, 58, 74, 77, 94))
K19 = frozenset((11, 12, 13, 14, 21, 22, 23, 24, 25, 31, 32, 33, 42, 43, 52, 53, 54, 63, 73))
OUTSIDE = frozenset((30, 41))
U = frozenset((1, 41, 42, 52, 62))
E1 = frozenset((1, 11, 21, 31, 32, 42))
E41 = frozenset((11, 21, 31, 41, 42, 52))
E62 = frozenset((21, 31, 32, 42, 52, 62))
GAMMA = frozenset((13, 21, 22, 23))
GAMMA_PLUS = GAMMA | {14}
E_GAMMA = frozenset((13, 14, 20, 21, 22, 23))
SELECTED = (frozenset((12, 22, 31)), frozenset((23, 32, 33)), GAMMA)
REPAIR = tuple(map(frozenset, ((53, 54), (42, 52), (12, 22), (23, 33))))
BOUNDARY = frozenset(map(frozenset, (
    (1, 11, 21, 31, 32, 42), (10, 11, 12, 13, 23, 24),
    (10, 11, 21, 22, 23, 24), (11, 12, 13, 14, 20, 21),
    (11, 21, 31, 41, 42, 52), (14, 15, 21, 22, 23, 24))))


def need(ok, why):
    if not ok:
        raise ValueError(why)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def ordered(sets):
    return sorted((sorted(s) for s in sets))


def geometry(tick):
    """All eight literal orientations, with every in-board translation."""
    result = set()
    for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        for side in (-1, 1):
            fx, fy = -side * dy, side * dx
            for x in range(10):
                for y in range(10):
                    tick()
                    pts = [(x + j*dx, y + j*dy) for j in range(4)]
                    pts += [(x + j*dx + fx, y + j*dy + fy) for j in (3, 4)]
                    if all(0 <= a < 10 and 0 <= b < 10 for a, b in pts):
                        result.add(frozenset(10*b+a for a, b in pts))
    need(len(result) == 432, 'literal target universe differs')
    return frozenset(result)


def physical_state(m, b):
    need(M0 <= m and B0 <= b and m <= V and b <= V and not m & b,
         'old physical ownership lost, off-board, or conflicting')


def maker_move(m, b, move, edges, terminal=False):
    physical_state(m, b)
    need(move in V - m - b, 'Maker claim is not physically fresh')
    need(not any(e <= m for e in edges), 'play continued after an earlier physical win')
    result = m | {move}
    if not terminal:
        need(not any(e <= result for e in edges), 'nonterminal Maker claim already wins physically')
    return result


def finish(m, b, move, target, edges, physical):
    result = maker_move(m, b, move, edges, terminal=True)
    need(target <= result and not target & b, 'claimed terminal witness is incomplete or blocked')
    if physical:
        need(target in edges, 'selected target was substituted for a physical Snaky')
    return dict(maker=move, witness=sorted(target), physical_win=any(e <= result for e in edges))


def dispatch_prefix(cert, edges):
    """Replay actual rows/pair mates; no outside entry or filler is available."""
    defs = cert['definitions']
    active = [dict(component='K19_joint_port11'), dict(pair=sorted(OUTSIDE))]
    m, b = M0, B0
    trace = []
    cut = None

    def domain(item):
        return frozenset(item['pair'] if 'pair' in item else defs[item['component']]['domain'])

    for u, expected in ((11, 14), (21, 43), (31, 24), (32, 33)):
        selected = [i for i, item in enumerate(active) if u in domain(item)]
        need(len(selected) == 1, 'prefix entry lacks a unique active dispatcher')
        index = selected[0]
        item = active[index]
        parent = domain(item)
        before = dict(maker=sorted(m), breaker=sorted(b), active=deepcopy(active))
        m = maker_move(m, b, u, edges)
        if u == 32:
            cut = (m, b)
        if 'pair' in item:
            reply = next(iter(parent - {u}))
            children = []
            row = dict(maker=u, reply=reply, children=[])
        else:
            rows = [r for r in defs[item['component']]['rows'] if r['maker'] == u]
            need(len(rows) == 1, 'actual certificate row is missing or duplicated')
            row = rows[0]
            reply, children = row['reply'], deepcopy(row['children'])
        need(reply == expected and reply in V - m - b, 'prescribed prefix response differs or is not fresh')
        b = b | {reply}
        active.pop(index)
        occupied = set().union(*(domain(c) for c in active)) if active else set()
        for child in children:
            d = domain(child)
            need(d <= parent - {u, reply} and not d & (m | b | occupied),
                 'child borrows occupied cells or overlaps an active domain')
            occupied.update(d)
            active.append(child)
        physical_state(m, b)
        need(any(c.get('pair') == sorted(OUTSIDE) for c in active), 'outside30-41 pair was consumed')
        trace.append(dict(before=before, maker=u, reply=reply, dispatcher=item,
                          certificate_row=row, after=dict(maker=sorted(m), breaker=sorted(b), active=deepcopy(active))))
    need(cut == (M0 | {11, 21, 31, 32}, B0 | {14, 43, 24}), 'fourth-response cut changed')
    need(any(c.get('pair') == [42, 52] for c in active), 'nominal42 response is not52')
    return trace, cut, (m, b)


def physical_attack(m, b, edges, tick):
    """M42; B!=1/M1; B1/M52; then complete41 or62."""
    need(all(e in edges and not e & b for e in (E1, E41, E62)), 'attack target not literal/live')
    need((E1-m, E41-m, E62-m) == ({1, 42}, {41, 42, 52}, {42, 52, 62}), 'physical residuals differ')
    m1 = maker_move(m, b, 42, edges)
    first = []
    terminal = Counter()
    for r in sorted(V - m1 - b):
        tick()
        b1 = b | {r}
        if r != 1:
            row = dict(reply=r, terminal=finish(m1, b1, 1, E1, edges, True))
            terminal['E1'] += 1
        else:
            m2 = maker_move(m1, b1, 52, edges)
            second = []
            for s in sorted(V - m2 - b1):
                tick()
                move, witness, label = (62, E62, 'E62') if s == 41 else (41, E41, 'E41')
                second.append(dict(reply=s, terminal=finish(m2, b1 | {s}, move, witness, edges, True)))
                terminal[label] += 1
            need(len(second) == 71, 'final physical reply count differs')
            row = dict(reply=r, maker=52, replies=second)
        first.append(row)
    need(len(first) == 73 and sum(terminal.values()) == 143, 'physical reply enumeration incomplete')
    return dict(first_maker=42, replies=first, terminal_witness_counts=dict(terminal), terminal_count=143)


def selected_attack(m, b, edges, tick):
    """After any reply in U, unchanged three-guard contract loses."""
    need(all(not t & b for t in SELECTED), 'selected obstruction already blocked')
    need(tuple(t-m for t in SELECTED) == ({12, 22}, {23, 33}, {13, 22, 23}), 'selected residuals differ')
    m1 = maker_move(m, b, 22, edges)
    need(not any(t <= m1 for t in SELECTED), 'selected win should not precede the forced response')
    first = []
    counts = Counter()
    for r in sorted(V - m1 - b):
        tick()
        b1 = b | {r}
        if r != 12:
            terminal = finish(m1, b1, 12, SELECTED[0], edges, False)
            first.append(dict(reply=r, terminal=terminal))
            counts['selected_terminals'] += 1
            counts['also_physical_terminals'] += terminal['physical_win']
        else:
            m2 = maker_move(m1, b1, 23, edges)
            need(not any(t <= m2 for t in SELECTED), 'selected fork was already terminal')
            second = []
            for s in sorted(V - m2 - b1):
                tick()
                move, target = (13, GAMMA) if s == 33 else (33, SELECTED[1])
                terminal = finish(m2, b1 | {s}, move, target, edges, False)
                second.append(dict(reply=s, terminal=terminal))
                counts['selected_terminals'] += 1
                counts['also_physical_terminals'] += terminal['physical_win']
            need(len(second) == 71, 'selected final reply count differs')
            first.append(dict(reply=r, maker=23, replies=second))
    need(len(first) == 73 and counts['selected_terminals'] == 143, 'selected all-reply tree incomplete')
    return dict(first_maker=22, replies=first, counts=dict(counts), scope='Selected contract only; physical flags reported separately.')


def check_pairs(pairs, m, b):
    used = set()
    for p in pairs:
        need(len(p) == 2 and p <= V and not p & (m | b | used), 'pair is not fresh or disjoint')
        used.update(p)


def check_leaf(targets, pairs, m, b):
    check_pairs(pairs, m, b)
    need(all(t & b or any(p <= t-m for p in pairs) for t in targets), 'live target misses every fresh pair')


def audit(old, tick):
    edges = geometry(tick)
    cert = old['certificate']
    need(old['status'] == 'verified_complete_joint_K19_E11_controller'
         and old['checker_sha256'] == PINS['verification/controller19_joint_port11.py']
         and canonical(cert) == CERTIFICATE_SHA == old['certificate_sha256'], 'accepted certificate identity differs')
    need(old['physical_state'] == dict(maker=sorted(M0), breaker=sorted(B0), turn='Maker')
         and old['reserved_domain'] == sorted(K19) and old['outside_pair'] == sorted(OUTSIDE)
         and cert['roots'] == ['K19_joint_port11'], 'physical root/reservation differs')
    targets = frozenset(map(frozenset, cert['definitions']['K19_joint_port11']['targets']))
    need(len(targets) == 26 and set(SELECTED) <= targets and GAMMA_PLUS not in targets,
         'selected guard contract differs')
    live = frozenset(e for e in edges if not e & B0)
    cover = lambda ts: frozenset(e for e in live if any(t <= e-M0 for t in ts))
    assigned = cover(targets | {OUTSIDE})
    need(len(live) == 194 and len(assigned) == 58
         and ordered(assigned) == old['physical_coverage']['covered_targets'], 'accepted physical assignment differs')
    boundary = frozenset(e for e in live-assigned if len(e-M0-K19) <= 1)
    need(boundary == BOUNDARY and ordered(boundary) == ordered(frozenset(r['target']) for r in
         old['physical_coverage']['unprotected_zero_or_singleton_exterior']), 'six physical boundary targets differ')

    prefix, (mcut, bcut), reached = dispatch_prefix(cert, edges)
    replies = V-mcut-bcut
    need(len(replies) == 75 and U <= replies, 'cut freshness/count differs')
    bad = []
    for reply in sorted(replies-U):
        tick()
        bad.append(dict(fourth_reply=reply, maker=sorted(mcut), breaker=sorted(bcut | {reply}),
                        attack=physical_attack(mcut, bcut | {reply}, edges, tick)))
    need(len(bad) == 70 and reached == (mcut, bcut | {33}), 'nominal prefix not among bad replies')
    nominal = next(r for r in bad if r['fourth_reply'] == 33)
    selected = [dict(fourth_reply=r, maker=sorted(mcut), breaker=sorted(bcut | {r}),
                     attack=selected_attack(mcut, bcut | {r}, edges, tick)) for r in sorted(U)]

    gamma_bindings = frozenset(e for e in edges if GAMMA <= e)
    need(gamma_bindings == {E_GAMMA} == frozenset(e for e in edges if GAMMA_PLUS <= e)
         and E_GAMMA in live and 14 in bcut, 'Gamma unique/full physical binding differs')
    weakened = (targets-{GAMMA}) | {GAMMA_PLUS}
    need(cover(weakened | {OUTSIDE}) == assigned, 'guard weakening changed initial physical coverage')
    repaired_b = bcut | {1}
    need(1 in replies and 1 not in K19 | OUTSIDE and 33 not in repaired_b | mcut,
         'repair is not the claimed fresh outside response, or invents B33')
    check_leaf(weakened, REPAIR, mcut, repaired_b)
    check_pairs(REPAIR+(OUTSIDE,), mcut, repaired_b)
    residuals = {t-mcut for t in weakened if not t & repaired_b}
    minimal = {t for t in residuals if not any(s < t for s in residuals)}
    need(minimal == set(REPAIR), 'remaining selected antichain is not exactly the four repair pairs')
    required = assigned | BOUNDARY
    need(len(required) == 64, 'old58 plus six previously unprotected targets differ')
    check_leaf(required | {E62}, REPAIR+(OUTSIDE,), mcut, repaired_b)
    dispositions = []
    for e in sorted(required | {E62}, key=lambda e: sorted(e)):
        tick()
        dispositions.append(dict(target=sorted(e), breaker_hits=sorted(e & repaired_b),
                                 contained_pairs=ordered(p for p in REPAIR+(OUTSIDE,) if p <= e-mcut)))

    controls = []
    def reject(name, action):
        try:
            action()
        except ValueError:
            controls.append(name)
        else:
            raise ValueError('negative control accepted: '+name)
    reject('discard_old_Maker44', lambda: physical_state(mcut-{44}, repaired_b))
    reject('retain_unweakened_Gamma', lambda: check_leaf(targets, REPAIR, mcut, repaired_b))
    reject('retire_Gamma_without_actual_B14', lambda: check_leaf(weakened, REPAIR, mcut, repaired_b-{14}))
    wrong_pairs = REPAIR[:-1]+(frozenset((13, 23)),)
    reject('retain_old13_23_instead_of23_33', lambda: check_leaf(weakened, wrong_pairs, mcut, repaired_b))
    reject('omit_actual_B1', lambda: check_leaf({E1}, REPAIR+(OUTSIDE,), mcut, repaired_b-{1}))
    reject('invent_virtual_B33', lambda: check_pairs(REPAIR+(OUTSIDE,), mcut, repaired_b | {33}))
    reject('selected_Gamma_is_not_a_full_Snaky', lambda: need(GAMMA in edges, 'not literal'))
    safe = frozenset(e for e in live if e & repaired_b or any(p <= e-mcut for p in REPAIR+(OUTSIDE,)))
    return dict(
        status='verified_conditional_K19_dispatcher_loss_and_guarded_repair', literal_target_count=len(edges),
        initial_physical_state=dict(maker=sorted(M0), breaker=sorted(B0), turn='Maker'),
        initial_live_target_count=len(live), accepted_certificate_sha256=CERTIFICATE_SHA,
        prescribed_prefix=prefix, outside_pair=sorted(OUTSIDE), fourth_response_cut=dict(
            maker=sorted(mcut), breaker=sorted(bcut), turn='Breaker', legal_replies=sorted(replies)),
        physical_targets=ordered((E1, E41, E62)), bad_fourth_replies=bad,
        nominal_reached_state=dict(maker=sorted(reached[0]), breaker=sorted(reached[1]), turn='Maker'),
        nominal_attack_terminal_count=nominal['attack']['terminal_count'],
        physical_bad_reply_count=70, physical_attack_terminal_count=sum(r['attack']['terminal_count'] for r in bad),
        necessary_physical_reply_set=sorted(U), selected_obstructions=selected,
        selected_terminal_count=sum(r['attack']['counts']['selected_terminals'] for r in selected),
        gamma=dict(original=sorted(GAMMA), weakened=sorted(GAMMA_PLUS), full_physical_bindings=ordered(gamma_bindings),
                   actual_retiring_breaker=14, initial_coverage_unchanged=True),
        repair=dict(maker=sorted(mcut), breaker=sorted(repaired_b), turn='Maker', actual_reply=1,
                    fictitious_reply33=False, fresh_pairs=ordered(REPAIR), outside_pair_unchanged=sorted(OUTSIDE),
                    selected_residuals=ordered(residuals), minimal_selected_residuals=ordered(minimal),
                    original_assigned_count=58, additional_boundary_targets=ordered(BOUNDARY),
                    verified_assignment_count=len(required), physical_target_dispositions=dispositions,
                    safe_among_initial194=len(safe), unassigned_initial_targets=ordered(live-safe)),
        negative_controls=controls,
        scope=('Every fixed dispatcher executing these fresh K19 rows/pair mates reaches the recorded physical '
               'Maker-winning state, even with arbitrary later Breaker play. The five other replies lose only '
               'the unchanged selected contract in this proof. The B1 repair preserves the recorded assigned '
               'subfamily at its exact physical cut; it is not a complete194-target strategy or an ordinary '
               'exclusive-domain K19 row. Outside interleavings require new guard checks.'),
        unrestricted_initial9M9B_result=None, empty10_result=None, lean_proof=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    need(not args.output.exists(), 'preserve prior output')
    cpu, wall = time.process_time(), time.monotonic()
    def tick():
        if time.process_time()-cpu >= 4 or time.monotonic()-wall >= 25:
            raise TimeoutError('finite composition audit budget')
    report = dict(checker_sha256=sha(Path(__file__)), input_sha256=PINS,
                  created_utc=datetime.now(timezone.utc).isoformat())
    try:
        for path, digest in PINS.items():
            tick()
            need(sha(BASE/path) == digest, 'pinned input changed: '+path)
        old = json.loads((BASE/ACCEPTED).read_text())
        report.update(audit(old, tick))
    except (ValueError, KeyError, TypeError, OSError, TimeoutError) as exc:
        report.update(status='UNKNOWN' if isinstance(exc, TimeoutError) else 'rejected', error=str(exc))
    report.update(cpu_seconds=time.process_time()-cpu, wall_seconds=time.monotonic()-wall)
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({k:report.get(k) for k in ('status', 'error', 'physical_bad_reply_count',
        'physical_attack_terminal_count', 'selected_terminal_count', 'cpu_seconds', 'wall_seconds')}))
    return int(report['status'] != 'verified_conditional_K19_dispatcher_loss_and_guarded_repair')


if __name__ == '__main__':
    raise SystemExit(main())
