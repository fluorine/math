#!/usr/bin/env python3
"""Independent finite admission of the proposed full physical L_cap controller.

Only pinned literal geometry/pairing checking code is imported. No constructor,
search, solver, catalog or encoder is used. Exterior interleavings are covered
by a checked disjoint-pair/product condition, not by sampled play histories.
"""
from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import time

BASE = Path(__file__).resolve().parents[1]
PINS = {
    'browser/02-twentieth-final-section.txt':
        'd8d730b249e68792a5733c27027b792ff8bccdf30d8d8aa9f2bb0b9eb3f48ecb',
    'verification/browser_sixteenth_maker02.json':
        'b4a6cddcf00d819dfc43675f7f8e83b0c328ebc9159ecd57a164194d72e6e083',
    'maker/earlier-pairing-row-result.pairing.json':
        '4798216f6401073a9c8830a7c65d454207268f856840d1fd5cf80732a421e8ea',
    'verification/earlier_pairing_replay.json':
        'c228eae5cc77312edba72808500acee0145660a80e83d0cf8877fec78b427fec',
    'verification/browser_eighteenth_maker.py':
        '747b4b9d8b0624f292507fb1a9a49c089838795a67f40a078e313cdf519a8f32',
    'verification/descendant_pairing_replay.py':
        '42b67d5d9c6cac3334c563f6a762e1ff6b8fcaaedaf9e5c0828db1e28f1110eb',
}
CELLS = dict(a=(11,8), b=(13,8), c=(13,9), d=(12,9), e=(14,7),
             g=(14,8), h=(14,9), i=(14,10), f=(12,11), l=(12,12),
             u=(13,11), v=(13,12), w=(13,13))
K_NAMES = 'abcdeghi'
K = frozenset(CELLS[name] for name in K_NAMES)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def pair(names):
    return frozenset(CELLS[name] for name in names)


def policies():
    rows = {
        'a': ('d', ['be','ch','gi']),
        'b': ('d', ['ae','ch','gi']),
        'c': ('d', ['ab','hi']),
        'e': ('d', ['ab','ch','gi']),
        'g': ('d', ['ab','hi']),
        'h': ('d', ['ae','bc','gi']),
        'i': ('d', ['ae','bc','gh']),
        'd': ('b', ['ac','gi']),
        'outside_unmatched': ('d', ['be','ch','gi']),
    }
    return {name:dict(reply=CELLS[reply],pairs=tuple(pair(p) for p in pairs))
            for name,(reply,pairs) in rows.items()}


def admission(maker, breaker, original, exterior, domain, rows, geometry, literal, guard):
    need(len(maker) == len(breaker) == 34 and not maker & breaker
         and maker | breaker <= literal.V, 'wrong full initial colors')
    need(domain == K and domain <= literal.V-maker-breaker, 'reserved domain is changed or not pristine')
    need(len(original) == 54 and len(exterior) == 51, 'wrong original/exterior pair count')
    literal.pairing(original, literal.V-maker-breaker)
    literal.pairing(exterior, literal.V-maker-breaker-domain)
    core = frozenset(pair(p) for p in ('be','ch','gi'))
    need(core <= set(original) and frozenset(exterior) == frozenset(original)-core,
         'exterior matching is not exactly the three-pair deletion')
    traces_c = (pair('fuv'), pair('flvw'))
    need(all(any(p <= trace for p in exterior) for trace in traces_c), 'admission condition C fails')
    live = tuple(edge for edge in geometry if not edge & breaker)
    need(len(geometry) == 1040 and len(live) == 263
         and not any(edge <= maker for edge in geometry), 'wrong full geometry or initial win')
    inventory, uncovered = [], []
    for edge in sorted(live, key=lambda e: sorted(e)):
        guard()
        witnesses = [j for j,p in enumerate(exterior) if p <= edge]
        trace = edge & domain
        if not witnesses:
            need(len(trace) >= 2, 'target without exterior pair can win on first local entry')
            uncovered.append((edge, trace))
        inventory.append(dict(target=sorted(edge), exterior_pair_indices=witnesses,
                              reserved_trace=sorted(trace)))
    need(set(rows) == set(K_NAMES) | {'outside_unmatched'}, 'missing or extra local policy row')
    for name,row in rows.items():
        guard()
        entered = frozenset() if name == 'outside_unmatched' else frozenset({CELLS[name]})
        reply, pairs = row['reply'], row['pairs']
        need(reply in domain-entered, 'stale or exterior local response')
        literal.pairing(pairs, domain-entered-{reply})
        for _,trace in uncovered:
            need(not trace <= entered, 'Maker wins before local response')
            need(reply in trace or any(p <= trace for p in pairs), 'local response leaves a full target unprotected')
    need(rows['outside_unmatched']['reply'] == CELLS['d']
         and frozenset(rows['outside_unmatched']['pairs']) == core,
         'unmatched exterior entry does not commit the original matching')
    return live, uncovered, inventory


def pair_invariant():
    """Exhaust all two-endpoint colorings; 0 free, 1 Maker, 2 Breaker."""
    safe = {state for state in product(range(3), repeat=2)
            if 1 not in state or 2 in state}
    maker_steps = filler_steps = 0
    for state in safe:
        for endpoint in (0,1):
            if state[endpoint] != 0:
                continue
            moved = list(state); moved[endpoint] = 1
            need(moved != [1,1], 'Maker can finish a protected pair before response')
            if moved[1-endpoint] == 0:
                moved[1-endpoint] = 2
            need(tuple(moved) in safe, 'mate response breaks the pair invariant')
            maker_steps += 1
            filled = list(state); filled[endpoint] = 2
            need(tuple(filled) in safe, 'extra Breaker filler breaks the pair invariant')
            filler_steps += 1
    return dict(colorings=len(safe),maker_steps=maker_steps,filler_steps=filler_steps,
                final_claim_checked_before_response=True)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def local_replay(name, row, traces, guard):
    """Overapproximate all exterior moves and arbitrary committed fillers.

    Zero denotes an outside move. It may stutter forever in this quotient;
    revisiting a state adds no local winning possibility. Real play is finite.
    All local Maker wins are tested before any reply, including exhaustion.
    """
    positions = {CELLS[name]:1 << j for j,name in enumerate(K_NAMES)}
    masks = tuple(sum(positions[q] for q in trace) for trace in traces)
    pair_masks = tuple(sum(positions[q] for q in p) for p in row['pairs'])
    maker = 0 if name == 'outside_unmatched' else positions[CELLS[name]]
    breaker = positions[row['reply']]
    need(not any(t & maker == t for t in masks), 'initial local Maker win')
    pending, seen = [(maker,breaker)], set()
    moves = fillers = final_local = 0
    while pending:
        guard()
        m,b = pending.pop()
        if (m,b) in seen:
            continue
        seen.add((m,b))
        need(len(seen) <= 10000, 'unexpected local replay size')
        free = 255 & ~(m|b)
        for move in (0,*bits(free)):
            next_m = m | move
            need(not any(t & next_m == t for t in masks), 'local Maker wins before committed response')
            after = 255 & ~(next_m|b)
            if move and not after:
                final_local += 1
            mate = next((p ^ move for p in pair_masks if move and p & move and (p ^ move) & after), 0)
            responses = (mate,) if mate else (0,*bits(after))
            for response in responses:
                successor = (next_m,b|response)
                if successor not in seen:
                    pending.append(successor)
                if not mate:
                    fillers += 1
            moves += 1
    return dict(states=len(seen),maker_entries_including_outside=moves,
                arbitrary_filler_transitions=fillers,final_local_maker_claim_checks=final_local)


def audit(guard):
    for name, expected in PINS.items():
        guard()
        need(sha(BASE/name) == expected, 'changed pinned input: '+name)
    literal = load('k8_independent_geometry', BASE/'verification/browser_eighteenth_maker.py')
    replay = load('k8_independent_pairing', BASE/'verification/descendant_pairing_replay.py')
    geometry = literal.literal_geometry(guard)
    maker = literal.CROSS_M - {(13,8),(13,9),(11,8)}
    breaker = literal.CROSS_B - {(14,7),(14,9),(12,9)}
    declared = json.loads((BASE/'verification/browser_sixteenth_maker02.json').read_text())['residuals']['L_cap']
    literal.bind_state(declared,maker,breaker,34)
    certificate = json.loads((BASE/'maker/earlier-pairing-row-result.pairing.json').read_text())
    original_check = replay.check_certificate(certificate,maker|{CELLS['a']},breaker|{CELLS['d']},
                                              geometry,literal,guard)
    need(len(original_check['pairs']) == 54 and original_check['live_target_count'] == 257,
         'wrong accepted L_row matching')
    original = tuple(replay.physical(p) for p in certificate['pairs'])
    core = frozenset(pair(p) for p in ('be','ch','gi'))
    exterior = tuple(p for p in original if p not in core)
    rows = policies()
    live, uncovered, inventory = admission(maker,breaker,original,exterior,K,rows,geometry,literal,guard)
    need(pair('fl') in exterior and pair('uv') in exterior, 'advertised sufficient C pairs absent')
    d_targets = [edge for edge in live if CELLS['d'] in edge]
    need(len(d_targets) == 6, 'six-target classification through d differs')
    traces = frozenset(trace for _,trace in uncovered)
    local = {name:local_replay(name,row,traces,guard) for name,row in rows.items()}
    exterior_invariant = pair_invariant()
    controls = []
    def reject(label, function):
        guard()
        try:
            function()
        except ValueError:
            controls.append(label)
            return
        raise ValueError('negative control accepted: '+label)
    def altered(**changes):
        values = dict(maker=maker,breaker=breaker,original=original,exterior=exterior,
                      domain=K,rows=rows,geometry=geometry,literal=literal,guard=guard)
        values.update(changes)
        return admission(**values)
    reject('lost_old_maker',lambda:altered(maker=maker-{min(maker)}))
    reject('lost_old_breaker',lambda:altered(breaker=breaker-{min(breaker)}))
    reject('reserved_cell_not_fresh',lambda:altered(maker=(maker-{min(maker)})|{CELLS['a']}))
    reject('overlapping_exterior_pair',lambda:altered(exterior=exterior[:-1]+(exterior[0],)))
    unused = literal.V-maker-breaker-K-frozenset().union(*original)
    need(unused, 'no unused exterior cell for the C-corruption control')
    replacement = frozenset({CELLS['f'],min(unused)})
    without_c = tuple(replacement if p == pair('fl') else p for p in original)
    exterior_without_c = tuple(replacement if p == pair('fl') else p for p in exterior)
    reject('lost_C_pair',lambda:altered(original=without_c,exterior=exterior_without_c))
    bad = copy.deepcopy(rows); del bad['d']
    reject('missing_first_entry_row',lambda:altered(rows=bad))
    bad = copy.deepcopy(rows); bad['a']['reply'] = CELLS['a']
    reject('stale_local_response',lambda:altered(rows=bad))
    bad = copy.deepcopy(rows); bad['a']['pairs'] = (pair('ab'),)
    reject('pair_contains_entry',lambda:altered(rows=bad))
    bad = copy.deepcopy(rows); bad['a']['pairs'] = ()
    reject('uncovered_target_after_response',lambda:altered(rows=bad))
    bad = copy.deepcopy(rows); bad['d']['reply'] = CELLS['h']
    reject('wrong_d_response',lambda:altered(rows=bad))
    bad = copy.deepcopy(rows); bad['outside_unmatched']['reply'] = CELLS['a']
    reject('outside_commitment_uses_wrong_reply',lambda:altered(rows=bad))
    reject('immediate_local_win_before_reply',lambda:local_replay('d',rows['d'],[pair('d')],guard))
    guard()
    encoded_rows = {name:dict(maker_entry=None if name == 'outside_unmatched' else CELLS[name],
        breaker_reply=row['reply'],replacement_pairs=[sorted(p) for p in row['pairs']],
        local_replay=local[name]) for name,row in rows.items()}
    return dict(schema='snaky-independent-lcap-k8-controller-v1',
        status='independently_verified_full_conditional_breaker_controller',complete_defense=True,
        original_state=declared,geometry_count=len(geometry),live_target_count=len(live),
        reserved_domain=sorted(K),original_pair_count=len(original),exterior_pairs=[sorted(p) for p in exterior],
        admission_condition_C_pairs=[sorted(pair('uv')),sorted(pair('fl'))],
        policy=encoded_rows,full_live_target_inventory=inventory,
        targets_without_exterior_pair=[dict(target=sorted(edge),trace=sorted(trace)) for edge,trace in uncovered],
        distinct_reserved_traces=[sorted(t) for t in sorted(traces,key=lambda t:sorted(t))],
        d_target_inventory=[sorted(edge) for edge in sorted(d_targets,key=lambda e:sorted(e))],
        exterior_pair_invariant=exterior_invariant,negative_controls=controls,
        response_rule='While K is pristine, answer a Maker claim outside K by its free Q mate and keep waiting. If no free mate is required, claim d and commit to Q plus the original three core pairs. On first K entry use its literal row and commit. After commitment take a free mate in the selected matching if needed; otherwise take any fresh filler. Previously Breaker-hit pairs may be discarded.',
        proof='Every initially live full target contains a Q pair or one of the checked traces in K. During waiting, K is pristine and each Maker-touched Q pair has a Breaker endpoint. Thus exterior claims cannot win, and each first K claim is safe before its response because every unprotected trace has at least two K cells. The displayed fresh response either hits each trace or leaves a free internal pair in it. Q is disjoint from K, so all prior exterior histories preserve the same coverage: touched Q pairs are already Breaker-blocked and untouched pairs are free. The unmatched exterior row is checked by the same condition. After commitment a legal Maker claim cannot complete any protecting pair; a Maker-owned mate would require the proposed cell to be Breaker-owned. A fresh mate therefore exists whenever one is needed. Any other fresh filler preserves the invariant; if no reply remains, Maker has still not completed a pair. Old blocked targets remain blocked. The finite local replay also permits arbitrary outside moves and fillers as an overapproximation.',
        scope='Complete ordinary physical Breaker defense at the exact Maker-to-move L_cap 34+34 state, with all old stones retained. No parent loss, empty-board 14x14 defense, board-size lower bound, or novelty claim follows.')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args(argv)
    if args.output.exists():
        parser.error('fresh output required')
    start,cpu = time.monotonic(),time.process_time()
    def guard():
        if time.process_time()-cpu >= 8 or time.monotonic()-start >= 25:
            raise TimeoutError('finite controller CPU/wall cap')
    try:
        result = audit(guard)
    except TimeoutError as error:
        result = dict(status='incomplete',complete_defense=False,reason=str(error))
    except (ValueError,KeyError) as error:
        result = dict(status='rejected',complete_defense=False,reason=str(error))
    result.update(source_sha256=sha(Path(__file__)),input_sha256=PINS,
        utc=datetime.now(timezone.utc).isoformat(),cpu_seconds=time.process_time()-cpu,
        elapsed_seconds=time.monotonic()-start,limits=dict(cpu_seconds=8,wall_seconds=25))
    with args.output.open('x') as stream:
        json.dump(result,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps({key:result.get(key) for key in ('status','complete_defense','live_target_count',
        'cpu_seconds','elapsed_seconds')},sort_keys=True))
    return int(not result['complete_defense'])


if __name__ == '__main__':
    raise SystemExit(main())
