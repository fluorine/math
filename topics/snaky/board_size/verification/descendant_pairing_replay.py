#!/usr/bin/env python3
"""Independently bind and replay both complete physical descendant pairings.

The only imported checking code is the pinned literal body/hook geometry audit.
No encoder, constructor, catalog, solver or root pairing checker is imported.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import time

BASE = Path(__file__).resolve().parents[1]
PINS = {
    'verification/browser_eighteenth_maker.py':
        '747b4b9d8b0624f292507fb1a9a49c089838795a67f40a078e313cdf519a8f32',
    'verification/browser_seventeenth_maker02.json':
        'deb1d35610621f7eba9c16e6a608d166bd6dc3a9bd17794b7d6fee04a577e0ca',
    'maker/descendant-pairing-cross-result.json':
        '386c480fa29a849eead40e3e83ac424333d16f32b2b9d9f26489a410c173b4f4',
    'maker/descendant-pairing-cross-result.pairing.json':
        '8cc738cbfbc94a369f1f3ee4d28419ebac18291213ad62440ba7bf9263db61ad',
    'maker/descendant-pairing-blocked-result.json':
        '205fe54917c538a2653402295276afded35b2772b4f95b35caa25479dac97385',
    'maker/descendant-pairing-blocked-result.pairing.json':
        '0a0180057ec11295a93ecaebb02f65d76ead4fe799ddd6e5603c45854c9ef0c9',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def physical(raw):
    need(isinstance(raw, list) and all(type(q) is int and 0 <= q < 196 for q in raw),
         'nonliteral or out-of-board cell IDs')
    need(len(set(raw)) == len(raw), 'repeated cell ID')
    return frozenset((q % 14 + 1, q // 14 + 1) for q in raw)


def check_certificate(certificate, maker, breaker, geometry, literal, guard):
    need(certificate['schema'] == 'snaky-static-pairing-v1' and certificate['size'] == 14,
         'wrong pairing schema/board')
    need(physical(certificate['maker']) == maker and physical(certificate['breaker']) == breaker,
         'pairing changes original physical colors')
    need(not maker & breaker and maker | breaker <= literal.V, 'invalid original colors')
    need(not any(edge <= maker for edge in geometry), 'Maker initially owns a winning target')
    pairs = tuple(physical(row) for row in certificate['pairs'])
    literal.pairing(pairs, literal.V-maker-breaker)
    live = frozenset(edge for edge in geometry if not edge & breaker)
    rows = []
    for edge in sorted(live, key=lambda edge: sorted(edge)):
        guard()
        indices = [i+1 for i, pair in enumerate(pairs) if pair <= edge]
        need(indices, 'full live physical target is uncovered')
        rows.append(dict(target=sorted(edge), pair_indices=indices))
    return dict(maker=sorted(maker), breaker=sorted(breaker), board=[1,1,14,14],
                turn='Maker', pairs=[sorted(pair) for pair in pairs],
                live_target_count=len(live), full_target_coverage=rows)


def audit(guard):
    for name, expected in PINS.items():
        guard()
        need(sha(BASE/name) == expected, 'changed pinned input: ' + name)
    spec = importlib.util.spec_from_file_location('independent_eighteenth_geometry',
        BASE/'verification/browser_eighteenth_maker.py')
    literal = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(literal)
    geometry = literal.literal_geometry(guard)
    accepted = json.loads((BASE/'verification/browser_seventeenth_maker02.json').read_text())
    results, controls = {}, []
    for name, maker, breaker, count, expected_live in (
            ('cross', literal.CROSS_M, literal.CROSS_B, 37, 246),
            ('blocked', literal.BLOCKED_M, literal.BLOCKED_B, 36, 248)):
        label = 'T_' + name
        literal.bind_state(accepted['residuals'][label], maker, breaker, count)
        report_path = BASE/f'maker/descendant-pairing-{name}-result.json'
        certificate_path = BASE/f'maker/descendant-pairing-{name}-result.pairing.json'
        report, certificate = (json.loads(path.read_text()) for path in (report_path, certificate_path))
        need(report['status'] == 'checked_full_conditional_pairing_candidate', 'root report status')
        need(Path(report['certificate']).resolve() == certificate_path.resolve()
             and report['certificate_sha256'] == sha(certificate_path), 'certificate binding')
        need(report['binding']['name'] == label, 'result state label')
        literal.bind_state(report['binding']['original_state'], maker, breaker, count)
        checked = check_certificate(certificate, maker, breaker, geometry, literal, guard)
        need(len(checked['pairs']) == 53 and checked['live_target_count'] == expected_live,
             'claimed pair or live-target count differs')
        results[label] = checked
        def reject(suffix, changed):
            guard()
            try:
                check_certificate(changed, maker, breaker, geometry, literal, guard)
            except ValueError:
                controls.append(label + ':' + suffix)
                return
            raise ValueError('negative control accepted: ' + label + ':' + suffix)
        bad = dict(certificate, maker=certificate['maker'][:-1])
        reject('dropped_old_maker', bad)
        bad = dict(certificate, breaker=certificate['breaker'][:-1])
        reject('dropped_old_breaker', bad)
        bad = dict(certificate, pairs=[*certificate['pairs'], certificate['pairs'][0]])
        reject('overlapping_pair', bad)
        bad = dict(certificate, pairs=[[certificate['maker'][0],certificate['pairs'][0][1]],
                                      *certificate['pairs'][1:]])
        reject('owned_pair_endpoint', bad)
        target = literal.cells(checked['full_target_coverage'][0]['target'])
        bad = dict(certificate, pairs=[pair for pair in certificate['pairs'] if not physical(pair) <= target])
        reject('uncovered_full_target', bad)
    guard()
    return dict(status='independently_verified_full_conditional_breaker_pairings',
        geometry_count=len(geometry), states=results, negative_controls=controls,
        response_rule='After each legal Maker claim, if its paired mate is free, Breaker claims the mate. Otherwise Breaker claims any remaining fresh cell, for example the lexicographically least. Every filler remains permanently Breaker-owned.',
        proof='Initially every pair has two free cells. At every later Maker turn, any pair already touched by Maker has a Breaker endpoint. Thus the next fresh Maker claim cannot complete a pair, including on a final legal claim: a Maker-owned mate would imply the proposed cell is already Breaker-owned. If a newly touched pair still has a free mate, that mate supplies a legal Breaker response even near exhaustion. If the mate is already Breaker-owned or Maker played outside all pairs, any available fresh filler preserves the invariant. If no reply remains, Maker has still not completed a pair. Every initially live full Snaky contains a displayed pair; targets already hit by old Breaker stones remain blocked. Therefore Maker never wins in either exact state.',
        scope='Complete conditional physical Breaker defenses at these exact Maker-to-move T_cross37+37 and T_blocked36+36 states only. No empty14 defense, ancestor loss, or global board-size lower bound follows.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cpu-seconds', type=float, default=4)
    parser.add_argument('--seconds', type=float, default=20)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if any(not math.isfinite(t) or t <= 0 for t in (args.cpu_seconds,args.seconds)):
        parser.error('limits must be finite and positive')
    if args.output.exists():
        parser.error('fresh output required')
    start, cpu = time.monotonic(), time.process_time()
    def guard():
        if time.monotonic()-start >= args.seconds or time.process_time()-cpu >= args.cpu_seconds:
            raise TimeoutError('finite replay limit')
    try:
        result = audit(guard)
    except TimeoutError as error:
        result = dict(status='incomplete', reason=str(error))
    except (ValueError,KeyError) as error:
        result = dict(status='rejected', reason=str(error))
    result.update(schema='snaky-independent-descendant-pairing-replay-v1',
        source_sha256=sha(Path(__file__)), input_sha256=PINS,
        utc=datetime.now(timezone.utc).isoformat(), cpu_seconds=time.process_time()-cpu,
        elapsed_seconds=time.monotonic()-start)
    with args.output.open('x') as stream:
        json.dump(result,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps({key:result[key] for key in ('status','cpu_seconds','elapsed_seconds')}))
    return 0 if result['status'] == 'independently_verified_full_conditional_breaker_pairings' else 1


if __name__ == '__main__':
    raise SystemExit(main())
