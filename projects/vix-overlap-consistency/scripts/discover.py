"""Numerical discovery only. Never a proof or an unrestricted-model LP.

All 64 schedules of the frozen architecture are included. Prefix-count rows
imply the standing SPX strips, but require a separate identification bridge
before an infeasibility result is a vanilla-quote theorem.
"""
import itertools
import json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

A = np.array(list(itertools.product(range(2), repeat=6)), dtype=int)
N = np.cumsum(A, axis=1)
W = np.array([A[:, i:i+3].sum(axis=1) for i in (1, 2, 3)])
F = np.array([np.ones(64)] + [(N[:, k] == j).astype(int)
              for k in range(6) for j in range(k+1)])
G = np.array([(W[i] == j).astype(int) for i in range(3) for j in (0, 3)])
p0 = np.ones(64)/64
f = F @ p0
pairs = ((0,1), (0,2), (1,2))
rows, rhs = [], []
for block in range(3):
    for row, value in zip(F, f):
        x = np.zeros(192); x[64*block:64*(block+1)] = row
        rows.append(x); rhs.append(value)
for i in range(3):
    b1, b2 = [b for b in range(3) if i in pairs[b]]
    for row in G[2*i:2*i+2]:
        x = np.zeros(192)
        x[64*b1:64*(b1+1)] = row
        x[64*b2:64*(b2+1)] = -row
        rows.append(x); rhs.append(0)
Q = np.array(rows)
outdir = Path(__file__).resolve().parent.parent / 'certificates'
rng = np.random.default_rng(4017)
best = 0
for it in range(2000):
    d = rng.integers(-2,3,6)
    objective = np.zeros(192)
    for i in range(3):
        block = next(b for b in range(3) if i in pairs[b])
        objective[64*block:64*(block+1)] += d[2*i:2*i+2] @ G[2*i:2*i+2]
    q = linprog(-objective, A_eq=Q, b_eq=rhs, bounds=(0,None),method='highs')
    g = linprog(-(d @ G), A_eq=F, b_eq=f, bounds=(0,None),method='highs')
    if not q.success or not g.success:
        raise RuntimeError((q.message,g.message))
    gap = g.fun-q.fun
    if gap > best+1e-8:
        best = gap
        data = dict(iteration=it, direction=d.tolist(), gap=gap,
                    schedules=A.tolist(), prefix_target=f.tolist(),
                    pair_witnesses=q.x.reshape(3,64).tolist(),
                    global_upper=-g.fun, pair_objective=-q.fun,
                    spx_dual=(-g.eqlin.marginals).tolist())
        (outdir/'discovery.json').write_text(json.dumps(data,indent=2)+'\n')
        print('candidate',it,'direction',d,'gap',gap,flush=True)
        if gap >= 0.03:
            break
print('finished best gap',best,flush=True)
