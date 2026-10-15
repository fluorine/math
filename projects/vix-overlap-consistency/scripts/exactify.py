"""Verify reconstructed discovery data using exact fractions (not Lean proof)."""
from fractions import Fraction as Q
import itertools
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
x = json.loads((root/'certificates/discovery.json').read_text())
A = list(itertools.product(range(2), repeat=6))
prefix = lambda a: [1]+[int(sum(a[:k+1])==j) for k in range(6) for j in range(k+1)]
window = lambda a,i:sum(a[1+i:4+i])
g = lambda a:[int(window(a,i)==j) for i in range(3) for j in (0,3)]
ps = [[Q(v).limit_denominator(4096) for v in row] for row in x['pair_witnesses']]
dual = [Q(v).limit_denominator(4096) for v in x['spx_dual']]
d = x['direction']
f = [sum(Q(prefix(a)[j],64) for a in A) for j in range(22)]
targets = [[sum(p*int(window(a,i)==j) for a,p in zip(A,ps[0 if i<2 else 1])) for j in range(4)] for i in range(3)]
for p,pair in zip(ps,((0,1),(0,2),(1,2))):
    assert min(p)>=0 and sum(p)==1
    assert [sum(v*prefix(a)[j] for a,v in zip(A,p)) for j in range(22)]==f
    for i in pair:
        assert [sum(v*int(window(a,i)==j) for a,v in zip(A,p)) for j in range(4)]==targets[i]
slacks = [sum(u*v for u,v in zip(dual,prefix(a)))-sum(u*v for u,v in zip(d,g(a))) for a in A]
assert min(slacks)>=0
upper = sum(u*v for u,v in zip(dual,f))
value = sum(d[2*i]*targets[i][0]+d[2*i+1]*targets[i][3] for i in range(3))
assert value>upper
out = dict(schedules=[''.join(map(str,a)) for a in A],
           witness_numerators=[[int(v*64) for v in p] for p in ps],denominator=64,
           prefix_target=list(map(str,f)),window_target=[list(map(str,v)) for v in targets],
           direction=d,prefix_dual=list(map(str,dual)),pointwise_slacks=list(map(str,slacks)),
           upper=str(upper),value=str(value),gap=str(value-upper))
(root/'certificates/exact.json').write_text(json.dumps(out,indent=2)+'\n')
print('Exact arithmetic pass; gap',value-upper,'(not a Lean proof).')
