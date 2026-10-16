#!/usr/bin/env python3
"""Split the generated N32 root into one independently checked file per row."""
from pathlib import Path
import re
f=Path(__file__).resolve().parents[1]/'Snaky'
p=f/'BreakerN32Context00.lean';s=p.read_text()
if 'import Snaky.BreakerN32RootRow' in s:
    raise SystemExit('Already split; regenerate the hierarchical source first to repeat.')
start=s.index('private def row');end=s.index('\ntheorem defense :')
header=s[:start];tail=s[end:];matches=list(re.finditer(r'^private def row(\d+)Domains',s[start:end],re.M));assert len(matches)==24
(f/'BreakerN32RootBase.lean').write_text(header+'\nend Snaky.BreakerN32.C00\n')
imports=[]
for j,m in enumerate(matches):
    n=m.group(1);a=start+m.start();b=start+matches[j+1].start() if j+1<len(matches) else end
    body=s[a:b].replace(f'private theorem row{n}Fresh',f'theorem row{n}Fresh').replace(f'private theorem row{n}Defense',f'theorem row{n}Defense')
    name='BreakerN32RootRow'+n
    (f/(name+'.lean')).write_text('import Snaky.BreakerN32RootBase\n\nnamespace Snaky.BreakerN32.C00\nopen Snaky.Breaker\n'+body+'\nend Snaky.BreakerN32.C00\n')
    imports.append('import Snaky.'+name)
p.write_text('\n'.join(imports)+'\n\nnamespace Snaky.BreakerN32.C00\nopen Snaky.Breaker\n'+tail)
print('Split24 rows without changing their statements or proofs.')
