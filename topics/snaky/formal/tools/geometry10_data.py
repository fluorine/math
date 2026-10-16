#!/usr/bin/env python3
"""Emit small untrusted 10-board geometry slices, each checked by Lean's kernel."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1] / 'Snaky'

def lit(v):
    if isinstance(v,list): return '['+', '.join(map(lit,v))+']'
    if isinstance(v,tuple): return '('+', '.join(map(lit,v))+')'
    return str(v)

def main():
    n = int(sys.argv[1]) if len(sys.argv)>1 else 10
    if n not in (10,14): raise ValueError("only requested boards10 and14")
    shape=[(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)]
    rot=lambda s:[(-y,x) for x,y in s]
    # Preserve Game.lean's orientation order, including reflection in the x axis.
    refl=[(x,-y) for x,y in shape]
    raw=[shape,rot(shape),rot(rot(shape)),rot(rot(rot(shape))),
         refl,rot(refl),rot(rot(refl)),rot(rot(rot(refl)))]
    orient=[[(x-min(a for a,b in s),y-min(b for a,b in s)) for x,y in s] for s in raw]
    data=['import Snaky.Game','','namespace Snaky.Geometry10','',
          'def slice (o : List (Int × Int)) (dx : Nat) : List (List Nat) :=',
          '  (List.range 10).filterMap fun (dy : Nat) =>',
          '    let cells : List (Int × Int) := o.map fun p => (p.1 + (dx : Int), p.2 + (dy : Int))',
          '    if cells.all (fun q => decide (q.1 < (10 : Int) ∧ q.2 < (10 : Int))) then',
          '      some (cells.map fun q => q.2.toNat * 10 + q.1.toNat)',
          '    else none','']
    def emit(name, text):
        text=text.replace('Geometry10',f'Geometry{n}').replace('List.range 10',f'List.range {n}').replace('placements 10 10',f'placements {n} {n}').replace('(10 : Int)',f'({n} : Int)').replace('* 10 +',f'* {n} +')
        (HERE/name.replace('Geometry10',f'Geometry{n}')).write_text(text)
    modules=[];names=[]
    for k,o in enumerate(orient):
        data += [f'def orient{k} : List (Int × Int) := {lit(o)}']
        for dx in range(n):
            i=k*n+dx;name=f'part{i:02d}';names.append(name)
            cells=[[n*(y+dy)+x+dx for x,y in o] for dy in range(n)
                   if all(x+dx<n and y+dy<n for x,y in o)]
            data += [f'def {name} : List (List Nat) := {lit(cells)}']
            module=f'Geometry10Slice{i:02d}';modules.append(module)
            emit(f'{module}.lean',
                'import Snaky.Geometry10Data\n\nnamespace Snaky.Geometry10\n'
                'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
                f'theorem slice{i:02d}_eq : slice orient{k} {dx} = {name} := by decide +kernel\n'
                f'theorem part{i:02d}_length : {name}.length = {len(cells)} := by decide +kernel\n'
                'end Snaky.Geometry10\n')
    data += ['', 'def targets : List (List Nat) := '+' ++ '.join(names),'','end Snaky.Geometry10','']
    emit('Geometry10Data.lean','\n'.join(data))
    groups=['import Snaky.Geometry10Data','','namespace Snaky.Geometry10','']
    for k in range(8):
        groups += [f'def group{k} : List (List Nat) := '+' ++ '.join(names[k*n:(k+1)*n])]
    groups += ['','theorem targets_eq_groups : targets = '+' ++ '.join(f'group{k}' for k in range(8))+' := by',
        '  simp only [targets, '+', '.join(f'group{k}' for k in range(8))+', List.append_assoc]',
        '', 'end Snaky.Geometry10','']
    emit('Geometry10GroupsData.lean','\n'.join(groups))
    for k in range(8):
        group=[f'import Snaky.{m}' for m in modules[k*n:(k+1)*n]]+['import Snaky.Geometry10GroupsData',
            '','namespace Snaky.Geometry10','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
            f'theorem group{k}_eq : (List.range 10).flatMap (slice orient{k}) = group{k} := by',
            f'  have hr : List.range 10 = {lit(list(range(n)))} := rfl',
            '  rw [hr]',
            '  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, '+', '.join(f'slice{i:02d}_eq' for i in range(k*n,(k+1)*n))+']',
            '  rfl','','end Snaky.Geometry10','']
        emit(f'Geometry10Group{k}.lean','\n'.join(group))
    out=[f'import Snaky.Geometry10Group{k}' for k in range(8)]+['','namespace Snaky.Geometry10',
        'set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
        'theorem orientations_exact : orientations snaky = ['+', '.join(f'orient{i}' for i in range(8))+'] := by decide +kernel',
        'theorem placements_as_slices : placements 10 10 snaky =',
        '    (orientations snaky).flatMap (fun o => (List.range 10).flatMap (slice o)) := rfl',
        'theorem placements_eq_targets : placements 10 10 snaky = targets := by',
        '  rw [placements_as_slices, orientations_exact, targets_eq_groups]',
        '  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, '+', '.join(f'group{k}_eq' for k in range(8))+']','',
        f'theorem target_count : (placements 10 10 snaky).length = {8*(n-4)*(n-1)} := by',
        '  rw [placements_eq_targets]',
        '  simp only [targets, List.length_append, '+', '.join(f'part{i:02d}_length' for i in range(8*n))+']','',
        'end Snaky.Geometry10','']
    emit('Geometry10.lean','\n'.join(out))
    print(f'Generated{8*n} geometry slices for{n} and exact assembly theorem')

if __name__=='__main__':main()
