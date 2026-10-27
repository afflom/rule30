import numpy as np, itertools
from family import mons, ep, V, run
from linearizable import orbit, desc, lin
def depends(code,var):
    tab=[]
    for bits in itertools.product((0,1),repeat=4):
        val=0
        for k,m in enumerate(mons):
            if code>>k&1: val^=int(all(bits[i] for i in m))
        tab.append(val)
    i=var
    return any(tab[j]!=tab[j^(1<<(3-i))] for j in range(16))
if __name__=="__main__":
  rules=[c for c in range(1,1<<10) if depends(c,2) or depends(c,3)]        # depends on d or e: center interior
  eps={c:ep(run(c)) for c in rules}
  nl=[c for c in rules if c>>4]; l=[c for c in rules if not c>>4]
  print(f"rules with the center strictly inside the dependency cone: {len(rules)} (linear {len(l)}, nonlinear {len(nl)})")
  print(f"  linear with periodic center: {sum(1 for c in l if eps[c])}/{len(l)}: {[desc(c) for c in l if eps[c]]}")
  pn=[c for c in nl if eps[c]]
  print(f"  nonlinear with periodic center: {len(pn)}/{len(nl)}")
  lm=[c for c in pn if orbit(c) in lin.values()]
  print(f"    of which the seed orbit is a linear rule's orbit: {len(lm)}; not: {len(pn)-len(lm)}")
  print("    examples not linear:",[desc(c) for c in pn if c not in lm][:15])
