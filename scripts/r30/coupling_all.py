import numpy as np
from family import ep, run
from interior import depends
from coupling import coupling
rules=[c for c in range(16,1<<10) if (depends(c,2) or depends(c,3))]
data=[]
for c in rules:
    g=coupling(c,ks=[0,5])
    data.append((c, ep(run(c)) is None, g[0], g[1]))
A=np.array([d[3] for d in data if d[1]]); P=np.array([d[3] for d in data if not d[1]])
print(f"{len(data)} nonlinear interior rules: aperiodic {len(A)}, periodic {len(P)}")
edges=[0,0.001,0.05,0.1,0.15,0.2,0.24,0.26,0.3,0.35,0.4,0.45,0.5,0.6]
ha=np.histogram(A,edges)[0]; hp=np.histogram(P,edges)[0]
print("g_5 bin        aperiodic  periodic")
for i in range(len(edges)-1): print(f"[{edges[i]:.3f},{edges[i+1]:.3f})  {ha[i]:6d}  {hp[i]:6d}")
print("max g_5 among periodic-center rules:",P.max(), " count of aperiodic rules with g_5 <= that:",int((A<=P.max()).sum()))
np.save('coupling_all.npy',np.array([(c,a,g0,g5) for c,a,g0,g5 in data],dtype=float))
