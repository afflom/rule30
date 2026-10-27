# Zero-state activity: in the settled left region (diagonal coordinates), does any nonlinear monomial fire?
import numpy as np, itertools, sys
from seeds_ep import evolve_seed, col_ep
def zs_activity(monos,r,seed=1,T=3000,K=512):
    w=seed.bit_length(); rows,mid=evolve_seed(monos,r,T,seed,w)
    J=r*T; mask=(1<<J)-1
    ys=[(rows[t]>>(mid-r*t))&mask for t in range(T+1)]
    st=mask
    for t in range(T-K,T+1): st&=~(ys[t]^ys[t-K])
    fu=((~st)&mask); depth=(fu&-fu).bit_length()-1 if fu else J   # all depths < depth settled
    # activity at depth j, time t: product over offsets o of y_t[j+o]  (diagonal coords: same time, position shift o)
    nl=[m for m in monos if len(m)>=2]
    act_cells=0; tot=0; first=None
    for t in range(T-K,T):
        y=ys[t]; a=0
        for m in nl:
            term=mask
            for o in m: term&= (y>>o) if o>0 else (y<<(-o))
            a|=term
        a&=(1<<max(depth-r,0))-1      # only depths whose neighbourhood is settled
        c=bin(a).count('1'); act_cells+=c; tot+=max(depth-r,0)
        if a and first is None: first=(a&-a).bit_length()-1
    return depth, act_cells/max(tot,1), first
off=[-1,0,1,2]; mons=[(i,) for i in range(4)]+list(itertools.combinations(range(4),2))
A=[[(-2,)]+[tuple(off[i] for i in mons[k]) for k in range(10) if code>>k&1] for code in range(1,1<<10)]
from extrapolate import symmetric
res={'EP_free':0,'EP_act':[], 'AP_free':[], 'AP_act':0}
for monos in A:
    if not any(len(m)>=2 for m in monos) or symmetric(monos): continue
    rows,mid=evolve_seed(monos,2,1200,1,1)
    ep=col_ep(rows,mid,1200) is not None
    d,dens,first=zs_activity(monos,2,T=1500,K=256)
    if d<200: continue
    if ep:
        if first is None: res['EP_free']+=1
        else: res['EP_act'].append((round(dens,4),first,d,monos))
    else:
        if first is None: res['AP_free'].append((d,monos))
        else: res['AP_act']+=1
print("EP centers: zero-state activity-free",res['EP_free'],"active",len(res['EP_act']))
for x in sorted(res['EP_act'])[-10:]: print("   EP active:",x)
print("aperiodic: active",res['AP_act'],"activity-free",len(res['AP_free']))
for x in res['AP_free'][:8]: print("   AP free:",x)
