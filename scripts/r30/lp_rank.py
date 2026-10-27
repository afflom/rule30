import numpy as np, sys
from scipy.optimize import linprog
from scipy.sparse import lil_matrix, csr_matrix, vstack
from zbl import Z
Wmax=int(sys.argv[1]); K=int(sys.argv[2])
def bits(X): return np.array([(X>>i)&1 for i in range(K)],dtype=float)
rows_dec=[]; rows_pos=[]
for X in range(1,1<<Wmax):
    if not X&1: continue
    cur=X
    while True:
        nxt=Z(Z(cur))
        rows_pos.append(bits(cur))
        if not nxt&1: break                     # dies at the next even time: no surviving double step
        rows_dec.append(bits(cur)-bits(nxt))    # E(cur) - E(nxt) >= 1
        cur=nxt
        if cur>>K: raise SystemExit("increase K")
A=np.array(rows_dec); P=np.array(rows_pos)
A,ia=np.unique(A,axis=0,return_index=True); P=np.unique(P,axis=0)
print(f"widths <= {Wmax}: {len(A)} distinct surviving double steps, {len(P)} distinct states, {K} weights")
# feasibility: -A w <= -1, -P w <= 0
res=linprog(np.zeros(K),A_ub=np.vstack([-A,-P]),b_ub=np.concatenate([-np.ones(len(A)),np.zeros(len(P))]),
            bounds=[(None,None)]*K,method="highs")
print("linear ranking E(X) = sum_k w_k x_k exists:",res.status==0, "|", res.message)
if res.status==0: print("weights:",np.round(res.x,3).tolist())
