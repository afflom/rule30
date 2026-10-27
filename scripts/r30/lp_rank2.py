import numpy as np
from scipy.optimize import linprog
from zbl import Z
K=80
def data(Wlo,Whi):
    dec=set(); pos=set()
    for X in range(1<<(Wlo-1) if Wlo>1 else 1, 1<<Whi):
        if not X&1: continue
        cur=X
        while True:
            nxt=Z(Z(cur)); pos.add(cur)
            if not nxt&1: break
            dec.add((cur,nxt)); cur=nxt
    B=lambda X: np.array([(X>>i)&1 for i in range(K)],dtype=float)
    A=np.array([B(a)-B(b) for a,b in dec]); P=np.array([B(p) for p in pos])
    return A,P
def fit(A,P,basis):                       # w = basis @ theta
    AB=A@basis; PB=P@basis; n=basis.shape[1]
    r=linprog(np.zeros(n),A_ub=np.vstack([-AB,-PB]),b_ub=np.concatenate([-np.ones(len(AB)),np.zeros(len(PB))]),
              bounds=[(None,None)]*n,method="highs")
    return r
if __name__=="__main__":
  A12,P12=data(1,12); A16,P16=data(13,16)
  print("train: widths<=12:",len(A12),"steps | test: widths 13-16:",len(A16),"steps")
  r=fit(A12,P12,np.eye(K))
  w=r.x; viol=(A16@w<1-1e-9).sum()+(P16@w< -1e-9).sum()
  print("free weights fitted on widths<=12 fail on widths 13-16 at",viol,"of",len(A16)+len(P16),"constraints")
  k=np.arange(1,K+1,dtype=float)
  fams={
   "w_k = a + b k, by parity of k (4 params) + depth-1 offset": np.column_stack([(k%2==1),(k%2==1)*k,(k%2==0),(k%2==0)*k,(k==1)]).astype(float),
   "w_k = a + b k + c k^2, by parity (6 params) + offset": np.column_stack([(k%2==1),(k%2==1)*k,(k%2==1)*k*k,(k%2==0),(k%2==0)*k,(k%2==0)*k*k,(k==1)]).astype(float),
   "w_k = a r^k + b, r in grid, by parity": None,
  }
  for name,Bm in fams.items():
      if Bm is None: continue
      A=np.vstack([A12,A16]); P=np.vstack([P12,P16])
      print(f"{name}: feasible on widths<=16: {fit(A,P,Bm).status==0}")
  A=np.vstack([A12,A16]); P=np.vstack([P12,P16]); ok=[]
  for rr in [0.5,0.7,0.8,0.9,0.95,1.05,1.1,1.2,1.5,2.0]:
      Bm=np.column_stack([(k%2==1)*rr**k,(k%2==0)*rr**k,(k%2==1),(k%2==0),(k==1)]).astype(float)
      ok.append((rr,fit(A,P,Bm).status==0))
  print("geometric-by-parity families feasible on widths<=16:",ok)
