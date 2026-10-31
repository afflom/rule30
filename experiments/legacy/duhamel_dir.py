# Duhamel: c(t) = 1 + sum_{s<t} sum_p K(t-1-s, p) Q_s(p)  (mod 2), K = rule-150 kernel, Q_s(p) = x_s(p) x_s(p+1).
# Decompose the active corrections by direction d = -p/(t-1-s) (slope from source to target) and by lag.
import numpy as np
T=1024; W=2*T+5; mid=T+2
X=np.zeros((T+1,W),np.uint8); X[0,mid]=1
for t in range(T):
    x=X[t]; X[t+1,1:-1]=x[:-2]^(x[1:-1]|x[2:])
Q=np.zeros_like(X); Q[:,:-1]=X[:,:-1]&X[:,1:]                     # source at (s,p): x(p) x(p+1)
K=np.zeros((T+1,W),np.uint8); K[0,mid]=1
for m in range(T):
    k=K[m]; K[m+1,1:-1]=k[:-2]^k[1:-1]^k[2:]
c=X[:,mid]
bins=np.linspace(-1,1,21)
hist_all=np.zeros(20); ok=True
band_pred={th:0 for th in (0.1,0.25,0.5,0.75,0.9,1.0)}
lag_pred={L:0 for L in (4,16,64,256,10**9)}
for t in range(1,T+1):
    tot=0; contrib_d=[]; contrib_lag=[]
    for s in range(t):
        m=t-1-s
        # contribution of source (s,p) to (t,0): K[m] at displacement -p, i.e. K[m, mid - p] with p = col - mid
        row=Q[s]; ker=K[m][::-1]                                     # ker[col] = K[m, 2mid - col] = displacement -(col-mid)
        act=np.nonzero(row & ker[ (np.arange(W)) ])[0] if False else np.nonzero(row & np.roll(K[m][::-1], 2*mid-(W-1)))[0]
        if len(act)==0: continue
        p=act-mid
        d=-p/m if m>0 else np.zeros(len(p))
        contrib_d.append(d); contrib_lag.append(np.full(len(p),m))
    if contrib_d:
        d=np.concatenate(contrib_d); lg=np.concatenate(contrib_lag)
    else:
        d=np.zeros(0); lg=np.zeros(0)
    ok &= ((1+len(d))%2)==c[t]
    hist_all+=np.histogram(d,bins)[0]
    for th in band_pred: band_pred[th]+= ((1+int((np.abs(d)<=th).sum()))%2)==c[t]
    for L in lag_pred: lag_pred[L]+= ((1+int((lg<L).sum()))%2)==c[t]
print("Duhamel reproduces c(t) for t<=%d:"%T, ok)
print("active corrections by direction (slope bins from -1 to 1):", hist_all.astype(int).tolist())
print("agreement of c(t) with the parity of corrections from |direction| <= theta:",{k:round(v/T,3) for k,v in band_pred.items()})
print("agreement with corrections of lag < L:",{k:round(v/T,3) for k,v in lag_pred.items()})
