# y_t = Phi^t(1): bit j = cell(t, t-j); bit-length 2t+1; c(t) = bit t (the middle digit).
# Right diagonals R_j(t) = bit j of y_t (from the bottom); left diagonals D_j(t) = bit 2t-j (from the top).
import numpy as np
T=1<<14; J=48
R=np.zeros((J,T),np.uint8); D=np.zeros((J,T),np.uint8); c=np.zeros(T,np.uint8)
y=1; ok=True
for t in range(T):
    ok &= y.bit_length()==2*t+1
    c[t]=(y>>t)&1
    for j in range(J):
        R[j,t]=(y>>j)&1
        if 2*t-j>=0: D[j,t]=(y>>(2*t-j))&1
    y=y^((y<<1)|(y<<2))
print("bit-length of Phi^t(1) is exactly 2t+1 for t <",T,":",ok)
def per_trans(x):
    n=len(x)
    for e in range(0,13):
        P=1<<e
        if 4*P>n: break
        neq=np.nonzero(x[:-P]!=x[P:])[0]
        tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau < n-2*P: return e,tau
    return None,None
print(" j | right: log2 period, transient | left: log2 period, transient")
for j in range(J):
    e,tr=per_trans(R[j]); f,tl=per_trans(D[j])
    print(f"{j:2d} | {e}, {tr} | {f}, {tl}")
