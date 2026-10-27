# Muxed Duhamel: c(t) = 1 + sum_{s<t} sum_p kappa_s(p) T(t-1-s, t-1-s-p),  T(n,m) = [x^m](1+x+x^2)^n mod 2,
# split by where the carry sits: settled zero-state region (left of the damage edge), band, right half.
import numpy as np
T=1500
W=2*T+5; mid=T+2
x=np.zeros(W,dtype=np.uint8); x[mid]=1; rows=[]
for t in range(T):
    rows.append(x.copy())
    l=np.roll(x,1); r=np.roll(x,-1); l[0]=0; r[-1]=0
    x=l^(x|r)
# trinomial kernel rows mod 2 via Frobenius-free recursion
K=[np.array([1],dtype=np.uint8)]
for n in range(1,T):
    prev=K[-1]; nxt=np.zeros(len(prev)+2,dtype=np.uint8)
    nxt[:-2]^=prev; nxt[1:-1]^=prev; nxt[2:]^=prev; K.append(nxt)
per,last=np.load("leftdyn_100000_160000.npy"); tau=last+1-1024; tau[last<0]=0
def region(s,p):     # p = centered position at time s; depth j = p + s
    if p>=0: return 2
    j=p+s
    return 0 if tau[j]<=s else 1
c=np.array([rows[t][mid] for t in range(T)])
A=np.zeros((3,T),dtype=np.uint8)
for t in range(1,T):
    for s in range(t):
        n=t-1-s; xs=rows[s]
        kap=xs[:-1]&xs[1:]            # kappa at index i (position i-mid) = x(i) x(i+1)
        idx=np.nonzero(kap)[0]
        for i in idx:
            p=i-mid; m=n-p              # need [x^{-p}] (x^-1+1+x)^n = T(n, n-p)
            if 0<=m<=2*n and K[n][m]:
                A[region(s,p),t]^=1
ok=((1^A[0]^A[1]^A[2])==c)[1:].all()
print("Duhamel decomposition reproduces the center:",ok)
def bm(seq):
    s=list(map(int,seq)); n=len(s); C=[1]+[0]*n; B=[1]+[0]*n; L=0; m=1; b=1
    for i in range(n):
        d=s[i]
        for j in range(1,L+1): d^=C[j]&s[i-j]
        if d==0: m+=1
        elif 2*L<=i:
            Tt=C[:]; 
            for j in range(m,n+1): C[j]^=B[j-m]
            L=i+1-L; B=Tt; m=1
        else:
            for j in range(m,n+1): C[j]^=B[j-m]
            m+=1
    return L
for name,seq in [("zero-state carries",A[0]),("band carries",A[1]),("right-half carries",A[2]),("center",c)]:
    print(f"{name:20s} density {seq[1:].mean():.3f}  linear complexity {bm(seq[1:1201])} / 1200")
