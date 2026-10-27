from zbl import Z, recon
# 1. Q01 in integer form: every X >= 1 reaches an even value at some even step
worst={}
for W in range(1,23):
    m=0
    for X in range(1<<(W-1), 1<<W):
        k=0; Y=X
        while Y&1: Y=Z(Z(Y)); k+=1
        m=max(m,2*k)
    worst[W]=m
print("max death time (even step) by width:", worst)
# 2. rational points of the constrained set: column -1 = 1 at even times, f at odd times
def alt(f,n):
    a=0
    for t in range(n): a|=(1 if t%2==0 else f(t//2))<<t
    return a
def tail(X,N):
    bits=[(X>>i)&1 for i in range(N)]
    for P in range(1,65):
        lo=N//2
        if all(bits[i]==bits[i+P] for i in range(lo,N-P)):
            w=''.join(map(str,bits[N-P:N]))
            return P,w
    return None
N=1600
from collections import Counter
res=Counter(); nonper=0; total=0
for p in range(1,9):
    for q in range(0,3):
        for w in range(1<<p):
            for pre in range(1<<q):
                f=lambda j,w=w,p=p,q=q,pre=pre: (pre>>j)&1 if j<q else (w>>((j-q)%p))&1
                X=recon(alt(f,N+2),N); total+=1
                r=tail(X,N)
                if r is None: nonper+=1
                else: res[r]+=1
print("eventually periodic free bits tested:",total,"| start not eventually periodic:",nonper)
print("tails of eventually periodic starts (period, repeating word read upward):")
for (P,w),n in sorted(res.items()): print("  ",P,w,n)
