from lift import antidiags
import random
def stats(L,W,T):
    y,a=antidiags(L,T); rows=[]
    for k in range(W,T-2):
        A=a[k]; B=[0]+a[k-1]
        n=len(A); blk=sum(A); N=sum(A[i]|B[i] for i in range(n)); ov=sum(A[i]&B[i] for i in range(n))
        e=max([i+1 for i in range(n) if A[i]] or [0])
        rows.append((k,y[k],e,blk,sum(a[k-1]),ov,N, (y[k]+N)%2))
    return rows
L=int('1011111101100100001'[::-1],2); W=19
print(" k  y(k)  edge  |a_k| |a_k-1| overlap  N_k  next-start-bit(must be 0)")
for r in stats(L,W,W+24): print("%3d %4d %5d %5d %6d %7d %5d %6d"%r)
# exact identity hunt over many random finite starts: is N_k + |a_k AND S a_{k-1}| = |a_k| + |a_{k-1}| (trivial) ...
# test candidate: |a_{k+1}| relation to N_k and positions
ok1=ok2=True
for _ in range(300):
    W=random.randrange(3,24); L=random.getrandbits(W)|1<<(W-1); y,a=antidiags(L,W+30)
    for k in range(W+1,W+28):
        A=a[k]; B=[0]+a[k-1]; u=[A[i]|B[i] for i in range(len(A))]
        # black cells of a_{k+1} = positions with odd prefix height: count via runs
        h=y[k]; cnt=0
        for j in range(len(a[k+1])):
            cnt+=h%2
            if j<len(u): h+=u[j]
        ok1&= cnt==sum(a[k+1])
print("|a_{k+1}| = number of positions at odd height of the staircase y(k) + prefix count of the OR:",ok1)
