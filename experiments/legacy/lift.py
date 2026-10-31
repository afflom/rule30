from zbl import Z, col1
def antidiags(L,T):
    """a_k(j) = x_j(k-j), j=1..k, from the sideways reconstruction of start L (depth j = bit j-1)"""
    y=[(col1(L,T+2)>>t)&1 for t in range(T+2)]
    x=[[0]*(T+2), y[:]]
    for j in range(1,T): x.append([x[j][t+1]^(x[j][t]|x[j-1][t]) for t in range(T+1-j)])
    return y,[[x[j][k-j] for j in range(1,k+1)] for k in range(0,T)]
# identity check: delta a_{k+1} = a_k OR shift(a_{k-1}),  a_{k+1}(1) = y(k)
import random; ok=True
for _ in range(200):
    W=random.randrange(2,25); L=random.getrandbits(W)|1<<(W-1); y,a=antidiags(L,W+30)
    for k in range(2,len(a)-1):
        u=[a[k][i-1] | (a[k-1][i-2] if i>=2 else 0) for i in range(1,k+1)]
        ok&= a[k+1][0]==y[k] and all(a[k+1][j]^a[k+1][j-1]==u[j-1] for j in range(1,k+1))
print("a_{k+1}(1) = y(k) and a_{k+1}(j+1) - a_{k+1}(j) = a_k(j) OR a_{k-1}(j-1) (mod 2):",ok)
