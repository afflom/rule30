import random
from zbl import Z, col1
ok=True
for _ in range(300):
    W=random.randrange(2,30); L=random.getrandbits(W)|1<<(W-1); T=W+40
    y=[(col1(L,T+2)>>t)&1 for t in range(T+2)]
    # x_j(t) by sideways reconstruction: x_0 = 0, x_1 = y, x_{j+1}(t) = x_j(t+1) ^ (x_j(t) | x_{j-1}(t))
    x=[[0]*(T+2), y[:]]
    for j in range(1,T): x.append([x[j][t+1]^(x[j][t]|x[j-1][t]) for t in range(T+1-j)])
    A=lambda k,j: x[j][k-j] if 0<=k-j<len(x[j]) else 0       # anti-diagonal k at depth j
    for k in range(1,T-2):
        s=sum(A(k,i)|A(k-1,i-1) for i in range(1,k+1))%2
        Lk1=(L>>k)&1                                            # start bit at depth k+1
        ok&= Lk1==(y[k]^s)
print("start bit at depth k+1 = y(k) xor parity of #{i<=k : A_k(i) or A_(k-1)(i-1)}:",ok)
