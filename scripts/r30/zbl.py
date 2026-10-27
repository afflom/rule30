import random
def Z(X):                       # zero-boundary left half, depth k = bit k-1, wall held white
    return (X>>1) ^ (X | (X<<1))
def col1(X,n):                  # column -1 (depth 1) at times 0..n-1, as an int over time
    a=0
    for t in range(n): a|=(X&1)<<t; X=Z(X)
    return a
def recon(a,N):                 # start bits at depths 1..N from column -1 (needs a at times 0..N)
    xkm1=0; xk=a; X=0; n=N+1      # x_0 = wall = 0
    for k in range(1,N+1):
        X|=(xk&1)<<(k-1)
        m=(1<<(n-1))-1
        xn=((xk>>1) ^ (xk | xkm1)) & m   # x_{k+1}(t) = x_k(t+1) xor (x_k(t) or x_{k-1}(t))
        xkm1, xk, n = xk & m, xn, n-1
    return X
ok=True
for _ in range(500):
    W=random.randrange(1,60); X=random.getrandbits(W)|1<<(W-1)
    ok&= recon(col1(X,W+70),W+60)==X
print("sideways reconstruction recovers every finite start:",ok)
