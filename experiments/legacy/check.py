import random
from recon import depth, seed_center
M=300; cs=seed_center(30,M)
# 1. reconstruction depth == first disagreement with the true column
ok=True
for _ in range(2000):
    k=random.randrange(1,M-5); c=(cs & ((1<<k)-1)) | (((cs>>k)&1)^1)<<k | (random.getrandbits(M+1-k-1)<<(k+1))
    d=depth(30,c,M); ok &= (d==k)
print("depth(c) = first index where c differs from the true column:", ok)
# 2. Duhamel over F2: x_t = A^t x0 + sum_s A^(t-1-s) Q(x_s), A = rule 150 (l+c+r), Q = c*r
T=200; W=2*T+3; mid=T+1; mask=(1<<W)-1
def A(x): return ((x<<1)^x^(x>>1))&mask
def Q(x): return (x & (x>>1))&mask          # bit p: c(p)*r(p) with r = p+1 neighbour -> x>>1 at bit p
def R30(x): return ((x<<1) ^ (x | (x>>1)))&mask
rows=[1<<mid]
for t in range(T): rows.append(R30(rows[-1]))
acc=1<<mid; good=True
for t in range(T):
    acc = A(acc) ^ Q(rows[t])
    good &= acc==rows[t+1]
print("x_{t+1} = A x_t + Q(x_t) with A = rule 150, Q = c*r:", good)
# 3. kernel center K(n,0) of rule 150 (central trinomial coeff mod 2) and rule 90 (central binomial mod 2)
x=1<<mid; y=1<<mid; k150=[]; k90=[]
for n in range(T):
    k150.append((x>>mid)&1); k90.append((y>>mid)&1); x=A(x); y=((y<<1)^(y>>1))&mask
print("rule-150 kernel centre all 1 for n<200:", all(k150), "| rule-90 kernel centre ones at n =", [n for n,b in enumerate(k90) if b])
