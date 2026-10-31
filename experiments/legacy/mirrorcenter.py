# Center = parity (interface 1+x) xor sum_k [u^(2^k-1)] B(u), where P(x) is the centered row,
# u = x + 1/x, and P(x) + P(1/x) = u B(u) (the mirror difference, symmetric, divisible by u).
from functools import lru_cache
T=300
def row_evolve(T):
    W=2*T+3; x=[0]*W; x[T+1]=1; mid=T+1; rows=[]
    for t in range(T):
        rows.append({i-mid for i in range(W) if x[i]})
        x=[(x[i-1] if i>0 else 0)^(x[i]|(x[i+1] if i+1<W else 0)) for i in range(W)]
    return rows
@lru_cache(None)
def upow(n):   # u^n as a frozenset of exponents (Laurent, F2)
    if n==0: return frozenset([0])
    prev=upow(n-1); s=set()
    for e in prev:
        for d in (1,-1): s^={e+d}
    return frozenset(s)
def to_u(sym):   # symmetric Laurent set -> set of n with coefficient 1 in u^n
    s=set(sym); out=set()
    while s:
        n=max(s); out^={n}; s^=set(upow(n))
    return out
rows=row_evolve(T); ok=0
for t,P in enumerate(rows):
    Pbar={-e for e in P}
    D=P^Pbar
    Du=to_u(D)                       # D = sum_{n in Du} u^n, with 0 not in Du
    assert 0 not in Du
    Bu={n-1 for n in Du}
    par=len(P)%2
    gamma=sum(1 for k in range(0,20) if (2**k-1) in Bu)%2
    c=1 if 0 in P else 0
    ok+= (c==(par^gamma))
print("center = parity xor Gamma(mirror difference):",ok,"of",T)
# Duhamel in the mirror sector: D_{t+1} = (1+u) D_t + delta_t, delta_t = kappa_t + mirror(kappa_t),
# kappa_t(p) = x_t(p) x_t(p+1) (the carry feeding cell p). Check Gamma(D_t) via binomials mod 2.
def binom2(n,k): return 1 if 0<=k<=n and (k & ~n)==0 else 0
deltas=[]
for t,P in enumerate(rows):
    kap={p for p in P if p+1 in P}
    dl=kap^{-e for e in kap}
    deltas.append(to_u(dl))
ok=0; ok2=0
for t,P in enumerate(rows):
    g=0
    for s in range(t):
        n=t-1-s
        for m in deltas[s]:
            for k in range(0,12):
                g^=binom2(n,2**k-m)
    Du=to_u(P^{-e for e in P}); gamma=sum(1 for k in range(20) if 2**k in Du)%2
    ok+= (g==gamma)
    # parity via carries
print("Gamma(D_t) from the mirror-sector Duhamel sum:",ok,"of",T)
