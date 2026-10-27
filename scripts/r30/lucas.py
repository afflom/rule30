T=400; W=2*T+3; mid=T+1; mask=(1<<W)-1
R30=lambda x: ((x<<1) ^ (x | (x>>1)))&mask
B=lambda x: ((x<<1)^(x>>1))&mask              # rule 90 = l + r
S=lambda x: (x & ~(x>>1))&mask                 # c AND NOT r  (bit p: x(p)=1, x(p+1)=0)
rows=[1<<mid]
for t in range(T): rows.append(R30(rows[-1]))
print("rule30 = rule90 + (c AND NOT r):", all(rows[t+1]==B(rows[t])^S(rows[t]) for t in range(T)))
cstar=[(r>>mid)&1 for r in rows]
# center via Lucas: c*(t) = [t=0] + #{(s,q): s<t, source at q, n=t-1-s, n+d even, C(n,(n+d)/2) odd} mod 2, d = displacement
def cf(n,d):
    if (n+d)&1 or abs(d)>n: return 0
    k=(n+d)//2; return 1 if (k & (n-k))==0 else 0     # Kummer: C(n,k) odd iff k, n-k add without carries
ok=True
src=[[q-mid for q in range(W) if (S(rows[s])>>q)&1] for s in range(T)]
for t in range(1,T):
    v=0
    for s in range(t):
        n=t-1-s
        for q in src[s]: v^=cf(n,q)
    ok &= v==cstar[t]
print("c*(t) = parity of carry-free source incidences, t<400:", ok)
# right side: diagonals d = t - p (d=0 is the right edge)
for d in range(0,12):
    seq=[(rows[t]>>(mid+t-d))&1 for t in range(d,T)]
    per=None
    for P in range(1,129):
        if all(seq[i]==seq[i+P] for i in range(len(seq)//2, len(seq)-P)): per=P;break
    print(f"right diagonal d={d:2d}: eventual period {per}")
