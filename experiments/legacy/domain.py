from zbl import Z, recon
def alt(f,n):
    a=0
    for t in range(n): a|=(1 if t%2==0 else f(t//2))<<t
    return a
N=1600
found={}
for p in range(1,9):
  for q in range(0,3):
    for w in range(1<<p):
      for pre in range(1<<q):
        f=lambda j: (pre>>j)&1 if j<q else (w>>((j-q)%p))&1
        X=recon(alt(f,N+2),N); bits=[(X>>i)&1 for i in range(N)]
        P=next((P for P in range(1,65) if all(bits[i]==bits[i+P] for i in range(N//2,N-P))),None)
        if P in (14,60) and P not in found: found[P]=(X,(p,q,w,pre))
def ether_mask(row,depth):
    """for each position, is the local 2*14 window period-2 or period-7?"""
    s=''
    for i in range(depth):
        win=[(row>>(i+j))&1 for j in range(14)]
        if all(win[j]==win[j+2] for j in range(12)): s+='s'
        elif all(win[j]==win[j+7] for j in range(7)): s+='e'
        else: s+='.'
    return s
for P,(X,src) in found.items():
    print(f"tail period {P}, free bits (p,q,w,pre)={src}; rows at even times, depth 1..90 (s = stripe-periodic window, e = period-7 window):")
    Y=X
    for t in range(0,121,2):
        if t%12==0: print(f"  t={t:3d} ", ''.join(str((Y>>i)&1) for i in range(90)))
        if t%12==0: print("        ", ether_mask(Y,90))
        Y=Z(Z(Y))
