# Group-valued invariants of rule 30: g on k-windows, g(0^k)=e, ordered product over a finite
# configuration (zero background) conserved by one step. Detect non-telescoping solutions.
import itertools, sys
def perm_mul(a,b): return tuple(a[b[i]] for i in range(len(a)))   # a∘b
def gen_group(gens):
    e=tuple(range(len(gens[0]))); G={e}; frontier=[e]
    while frontier:
        nf=[]
        for x in frontier:
            for g in gens:
                y=perm_mul(x,g)
                if y not in G: G.add(y); nf.append(y)
        frontier=nf
    return sorted(G)
S3=gen_group([(1,0,2),(1,2,0)])
D4=gen_group([(1,2,3,0),(3,2,1,0)])
Q8=gen_group([(1,4,3,6,5,0,7,2),(2,7,4,1,6,3,0,5)])
def step(x):
    n=len(x); return [ (x[i-1] if i>0 else 0) ^ (x[i] | (x[i+1] if i+1<n else 0)) for i in range(n)]
def configs(maxw):
    for w in range(1,maxw+1):
        for bits in itertools.product([0,1],repeat=w):
            if bits[0]==1 and bits[-1]==1: yield list(bits)
def wins(x,k):
    pad=[0]*(k)+x+[0]*(k)
    return [sum(pad[i+j]<<j for j in range(k)) for i in range(len(pad)-k+1)]
def prod(G,g,ws,e):
    r=e
    for w in ws: r=perm_mul(r,g[w])
    return r
tests=[]
for x in configs(7):
    y=step([0,0]+x+[0,0])     # room to grow
    tests.append((x,y))
def search(G,name,k):
    e=tuple(range(len(G[0]))); nz=list(range(1,2**k)); found=0; nontriv=0
    pre=[(wins(x,k),wins(y,k)) for x,y in tests]
    for vals in itertools.product(G,repeat=len(nz)):
        g={0:e}; g.update(zip(nz,vals))
        ok=True
        for a,b in pre:
            if prod(G,g,a,e)!=prod(G,g,b,e): ok=False; break
        if ok:
            found+=1
            if any(v!=e for v in vals): nontriv+=1
    print(f"{name} (order {len(G)}), k={k}: solutions {found}, with some g != e: {nontriv}"); sys.stdout.flush()
print("orders",len(S3),len(D4),len(Q8))
search(Q8,"Q8",2); search(S3,"S3",3)
