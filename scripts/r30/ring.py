def ring_step(w,P):            # rule 30 on Z/P, bit i = depth i (left neighbour = depth i+1)
    m=(1<<P)-1
    up=((w>>1)|((w&1)<<(P-1)))&m      # x_{i+1}
    dn=((w<<1)|(w>>(P-1)))&m          # x_{i-1}
    return up ^ (w | dn)
def rot(w,P): return ((w>>1)|((w&1)<<(P-1)))&((1<<P)-1)
def primitive(w,P):
    return all(not(P%d==0 and w==sum(((w>>(i%d))&1)<<i for i in range(P)) ) for d in range(1,P))
def cycles(P):
    """time-cycles of the ring map, grouped up to rotation; returns list of (rep word, cycle length)"""
    m=1<<P; seen=set(); out=[]
    oncycle=set()
    for w in range(m):
        path={}; x=w
        while x not in path and x not in oncycle and x not in seen: path[x]=len(path); x=ring_step(x,P)
        if x in path:                       # new cycle found
            cyc=[]; y=x
            while True:
                cyc.append(y); y=ring_step(y,P)
                if y==x: break
            oncycle.update(cyc)
            key=min(min(r for r in rots(c,P)) for c in cyc)
            out.append((key,len(cyc),cyc))
        seen.update(path)
    # merge cycles equal up to rotation
    d={}
    for key,L,cyc in out: d.setdefault(key,(L,cyc))
    return [(k,L,c) for k,(L,c) in sorted(d.items()) if primitive(k,P) or k in (0,)]
def rots(w,P):
    r=[w]
    for _ in range(P-1): w=rot(w,P); r.append(w)
    return r
if __name__=="__main__":
    for P in range(1,17):
        cs=cycles(P)
        print(P, len(cs), "cycle classes; lengths", sorted(L for _,L,_ in cs)[:20])
