# Vacuum tree of the depth map in C-world: states (x,y), x,y in F2^C (bits = phases s mod C).
# Forward: z(s+1) = x(s) ^ (y(s) | z(s)), cyclic mod C.
import sys
from collections import deque
def succ(x,y,C):
    M=(1<<C)-1
    bit=lambda v,s:(v>>(s%C))&1
    if y==0:
        if bin(x).count('1')%2: return []
        out=[]
        for z0 in (0,1):
            z=z0; cur=z0
            for s in range(C-1):
                cur=bit(x,s)^cur; z|=cur<<(s+1)
            out.append((y,z))
        return out
    # find a phase with y=1: z there+1 = ~x
    s0=next(s for s in range(C) if bit(y,s))
    zs=[0]*C; cur=1^bit(x,s0); zs[(s0+1)%C]=cur
    for k in range(1,C):
        s=(s0+k)%C
        cur=bit(x,s)^(bit(y,s)|cur); zs[(s+1)%C]=cur
    return [(y,sum(b<<i for i,b in enumerate(zs)))]
C=int(sys.argv[1])
start=(0,0)
depth={start:0}; q=deque([start]); maxd=0; far=start
while q:
    v=q.popleft()
    for w in succ(*v,C):
        if w not in depth:
            depth[w]=depth[v]+1; q.append(w)
            if depth[w]>maxd: maxd=depth[w]; far=w
print("C=%d basin size %d, height %d"%(C,len(depth),maxd))
# zero-state path in C-world: start at vacuum, edge (1,1) is at depth? (0,0)->(0,1)->(1,1)
