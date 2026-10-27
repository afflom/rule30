import numpy as np
T=6000; W=2*T+3; mid=T+1; mask=(1<<W)-1
rows=[1<<mid]
for t in range(T): x=rows[-1]; rows.append(((x<<1)^(x|(x>>1)))&mask)   # bit position = mid - p?  check orientation below
# orientation: rule30 new(p) = x(p-1) xor (x(p) or x(p+1)); with bit index b = mid + p: left neighbour p-1 -> bit b-1 = x<<1 at b
def cell(t,p): return (rows[t]>>(mid+p))&1
# sanity: center column
c=[cell(t,0) for t in range(20)]; print("center:",''.join(map(str,c)))
print("left edge black at -t:",all(cell(t,-t)==1 for t in range(200)), " white beyond:",all(cell(t,-t-1)==0 for t in range(200)))
# regular test along slope -1 diagonals from the left edge: cell(t,p) == cell(t-8, p+8)
B=[]
for t in range(16,T+1):
    j=0
    while j<=2*t and cell(t,j-t)==cell(t-8,j-t+8): j+=1
    B.append((t,j))
import math
for t,j in B[::500]: print(f"t={t:5d}  regular depth from left edge {j:5d}  ratio {j/t:.4f}  boundary position {j-t}")
ts=np.array([t for t,_ in B]); js=np.array([j for _,j in B],float)
k=np.polyfit(ts,js,1); res=js-np.polyval(k,ts)
print(f"fit: depth = {k[0]:.5f} t + {k[1]:.2f}; residual std {res.std():.2f}, max |res| {abs(res).max():.1f}")
# the ether: one period of the wedge pattern near the left edge
t=4000
print("wedge rows (left edge first, 40 cells) at t..t+8:")
for s in range(t,t+9): print(''.join(str(cell(s,p)) for p in range(-s,-s+40)))
