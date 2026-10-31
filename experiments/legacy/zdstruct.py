import numpy as np
pat=np.load("ether_pat_100000.npy"); J=pat.shape[0]
def per(row):
    for p in [1,2,4,8,16,32,64]:
        if np.array_equal(row,np.roll(row,p)): return p
    return None
P=[per(pat[j]) for j in range(J)]
Z=[j for j in range(J) if not pat[j].any()]
O=[j for j in range(J) if pat[j].all()]
print("zero diagonals:",len(Z),Z[:40], Z[-10:])
print("black diagonals:",len(O),O[:40])
# check structure
bad1=[z for z in Z if z>=2 and not np.array_equal(pat[z-1],pat[z-2])]
bad2=[z for z in Z if z+2<J and not pat[z+2].all() and pat[z+1].any()]
print("E(z-1)!=E(z-2):",bad1[:10]," E(z+2) not black with E(z+1)!=0:",bad2[:10])
# period changes
ch=[(j,P[j-1],P[j]) for j in range(1,J) if P[j]!=P[j-1]]
print("period changes (first 30):",ch[:30])
mx=1; dbl=[]
for j in range(J):
    if P[j]>mx: dbl.append((j,P[j])); mx=P[j]
print("new max period at depth:",dbl)
cz=[(z, int(pat[z+1][(z+1)%64]), int(pat[z-1][z%64]), int(pat[z+1].sum()%2)) for z in Z if 1<=z<J-1]
print("(z, center at z+1, col-1 at z, weight parity E(z+1)) first 40:",cz[:40])
