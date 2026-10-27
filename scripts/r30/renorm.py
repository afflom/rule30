# Is epoch (period 16, depths 400..87865) a renormalized copy of epoch (period 8, depths 29..398)?
import numpy as np
pat=np.load("ether_pat_100000.npy")          # pat[j, t mod 64]
def word(j,P,phase_map):                     # E_j restricted to a phase subset, as int
    return tuple(int(pat[j][phase_map(k)%64]) for k in range(P))
# epoch A: period 8, depths 29..398 ; epoch B: period 16, depths 400..87865
A=[tuple(int(pat[j][k]) for k in range(8)) for j in range(29,399)]
best=[]
for r in (0,1):                        # B restricted to phases 2k+r, a period-8 word
    for off in range(16):
        B=[tuple(int(pat[j][(2*k+r+off)%64]) for k in range(8)) for j in range(400,87866)]
        Aset={}
        for i,w in enumerate(A): Aset.setdefault(w,[]).append(i)
        hits=sum(1 for w in B if w in Aset)
        best.append((hits/len(B),r,off))
best.sort(reverse=True); print("fraction of epoch-16 half-words found among epoch-8 words:",best[:4])
# baseline: how many distinct period-8 words exist in epoch A
print("distinct epoch-8 words:",len(set(A)),"of",len(A))
# zero-state readout in the gauged frame: z(s) = E_s(s), transparency E_{s-1}(s)
z=[int(pat[s][s%64]) for s in range(1,100000)]
