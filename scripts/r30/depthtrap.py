# Window relaxation of the depth step in the gauged frame:
#   F_{j+2}(psi) = F_j(psi+1) xor (F_{j+1}(psi) or F_{j+2}(psi-1))
# window psi in [0,w): state (A,B) = (F_j, F_{j+1}) on the window; free inputs:
#   left  = F_{j+2}(-1),   right = F_j(w)   (needed for F_{j+2}(w-1)).
import numpy as np, sys
def step(A,B,w,left,right):
    C=[0]*w; prev=left
    for p in range(w):
        a_next = A[p+1] if p+1<w else right
        C[p]=a_next ^ (B[p] | prev); prev=C[p]
    return B,C
def enc(A,B,w): return sum(A[i]<<i for i in range(w)) | (sum(B[i]<<i for i in range(w))<<w)
def dec(x,w): return [(x>>i)&1 for i in range(w)], [(x>>(w+i))&1 for i in range(w)]
pat=np.load("ether_pat_100000.npy")
for w in range(3,9):
    N=1<<(2*w)
    succ=[set() for _ in range(N)]
    for x in range(N):
        A,B=dec(x,w)
        for l in (0,1):
            for r in (0,1):
                B2,C=step(A,B,w,l,r); succ[x].add(enc(B2,C,w))
    # zero-state windows: F_j(psi) = E_j(psi + j), depths 400..20000, window at psi = 0..w-1
    seen=set()
    for j in range(400,20000):
        A=[int(pat[j][(p+j)%64]) for p in range(w)]; B=[int(pat[j+1][(p+j+1)%64]) for p in range(w)]
        seen.add(enc(A,B,w))
    # forward closure
    clo=set(seen); stack=list(seen)
    while stack:
        x=stack.pop()
        for y in succ[x]:
            if y not in clo: clo.add(y); stack.append(y)
    print(f"w={w}: windows seen in the zero-state {len(seen)} / {N}; forward closure {len(clo)} / {N}"); sys.stdout.flush()
