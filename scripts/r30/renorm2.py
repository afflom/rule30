import numpy as np
pat=np.load("ether_pat_100000.npy").astype(np.int8)
best=[]
for a in (2,3,4):
    for b in range(-8,9):
        for c in range(32):
            for m in (1,2):
                js=np.arange(400,20000)
                tj=a*js+b
                ok=(tj>=0)&(tj<100000)
                js=js[ok]; tj=tj[ok]
                agree=0; n=0
                for ph in range(16):
                    agree+=(pat[js,ph]==pat[tj,(m*ph+c)%64]).sum(); n+=len(js)
                best.append((agree/n,a,b,c,m))
best.sort(reverse=True); print(best[:5]); print("worst",best[-3:])
