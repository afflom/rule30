import random
from stlib import build
from collections import Counter
N=500; random.seed(7); res=Counter(); ex=None
for trial in range(200):
    Wd=random.randrange(2,41)
    e={d:random.getrandbits(1) for d in range(2,Wd+1,2)}
    Y=build(e,N)
    ow=[d for d in range(1,N+1,2) if not (Y>>(d-1))&1]
    last=max(ow) if ow else 0
    if last < 2*Wd+40: res['stripe tail']+=1
    else:
        res['no stripe tail']+=1
        if ex is None or Wd<ex[0]: ex=(Wd,e,Y)
print(res)
Wd,e,Y=ex
print("smallest W without a stripe tail:",Wd,"  odd depths, 1 = black, from depth 1:")
print(''.join(str((Y>>(d-1))&1) for d in range(1,N+1,2)))
