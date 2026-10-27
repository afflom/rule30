import random
from zbl import Z
def runs(X,n):
    b=[(X>>i)&1 for i in range(n)]; out=[]; i=0
    while i<n:
        j=i
        while j<n and b[j]==b[i]: j+=1
        out.append((b[i],i+1,j)); i=j            # (colour, first depth, last depth)
    return out
okW=okB=True; nW=nB=0
for _ in range(3000):
    n=200; X=random.getrandbits(n) | 1<<(n-1)
    Y=Z(X)
    for col,a,b in runs(X,n-3):
        if a<3 or b>=n-3: continue
        if col==0 and b-a+1>=3:                    # white run a..b, black at a-1 and b+1
            nW+=1; okW &= all(((Y>>(d-1))&1)==0 for d in range(a+1,b)) and (Y>>(a-1))&1==1 and (Y>>(b-1))&1==1
        if col==1 and b-a+1>=2:                    # black run a..b, white at a-1 and b+1
            nB+=1; okB &= all(((Y>>(d-1))&1)==0 for d in range(a,b)) and (Y>>(b-1))&1==1
print(f"white run of length g>=3 becomes exactly a white run of length g-2 (both edges move in one step): {okW} on {nW} runs")
print(f"black run of length g>=2 becomes a white run of length g-1 ending at a black cell: {okB} on {nB} runs")
# preimages of rows with an infinite white or black tail (backward transducer, choice of depth-1 cell)
def pre(y,x1,n):
    x=[0,x1]                                       # x[0] = wall
    for k in range(1,n): x.append(((y>>(k-1))&1) ^ (x[k] | x[k-1]))
    return x[1:]
for _ in range(3):
    W=random.randrange(4,12); y=random.getrandbits(W)|1<<(W-1)
    for x1 in (0,1):
        x=pre(y,x1,W+24); print("row width",W,"depth-1 choice",x1,"-> preimage tail", ''.join(map(str,x[W:W+24])))
