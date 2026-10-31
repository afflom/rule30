import random, sys
from zbl import Z
def build(e,N):
    """point of InX with even-depth bits e (dict depth->bit, default 0); odd depths forced"""
    Y=0
    for t in range(N):
        d=t+1
        if d%2==0:
            if e.get(d,0): Y|=1<<(d-1)
        else:
            X=Y
            for _ in range(t): X=Z(X)
            if not X&1: Y|=1<<(d-1)          # pivot: flipping depth t+1 flips column -1 at time t
            # verify
    return Y
def check(Y,N):
    X=Y
    for t in range(0,N-1):
        if t%2==0 and not X&1: return False
        X=Z(X)
    return True
if __name__=="__main__":
    N=int(sys.argv[1]); random.seed(7)
  ok=True; last_bad=[]
  for trial in range(int(sys.argv[2])):
      Wd=random.randrange(2,41)
      e={d:random.getrandbits(1) for d in range(2,Wd+1,2)}
      Y=build(e,N)
      if trial<20: ok&=check(Y,N)
      odd_white=[d for d in range(1,N+1,2) if not (Y>>(d-1))&1]
      last=max(odd_white) if odd_white else 0
      last_bad.append((last,Wd))
  print("constructed points satisfy the constraint (first 20 checked to depth",N,"):",ok)
  r=max(l-2*w for l,w in last_bad)
  print("even bits white beyond depth W: last white odd depth L;  max(L - 2W) =",r, "  max L =",max(l for l,_ in last_bad), " (depth horizon",N,")")
  print("every sampled point is the stripe beyond depth 2W+%d"%max(r,0))
