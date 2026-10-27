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
