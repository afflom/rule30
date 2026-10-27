# Backward closure of the white pattern under rule 30 on spatially periodic (bi-infinite) rows.
# Depth convention: x'_k = x_{k+1} xor (x_k or x_{k-1}).  Given y (period p), a preimage x satisfies
# x_{k+1} = y_k xor (x_k or x_{k-1}): a 4-state transducer; periodic preimages = cycles of the
# one-period map on states, with period p * (cycle length).
def canon(word):                      # word: tuple, primitive-reduce then min rotation
    n=len(word)
    for d in range(1,n+1):
        if n%d==0 and word==word[:d]*(n//d): word=word[:d]; break
    n=len(word); return min(word[i:]+word[:i] for i in range(n))
def preimages(y):
    p=len(y); out=set()
    for s0 in range(4):
        # iterate the one-period map from state s0, find cycle
        seen={}; s=s0; seq=[]
        while s not in seen:
            seen[s]=len(seq); a,b=s>>1,s&1; xs=[a,b]
            for k in range(p): xs.append(y[k]^(xs[-1]|xs[-2]))
            seq.append(xs[2:]); s=(xs[-2]<<1)|xs[-1]
        c=seen[s]; cyc=seq[c:]
        x=tuple(v for blk in cyc for v in blk)      # x_{k+1} for k over the cycle: a period of x
        out.add(canon(x))
    return out
def step(x):
    p=len(x); return tuple(x[(k+1)%p]^(x[k]|x[k-1]) for k in range(p))
