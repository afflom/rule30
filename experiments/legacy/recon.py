import sys
G = {30: lambda C,R,m: C|R, 90: lambda C,R,m: R, 150: lambda C,R,m: C^R, 210: lambda C,R,m: (~C & m) & R}

def tables():
    for r in (30,90,150,210):
        anf=[]
        for mono,mask in (("1",0),("l",4),("c",2),("r",1),("lc",6),("lr",5),("cr",3),("lcr",7)):
            s=0
            for x in range(8):
                if x & ~mask & 7 == 0 and (x & mask)==x: s ^= (r>>x)&1
            if s: anf.append(mono)
        print(r, "ANF =", " + ".join(anf))
    print("90 ^ 150 ^ 210 =", 90^150^210)

def seed_center(rule, M):
    g=G[rule]; W=2*M+3; mask=(1<<W)-1; row=1<<(M+1); col=0
    for t in range(M+1):
        col |= ((row>>(M+1))&1)<<t
        L=(row<<1)&mask; R=row>>1
        row=(L ^ g(row,R,mask))&mask
    return col

def depth(rule, c, M):
    """first m>=1 with the left reconstruction (white right half, column c) black at time 0; None if none <= M"""
    g=G[rule]; W=M+3; mask=(1<<W)-1; row=0; x1=0
    for t in range(M+1):
        x1 |= (row&1)<<t
        L=((row<<1)|((c>>t)&1))&mask; R=row>>1
        row=(L ^ g(row,R,mask))&mask
    xp, xq = c, x1   # x_p, x_{p+1}
    n = M+1
    for m in range(1, M+1):
        n -= 1; cm=(1<<n)-1
        xn = ((xp>>1) ^ g(xp, xq, (1<<(n+1))-1)) & cm
        if xn & 1: return m
        xp, xq = xn, xp & cm
    return None

if __name__=="__main__":
    tables()
    for r in G:
        cs=seed_center(r,200); print(r,"seed center first 40:", ''.join(str((cs>>t)&1) for t in range(40)), "unrefuted to depth 200:", depth(r,cs,200) is None)
