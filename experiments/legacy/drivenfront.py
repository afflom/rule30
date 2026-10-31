# Settle front of the left half driven by a center column u: D t t = u(t), D(j+2)(t+1)=D j t ^ (D(j+1)t | D(j+2)t)
import sys, numpy as np
def run(u, T):
    y=1; rows=[]
    for t in range(T):
        rows.append(y)
        n=((y<<2)^((y<<1)|y)) & ((1<<(t+1))-1)   # bits 0..t (left half at t+1)
        y=n | (u(t+1)<<(t+1))
    return rows
def settle_times(rows,T,J):
    nb=(T+8)//8
    A=np.array([np.unpackbits(np.frombuffer(r.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J] for r in rows],dtype=np.uint8).T  # A[j,t]
    out=[]
    for j in range(J):
        s=A[j,j:]; n=len(s)
        if n<400: break
        found=None
        for p in [1,2,4,8,16,32,64,128,256]:
            tail=s[n//2:]
            if len(tail)>2*p and np.array_equal(tail[p:],tail[:-p]):
                k=n//2
                while k>0 and s[k-1]==s[k-1+p]: k-=1
                found=(p,k); break
        out.append((j,found))
    return out
T=4000; J=2400
# real center
real=run(None,0) if False else None
y=1; cen=[]
row=1; W=2*T+5
import numpy as np
r=np.zeros(W,dtype=np.uint8); c0=T+2; r[c0]=1
for t in range(T+2):
    cen.append(int(r[c0])); r=np.roll(r,1)^(r|np.roll(r,-1))
drivers={'real':lambda t:cen[t],'zero':lambda t:0,'one':lambda t:1,'alt':lambda t:t%2,'p3_110':lambda t:[1,1,0][t%3],'p4_1000':lambda t:int(t%4==0),'p5':lambda t:[1,0,1,1,0][t%5],'p7':lambda t:[1,1,0,1,0,0,0][t%7]}
print("--- eventual patterns vs real (phase-aligned mod 64 at late times)")
def late_pat(rows,T,J):
    nb=(T+8)//8
    last=rows[-64:]
    A=np.array([np.unpackbits(np.frombuffer(r.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J] for r in last],dtype=np.uint8).T
    base=T-64; P=np.zeros((J,64),dtype=np.uint8)
    for i in range(64): P[:,(base+i)%64]=A[:,i]
    return P
Jc=2400
ref=late_pat(run(drivers['real'],T),T,Jc)
print("--- up to phase shift per epoch")
for name,u in drivers.items():
    Pn=late_pat(run(u,T),T,Jc)
    res=[]
    for lo,hi in [(0,3),(3,8),(8,29),(29,400),(400,Jc)]:
        ok=[a for a in range(64) if all(np.array_equal(Pn[j],np.roll(ref[j],a)) for j in range(lo,hi))]
        res.append(ok[:3])
    print(name,res)
