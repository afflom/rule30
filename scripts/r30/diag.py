import numpy as np
T=1<<20; D=30
a=[None]*(D+1); z=np.zeros(T,np.uint8)
prev2,prev1=z,z
for d in range(D+1):
    inp=(prev1|prev2)
    cum=np.bitwise_xor.accumulate(inp)            # cum[t] = parity of inp[0..t]
    ad=np.empty(T,np.uint8); ad[0]=1 if d==0 else 0
    ad[1:]=ad[0]^cum[:-1]                          # a_d(t) = [d=0] + sum_{s<t} inp[s]
    a[d]=ad; prev2,prev1=prev1,ad
# check against direct simulation for small t
W=401; mid=200; mask=(1<<W)-1; row=1<<mid; ok=True
for t in range(190):
    for d in range(0,min(D,2*t)+1):
        p=t-d
        if abs(p)<=t: ok &= ((row>>(mid+p))&1)==a[d][t]
    row=((row<<1)^(row|(row>>1)))&mask
print("a_d(t) = [d=0] + sum_{s<t} (a_{d-1}(s) OR a_{d-2}(s)) mod 2:", ok)
print("centre a_t(t), t<=30:", ''.join(str(a[t][t]) for t in range(D+1)))
print(" d  log2(period)  transient  (centre time = d)")
for d in range(D+1):
    x=a[d]; P=1
    while P<T//4:
        tail=x[T//2:]
        if np.array_equal(tail[P:],tail[:-P]): break
        P*=2
    if P>=T//4: print(f"{d:2d}  period > {T//4}"); continue
    # transient: smallest tau with x[t]==x[t+P] for all t>=tau
    neq=np.nonzero(x[:-P]!=x[P:])[0]; tau=0 if len(neq)==0 else int(neq[-1])+1
    print(f"{d:2d}  {P.bit_length()-1:2d}  {tau:8d}")
