# Rule 30 at the interfaces of its linear part: x = 1 (prime 1+x) and x = w in F4 (prime 1+x+x^2).
# F4 = {0,1,w,w^2}, encoded 0,1,2,3 with w^2 = w+1.
def f4mul(a,b):
    if a==0 or b==0: return 0
    lg={1:0,2:1,3:2}; ex={0:1,1:2,2:3}
    return ex[(lg[a]+lg[b])%3]
def f4pow_w(p): return {0:1,1:2,2:3}[p%3]     # w^p
T=400; W=2*T+3
x=[0]*W; x[T+1]=1; mid=T+1
ok_w=ok_1=True
for t in range(T):
    y=[ (x[i-1] if i>0 else 0) ^ (x[i] | (x[i+1] if i+1<W else 0)) for i in range(W)]
    Xw_next=0; Kw=0; P_next=0; P=0; K1=0
    for i in range(W):
        p=i-mid
        if y[i]: Xw_next^=f4pow_w(p); P_next^=1
        if x[i]: P^=1
        if i+1<W and x[i] and x[i+1]: Kw^=f4pow_w(p); K1^=1
    if Xw_next!=Kw: ok_w=False
    if P_next!=P^K1: ok_1=False
    x=y
print("F4 interface: X_{t+1}(w) = K_t(w) for all t <",T,":",ok_w)
print("parity interface: P_{t+1} = P_t + K_t(1) for all t <",T,":",ok_1)
