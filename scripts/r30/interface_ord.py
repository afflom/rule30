# How much of each row polynomial X_t (bit i = cell t, t-i; degree 2t) sits at the interfaces 1+x and Phi3?
def pmod(a,b):
    db=b.bit_length()-1
    while a and a.bit_length()-1>=db:
        a^=b<<(a.bit_length()-1-db)
    return a
def pdiv(a,b):
    q=0; db=b.bit_length()-1
    while a and a.bit_length()-1>=db:
        s=a.bit_length()-1-db; q|=1<<s; a^=b<<s
    return q,a
def ordp(a,p):
    k=0
    while a:
        q,r=pdiv(a,p)
        if r: break
        a=q; k+=1
    return k
phi=lambda y: y^((y<<1)|(y<<2))
y=1; o1=[];o3=[];o7=[];o11=[]
for t in range(1,2049):
    y=phi(y)
    o1.append(ordp(y,0b11)); o3.append(ordp(y,0b111)); o7.append(ordp(y,0b1011)); o11.append(ordp(y,0b1101))
import collections
for name,o in [("1+x",o1),("Phi3=1+x+x^2",o3),("1+x+x^3",o7),("1+x^2+x^3",o11)]:
    c=collections.Counter(o); print(f"{name:14s} max ord {max(o)}  distribution {sorted(c.items())[:8]}")
# compare: rule 150 rows have ord_Phi3 = t
