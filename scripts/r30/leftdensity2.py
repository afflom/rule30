import leftdensity as L
from linearizable import desc
names=['a+d+e+cd+de','a+b+c+e+bc+bd+de','a+b+c+e+bc+cd','a+c+d+e+ce','a+b+e+bc','a+b+c+d+bc+be+cd+de']
from family import mons
V=['b','c','d','e']
def code_of(name):
    terms=name.split('+')[1:]; c=0
    for k,m in enumerate(mons):
        if ''.join(V[i] for i in m) in terms: c|=1<<k
    return c
for n in names:
    c=code_of(n); out=[]
    for T in (300,600,1200):
        L.T=T; out.append(round(L.left_activity_density(c),4))
    print(f"{n:24s} left activity density at T=300,600,1200: {out}")
