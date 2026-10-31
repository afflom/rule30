# Dihedral structure transported to rule 30's orbit: y_t = Phi^t(1), t in Z (backward via Phi^{-1} on Z/2^N).
N=1400; M=(1<<N)-1
def phi(x): return (x ^ ((x<<1)|(x<<2))) & M
def phinv(y):
    x=0
    for i in range(N):
        xi=((y>>i)&1) ^ (((x>>(i-1))&1 if i>=1 else 0) | ((x>>(i-2))&1 if i>=2 else 0))
        x|=xi<<i
    return x
T=600
fw=[1]; 
for t in range(T): fw.append(phi(fw[-1]))
bw=[1]
for t in range(T): bw.append(phinv(bw[-1]))
assert phi(bw[5])==bw[4]
c=[(fw[t]>>t)&1 for t in range(T)]          # forward center: bit t of y_t
cb=[(bw[t]>>t)&1 for t in range(T)]         # backward 'center': bit t of y_{-t}
cb1=[(bw[t+1]>>t)&1 for t in range(T-1)]    # bit t of y_{-1-t}
import numpy as np
c=np.array(c); cb=np.array(cb); cb1=np.array(cb1)
print("forward center      :",''.join(map(str,c[:64])))
print("bit t of y_{-t}     :",''.join(map(str,cb[:64])))
print("bit t of y_{-1-t}   :",''.join(map(str,cb1[:64])))
print("agreement c(t) vs bit t of y_{-t}: %.3f"%(c[:T-1]==cb[:T-1]).mean(), " vs bit t of y_{-1-t}: %.3f"%(c[:T-1]==cb1).mean())
# is y_{-t} related to y_t by a digitwise involution on low bits? compare low 64 bits
for t in [1,2,3,5,8,13]:
    print(t, format(fw[t]&((1<<24)-1),'024b')[::-1], format(bw[t]&((1<<24)-1),'024b')[::-1])
