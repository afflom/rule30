# 2-adic interpolation u -> Phi^u(1) on Z_2 (Phi(x) = x xor (2x or 4x), the right-edge frame of rule 30).
# Mahler coefficients a_k = sum_j (-1)^(k-j) C(k,j) Phi^j(1), computed mod 2^N; report v_2(a_k).
import sys
N=int(sys.argv[2]); K=int(sys.argv[1]); M=(1<<N)-1
orb=[1]
for j in range(K): x=orb[-1]; orb.append((x ^ ((2*x)|(4*x))) & M)
def v2(a):
    a&=M
    return N if a==0 else (a & -a).bit_length()-1
diff=orb[:]; vals=[]
for k in range(K+1):
    vals.append(v2(diff[0]))
    diff=[(diff[i+1]-diff[i]) & M for i in range(len(diff)-1)]
print("k: v2(a_k)")
for k in range(0,K+1,max(1,K//40)): print(f"{k:5d}: {vals[k]:5d}   v2(k!)={k - bin(k).count('1'):5d}")
import math
mins=[min(vals[k:]) for k in range(K+1)]
print("min over k>=2^m of v2(a_k):", [(m, mins[1<<m]) for m in range(int(math.log2(K))+1)])
