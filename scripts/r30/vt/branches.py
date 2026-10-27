import numpy as np, subprocess
pat=np.load("../ether_pat_100000.npy")
def word(j,C=16): return sum(int(pat[j][s])<<s for s in range(C))
Z=[2,7,28,399,53207,58286,87866]
M=0xffff
for z in Z:
    a=word(z-1); b=word(z+1)
    par=bin(a).count('1')%2
    res=[]
    for child in (b, b^M):
        out=subprocess.run(["./vt2","16","0","%x"%child],capture_output=True,text=True).stdout.strip()
        res.append(out)
    print(z,"a=%04x odd16=%d chosen b=%04x"%(a,par,b),"| chosen:",res[0],"| other:",res[1])
