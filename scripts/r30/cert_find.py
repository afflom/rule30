import sys
N=int(sys.argv[1]); P=int(sys.argv[2]); M=(1<<(N+1))-1
ring=[None]*P; y=1; t=0
while True:
    if t>=P and ring[t%P]==y:
        print("N",N,"P",P,"minimal T0",t-P); break
    ring[t%P]=y
    y=((y<<2)^((y<<1)|y))&M; t+=1
