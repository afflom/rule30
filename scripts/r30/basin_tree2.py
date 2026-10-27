from basin_tree import preimages, canon
from collections import Counter
basin={canon((0,)):0}; frontier=[canon((0,))]; d=0; log=[]
while frontier and d<5000:
    d+=1; new=[]
    for y in frontier:
        for x in preimages(y):
            if x not in basin: basin[x]=d; new.append(x)
    frontier=new
    if d%250==0 or not frontier: log.append((d,len(frontier),sorted(Counter(len(x) for x in frontier).items())))
for l in log[-8:]: print(l)
print("terminated:",not frontier,"| classes:",len(basin),"| max steps:",max(basin.values()))
print("periods:",sorted(Counter(len(x) for x in basin).items()))
