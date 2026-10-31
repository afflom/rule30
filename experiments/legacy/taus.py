# last black cell tau_z of real left diagonal z, for the zero diagonals z of the zero-state
Z=[2,7,28,399,53207,58286,87866]
N=88000; T=125000; M=(1<<N)-1; y=1; last={z:None for z in Z}
masks={z:1<<z for z in Z}
for t in range(T):
    for z in Z:
        if y & masks[z]: last[z]=t
    y=((y<<2)^((y<<1)|y))&M
for z in Z: print(z, last[z], round(last[z]/z,4) if last[z] else None)
