// Vacuum tree BFS in C-world for C<=16. State = x | y<<C.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int C; static uint32_t M;
static inline int bit(uint32_t v,int s){return (v>>(s%C))&1;}
static int succ(uint32_t x,uint32_t y,uint32_t out[2]){
  if(y==0){
    if(__builtin_popcount(x)&1) return 0;
    for(int z0=0;z0<2;z0++){uint32_t z=z0,cur=z0;
      for(int s=0;s<C-1;s++){cur=bit(x,s)^cur; z|=cur<<(s+1);} out[z0]=z;}
    return 2;
  }
  int s0=__builtin_ctz(y); uint32_t z=0; int cur=1^bit(x,s0); z|=(uint32_t)cur<<((s0+1)%C);
  for(int k=1;k<C;k++){int s=(s0+k)%C; cur=bit(x,s)^(bit(y,s)|cur); z|=(uint32_t)cur<<((s+1)%C);}
  out[0]=z; return 1;
}
int main(int argc,char**argv){ uint32_t sx=strtoul(argv[2],0,16), sy=strtoul(argv[3],0,16);
  C=atoi(argv[1]); M=(C==32)?0xffffffffu:((1u<<C)-1);
  uint64_t N=1ull<<(2*C);
  uint8_t *vis=calloc(N/8+1,1);
  uint32_t *cur=malloc(sizeof(uint32_t)*4), *nxt; size_t nc=1, cap=4; cur[0]=sx|(sy<<C); vis[cur[0]>>3]|=1<<(cur[0]&7);
  uint64_t total=1; int d=0; uint32_t last=0;
  while(nc){
    size_t nn=0, ncap=nc*2+4; nxt=malloc(sizeof(uint32_t)*ncap);
    for(size_t i=0;i<nc;i++){uint32_t v=cur[i],x=v&M,y=v>>C,o[2]; int k=succ(x,y,o);
      for(int j=0;j<k;j++){uint32_t w=y|(o[j]<<C); if(!(vis[w>>3]>>(w&7)&1)){vis[w>>3]|=1<<(w&7); nxt[nn++]=w;}}}
    free(cur); cur=nxt; if(nn){d++; last=cur[0];} total+=nn;
    if(0){ printf("depth %d frontier %zu:",d,nn); for(size_t i=0;i<nn;i++) printf(" (%x,%x)",cur[i]&M,cur[i]>>C); printf("\n"); }
    nc=nn;
  }
  printf("C=%d basin %llu height %d\n",C,(unsigned long long)total,d);
}
