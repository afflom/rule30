#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
/* least period of bit j of Phi^t(1), Phi(x)=x^((2x)|(4x)), for j<=J; periods divide 2^j */
int main(){
  int J=30;
  for(int j=0;j<=J;j++){
    uint64_t mask=(j+1>=64)?~0ULL:((1ULL<<(j+1))-1);
    uint64_t N=1ULL<<j;               /* period divides 2^j */
    unsigned char *b=malloc(N);
    uint64_t x=1;
    for(uint64_t t=0;t<N;t++){ b[t]=(x>>j)&1; x=(x^((x<<1)|(x<<2)))&mask; }
    uint64_t P=N;
    while(P>1){ uint64_t h=P/2; int ok=1; for(uint64_t t=0;t+h<N;t++) if(b[t]!=b[t+h]){ok=0;break;} if(!ok)break; P=h; }
    printf("%d %llu\n",j,(unsigned long long)P); fflush(stdout); free(b);
  }
}
