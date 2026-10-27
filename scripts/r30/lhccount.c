// survivor counts N(t): starts with leftmost black exactly at depth W surviving the mask up to time t
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
typedef unsigned __int128 u128;
int main(int argc,char**argv){
  const char*w=argv[1]; int P=strlen(w); int W=atoi(argv[2]); int ph=atoi(argv[3]);
  int T=4*W+20; long *N=calloc(T+1,sizeof(long));
  for(uint64_t m=0;m<(1ull<<(W-1));m++){
    u128 x=((u128)m)|((u128)1<<(W-1)); int t;
    for(t=0;t<T;t++){
      int ct=w[(t+ph)%P]-'0', cn=w[(t+1+ph)%P]-'0';
      if(ct && (int)(x&1)!=!cn) break;
      N[t]++;
      u128 left=x>>1, right=(x<<1)|(u128)ct; x=left^(x|right);
    }
  }
  for(int t=0;t<T;t++){ if(!N[t]) {printf("dead at %d\n",t);break;} int ct=w[(t+ph)%P]-'0'; printf("t=%d c=%d N=%ld\n",t,ct,N[t]); }
}
