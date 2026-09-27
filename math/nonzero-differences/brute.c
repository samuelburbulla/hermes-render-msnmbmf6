// Literal definition: build the whole difference table of each sequence and test for zeros.
// mode p: all permutations of [n] (degrees>=1). mode c D: all compositions of n (degrees>=D).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static int good(const ll*s,int m,int D){ ll r[64]; memcpy(r,s,m*sizeof(ll));
  for(int k=1;k<m;k++){ for(int i=0;i<m-k;i++){ r[i]=r[i+1]-r[i]; if(k>=D && r[i]==0) return 0; } } return 1; }
static int nextperm(ll*a,int n){ int i=n-2; while(i>=0&&a[i]>=a[i+1]) i--; if(i<0) return 0; int j=n-1; while(a[j]<=a[i]) j--;
  ll t=a[i];a[i]=a[j];a[j]=t; for(int l=i+1,r=n-1;l<r;l++,r--){t=a[l];a[l]=a[r];a[r]=t;} return 1; }
int main(int argc,char**argv){
  if(argv[1][0]=='p'){ int n=atoi(argv[2]); ll a[64]; for(int i=0;i<n;i++) a[i]=i+1; ll c=0; do c+=good(a,n,1); while(nextperm(a,n)); printf("perm %d %lld\n",n,c); }
  else { int D=atoi(argv[2]), n=atoi(argv[3]); ll c=0; ll s[64];
    for(unsigned long long mask=0; mask < (1ULL<<(n-1)); mask++){ int m=0; ll cur=1;   // bit i set => cut after position i+1
      for(int i=0;i<n-1;i++){ if(mask>>i&1){ s[m++]=cur; cur=1;} else cur++; } s[m++]=cur; c+=good(s,m,D); }
    printf("comp D=%d %d %lld\n",D,n,c); }
}
