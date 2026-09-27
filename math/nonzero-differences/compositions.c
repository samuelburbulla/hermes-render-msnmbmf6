// Compositions of N whose differences of all degrees >= D are nonzero.
// D=1: A325851, D=2: A325875. Appending part x to a sequence with right diagonal diag[0..L-1]
// gives nd[0]=x, nd[i]=x-P_i with P_i=diag[0]+..+diag[i-1]; need nd[i]!=0 for i>=D.
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int D;
static ll dfs(int L,const ll*diag,int rem){
  if(rem==0) return 1;
  ll P[128],s=0; for(int i=1;i<=L;i++){ s+=diag[i-1]; P[i]=s; }
  ll cnt=0,nd[128];
  for(int x=1;x<=rem;x++){ int ok=1; for(int i=D;i<=L;i++) if(P[i]==x){ok=0;break;}
    if(!ok) continue; nd[0]=x; for(int i=1;i<=L;i++) nd[i]=x-P[i]; cnt+=dfs(L+1,nd,rem-x); }
  return cnt;
}
int main(int argc,char**argv){ D=atoi(argv[1]); int lo=atoi(argv[2]),hi=atoi(argv[3]);
  for(int N=lo;N<=hi;N++){ printf("%d %lld\n",N,dfs(0,0,N)); fflush(stdout);} }
