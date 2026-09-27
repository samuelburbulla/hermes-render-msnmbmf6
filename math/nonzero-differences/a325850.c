// A325850 (faster): with old right diagonal diag[0..L-1], appending x gives
// nd[i] = x - P_i where P_i = diag[0]+...+diag[i-1]. So x is allowed iff x is unused and x != P_i for all i.
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int n; static unsigned FULL;
static ll dfs(int L, const ll *diag, unsigned used){
  if(L==n) return 1;
  ll P[32]; unsigned forb=used; ll s=0;
  for(int i=1;i<=L;i++){ s+=diag[i-1]; P[i]=s; if(s>=1 && s<=n) forb|=1u<<s; }
  unsigned ok=FULL&~forb;
  if(L==n-1) return __builtin_popcount(ok);
  ll cnt=0, nd[32];
  while(ok){ int x=__builtin_ctz(ok); ok&=ok-1;
    nd[0]=x; for(int i=1;i<=L;i++) nd[i]=x-P[i];
    cnt+=dfs(L+1,nd,used|1u<<x); }
  return cnt;
}
int main(int argc,char**argv){
  n=atoi(argv[1]); FULL=((1u<<(n+1))-1)&~1u;
  if(n<=1){ printf("%d 1\n",n); return 0; }
  ll total=0;
  #pragma omp parallel for schedule(dynamic,1) reduction(+:total)
  for(int w=0; w<n*n*n; w++){ int a=w/(n*n)+1, b=(w/n)%n+1, c=w%n+1;   // first three elements
    if(2*a>n+1 || a==b) continue;
    ll mult=(2*a==n+1)?1:2;
    if(n==2){ if(c==1) total+=mult; continue; }
    if(c==a||c==b) continue;
    ll d1[2]={b,b-a};                       // diagonal after 2 elements
    ll d2[3]={c,c-b,(c-b)-(b-a)}; if(d2[2]==0) continue;
    total+=mult*dfs(3,d2,(1u<<a)|(1u<<b)|(1u<<c)); }
  printf("%d %lld\n",n,total);
}
