#include <iostream>
#include <algorithm>
#include <vector>
#include <string>
#include <utility>
#include <set>
#include <map>
#include <cmath>
#include <queue>
#include <cstdio>
#include <limits>
#include <bitset>
#include <chrono>
#include <random>
#define rep(i,n) for(int i = 0; i < n; ++i)
#define rep1(i,n) for(int i = 1; i <= n; ++i)
#define rev(i,s,t) for(int i = s; i >= t; --i) 
#define printVec(vec) for(auto tmp: vec) {cout << tmp << " ";} cout << "\n";
#define print2(a, b) cout << a << ":" << b << "\n";
using namespace std;
template<class T>bool chmax(T &a, const T &b) { if(a < b){ a = b; return 1; } return 0; }
template<class T>bool chmin(T &a, const T &b) { if(a > b){ a = b; return 1; } return 0; }
template<class T> inline int sz(T &a) { return a.size(); }
using ll = long long; using ld = long double;
using pi = pair<int,int>; using pl = pair<ll,ll>;
using vi = vector<int>; using vvi = vector<vi>;
using vl = vector<ll>; using vvl = vector<vl>;
using PQ = priority_queue<int, vi, greater<int>>;
const int inf = numeric_limits<int>::max();
const ll infll = numeric_limits<ll>::max();
vi dx = {1, 0, -1, 0};
vi dy = {0, 1, 0, -1};
template<typename T>
struct Vec2 {
  T X; T Y;
  bool operator == (const Vec2& r) const { return (X == r.X && Y == r.Y); }
  bool operator != (const Vec2& r) const { return !(*this == r); }
  bool operator < (const Vec2& r) const { if(X == r.X) return Y < r.Y; return X < r.X; }
  bool operator > (const Vec2& r) const { if(X == r.X) return Y > r.Y; return X > r.X; }
};

// Modint
// modint<MOD> で宣言
template<long long MOD>
struct modint{
  long long x;
  long long mod = MOD;
  modint(long long x=0):x(x%MOD){}
  modint& operator+=(const modint a){ if((x+=a.x)>=MOD) x-=MOD; return *this; }
  modint& operator-=(const modint a){ if((x += MOD-a.x)>=MOD) x-=MOD; return *this; }
  modint& operator*=(const modint a){ (x*=a.x)%=MOD; return *this; }
  modint operator+(const modint a) const{ modint res(*this); return res+=a; }
  modint operator-(const modint a) const{ modint res(*this); return res-=a; }
  modint operator*(const modint a) const{ modint res(*this); return res*=a; }
  modint pow(long long t) const{ if(!t) return 1; modint a = pow(t>>1); a*=a; if(t&1) a*=*this; return a; }
  modint inv() const{ return pow(MOD-2); }
  modint& operator/=(const modint a){ return (*this) *= a.inv(); }
  modint operator/(const modint a) const{ modint res(*this); return res/=a; }
};
using mint = modint<1000000007>;
using mint998 = modint<998244353>;
using vm = vector<mint>;
using vmm = vector<vm>;
using vm998 = vector<mint998>;
using vmm998 = vector<vm998>;
const int NMAX=1000010; // we can calculate nCk until n is equal to NMAX
mint fact[NMAX],infac[NMAX];
void Make_Fact(){ fact[0]=fact[1]=1; for(int i=2;i<=NMAX-1;++i){ fact[i]=fact[i-1]*(mint)i;}}
void Make_InvFact(){ infac[0]=infac[1]=1; for(int i=2;i<=NMAX-1;++i){ infac[i]=infac[i-1]/(mint)i;}}
mint Comb(int n,int k){ if(n<0||k<0||n-k<0) return 0; return fact[n]*infac[k]*infac[n-k]; }

//----------------------------
// 抽象化セグ木
// 二項演算と単位元を渡して使ってね
///****例****************************
//  auto f = [&](int a,int b){ return a+b;}; // 二項演算:和
//  int id = 0; //単位元:0
//  SegTree<decltype(f),int> seg(f,id);
//************************************
//----------------------------
template <typename F,typename T>
struct SegTree{
  T identity; F merge; int size; vector<T> dat; // 二項演算merge,単位元identify
  SegTree(F f,T id):merge(f),identity(id){} // 二項演算fと単位元idを渡して宣言する
  void init(int n){ size = 1; while(size<=n) size *= 2; dat.resize(size*2-1,identity); } // データの要素の数nを渡して初期化、sizeはnより大きい2の冪乗  
  void build(vector<T> vec){ rep(i,vec.size()) dat[size-1+i] = vec[i]; dfs(0); } // 配列を渡して0(n)で初期化  
  T dfs(int k){ if(k>=size-1) return dat[k]; else return dat[k] = merge(dfs(2*k+1),dfs(2*k+2)); }
  // index kの要素をaに変更
  void update(int k,T a){ k += size - 1; dat[k] = a; while(k > 0){ k = (k-1)/2; dat[k] = merge(dat[2*k+1],dat[2*k+2]); } } 
  // index kの要素にaを加算
  void add(int k,T a){ k += size - 1; dat[k] += a; while(k > 0){ k = (k-1)/2; dat[k] = merge(dat[2*k+1],dat[2*k+2]); }}
  // 区間[a,b)に対するクエリに答える。(k,l,r)=(0,0,size)
  T query(int a,int b,int k,int l,int r){ if(r<=a||b<=l) return identity; if(a<=l&&r<=b) return dat[k];  else return merge(query(a,b,2*k+1,l,(l+r)/2),query(a,b,2*k+2,(l+r)/2,r)); }
  T query(int a,int b){ return query(a, b, 0, 0, size); }
  // デバッグ用
  void show(){ int index = 0; int num = 1; while(index<size){ rep(i,num){ if(dat[i+index]==identity) cout << "e "; else cout << dat[i+index] << " "; } cout << "\n"; num *= 2; index = index*2+1; }}
};

struct UFT{
  vector<int> par;//親
  vector<int> rank;//木の深さ
  vector<int> size;//木の大きさ
  int n;
  
  UFT(int _n) { n = _n; par.resize(n); rank.assign(n,0); size.assign(n,1); rep(i,n){ par[i] = i; }}
  //xの根を返す
  int find(int x) { if(par[x] == x) return x; else return par[x] = find(par[x]);}
  //x,yを併合
  void unite(int x,int y) {
    x = find(x);
    y = find(y);
    if(x == y) return;
    if(rank[x] < rank[y]){
      par[x] = y;
      size[y] += size[x];
    }
    else{
      par[y] = x;
      size[x] += size[y];
      if(rank[x] == rank[y]) rank[x]++;
    }
  }
  //x,yが同じグループにいるかどうかを返す
  bool same(int x,int y) { return find(x) == find(y); }
  //xの属する木のサイズを探す
  int usize(int x) { return size[find(x)]; }
};

unsigned int randxor()
{
    static unsigned int x=123456789,y=362436069,z=521288629,w=88675123;
    unsigned int t;
    t=(x^(x<<11));
    x=y;y=z;z=w; 
    return( w=(w^(w>>19))^(t^(t>>8)) );
}

struct Edge{
  int f,t,c,id;
  Edge(int _f, int _t, int _c, int _id) : f(_f), t(_t), c(_c), id(_id){}
};

int N,M,K;
vi X,Y;
vi U,V,W;
vi A,B;
vector<Edge> sortedEdge;
// 基地局から見て住人を近い順に並べたもの{距離, 番号}
vector<vector<pi>> distanceMap;
// 住人からみて基地局を近い順に並べたもの{距離, 番号}
vector<vector<pi>> distanceNode;

ll CalcDist(int i, int j){
  return (A[i] - X[j]) * (A[i] - X[j]) + (B[i] - Y[j]) * (B[i] - Y[j]);
}

ll CalcMinP(ll dist){
  ll lb = 0, ub = 1e+9;
  while(ub - lb > 1) {
    ll mid = (ub + lb) / 2;
    if(dist <= mid * mid) ub = mid;
    else lb = mid;
  }
  return ub;
}

void Input(){
  cin >> N >> M >> K;
  X.resize(N);
  Y.resize(N);
  U.resize(M);
  V.resize(M);
  W.resize(M);
  A.resize(K);
  B.resize(K);
  rep(i,N){
    cin >> X[i] >> Y[i];
  }
  rep(i,M){
    cin >> U[i] >> V[i] >> W[i];
    U[i]--; V[i]--;
    sortedEdge.push_back(Edge(U[i], V[i], W[i], i));
    
  }
  rep(i,K){
    cin >> A[i] >> B[i];
  }
  sort(sortedEdge.begin(),sortedEdge.end(), [](Edge a, Edge b)-> bool{
    return a.c < b.c;
  });
  distanceNode.resize(K);
  rep(i,N) {
    vector<pi> tmp;
    rep(j,K) {
      ll p = CalcMinP(CalcDist(j, i));
      if(p <= 5000) {
        tmp.push_back({p, j});
        distanceNode[j].push_back({p, i});
      }
    }
    sort(tmp.begin(),tmp.end());
    distanceMap.push_back(tmp);
  }
  rep(i,K) {
    sort(distanceNode[i].begin(),distanceNode[i].end());
  }
}

struct Result{
  vl P;
  vi b;
  vi U;
  Result() {U.assign(N, 1);}

  ld Score(){
    //Sのみ
    ll S = 0;
    rep(i,N) S += P[i] * P[i];
    rep(i,M) S += (b[i] ? W[i] : 0);
    vi f(K, 0);
    ll cnt = 0;
    rep(i,N) {
      for(pi p: distanceMap[i]) {        
        if(p.first <= P[i] && f[p.second] == 0) {
          f[p.second] = 1;
          cnt++;
        }
      }
    }
    
    return (cnt < K ? round(1e+6 * (ld)(cnt+1) / K) : round(1e+6 * (1 + 1e+8/(S + 1e+7))));
  }

  void Output(){
    rep(i,N) cout << P[i] << " ";
    cout << "\n";
    rep(i,M) cout << b[i] << " ";
    cout << "\n";
  }
};

vi MST(const Result& res){
  UFT uf(N);
  vi usedEdge(M, 0);
  for(Edge e: sortedEdge) {
    if(res.U[e.f] && res.U[e.t]) {
      if(uf.same(e.f, e.t)) continue;
      uf.unite(e.f, e.t);
      usedEdge[e.id] = 1;
      if(uf.usize(0) == N) break;
    }
  }
  bool f = true;
  rep(i,N) {
    if(!uf.same(0, i) && res.U[i]) {
      f = false;
      break;
    }
  }
  if(!f) return vi(0);
  return usedEdge;
}

void Initialize(Result& res){
  vi usedEdge = MST(res);
  vl p(N, 1);
  rep(i,K) {
    auto [d, id] = distanceNode[i][0];
    if(p[id] >= d) continue;
    p[id] = d;
  }
  res.P = p;
  res.b = usedEdge;
}

void Modify(Result& res) {
  int id = randxor() % N;
  int diff = randxor() % 3000 - 1000;
  ll newPid = max(0LL, res.P[id] - diff); 
  vi oldU = res.U;
  if(res.P[id]*newPid > 0 || id == 0) {
    res.P[id] = newPid;
    return ;
  }

  if(res.P[id] == 0 && newPid > 0) {
    res.U[id] = 1;
  }
  if(res.P[id] > 0 && newPid == 0) {
    res.U[id] = 0;
  }
  res.P[id] = newPid;
  vi newEdge = MST(res);  
  if(sz(newEdge) == 0) res.U = oldU;
  else { res.b = newEdge;}
}

double TimeLimit = 1800;
double StartTemp = 3000;
double EndTemp = 1;
Result Anneling(){
  Result res;
  Initialize(res);
  auto startTime = std::chrono::system_clock::now();   
  ll cnt = 0;
  while(1) {
    auto nowTime = std::chrono::system_clock::now();   
    auto msec = std::chrono::duration_cast<std::chrono::milliseconds>(nowTime - startTime).count(); 
    if(msec > TimeLimit) break;
     rep(i,100) {
      cnt++;
      Result newResult = res;
      Modify(newResult);
      ll newScore = newResult.Score();
      ll oldScore = res.Score();

      double temp = StartTemp + (EndTemp - StartTemp) * msec / TimeLimit;
      double prob = exp((newScore-oldScore)/temp);

      if(prob > (double)(randxor()%inf)/inf) {
        res = newResult;
        //cout << newScore << "\n";
      }            
    }
    //res.Output();    
  }
  //cout << cnt << "\n";
  return res;
}

int main()
{
  Input();
  Result res = Anneling();
  res.Output();

  return 0;
}
