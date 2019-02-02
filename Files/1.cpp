#include <bits/stdc++.h>

#define rep(i , l , r) for(int i = (l) , ___ = (r) ; i <= ___ ; ++i)
#define per(i , r , l) for(int i = (r) , ___ = (l) ; i >= ___ ; --i)

#define DEBUG(___) std::cerr << #___ << ":  " << ___ << std::endl

const size_t SIZE = 1 << 21;

struct Input
{
    char Buf[SIZE], *iS, *iE;
    inline char operator()()
    {
        return iS == iE ? iE = Buf + fread(iS = Buf , 1, SIZE , stdin), iS == iE ? EOF : *iS++ : *iS++;
    }
} gc;

struct Output
{
    char Buf[SIZE], *iS, *iE;
    Output(){ iS = Buf , iE = Buf + SIZE - 1; }
    ~Output(){ flush(); }
    inline void flush()
    {
        fwrite (Buf , 1 , iS - Buf , stdout);
        iS = Buf;
    }
    inline void operator()(char c)
    {
        *iS++ = c;
        if(iS == iE) flush();
    }
} pc;

template<typename T>inline T read(T &f)
{
    f = 0 ; int x = 1 ; char c = gc();
    while(!isdigit(c))
        x = c == '-' ? -1 : 1 , c = gc();
    while(isdigit(c))
        (f *= 10) += c & 15 , c = gc();
    return f *= x;
}

template<typename T>inline void print(T x)
{
    static int f , qr , qu[55];
    if (x == 0) pc('0');
    if (x < 0) pc('-') , x = -x;
    while(x) qu[++qr] = x % 10 + '0' , x /= 10;
    while(qr) pc(qu[qr--]);
}

template<typename T>inline int chkmin(T &x , const T &y) { return x > y ? x = y , 1 : 0; }
template<typename T>inline int chkmax(T &x , const T &y) { return x < y ? x = y , 1 : 0; }

typedef long long LL;
typedef double db;

const int N = 400000 + 5;
const int KCZ = 998244353 , g = 3;

LL mp(LL x , LL y = KCZ - 2)
{
    LL res = 1;
    while(y)
    {
        if(y & 1) res = res * x % KCZ;
        x = x * x % KCZ;
        y >>= 1;
    }
    return res;
}

LL add(LL x , const LL &y) { x += y; if(x >= KCZ) x -= KCZ; return x; }
LL sub(LL x , const LL &y) { x -= y; if(x < 0) x += KCZ; return x; }

int rev[N];

void NTT(LL *A , int lim , int type)
{
    rep(i , 0 , lim - 1)
        if(i < rev[i]) std::swap(A[i] , A[rev[i]]);
    for(int mid = 1 ; mid < lim ; mid <<= 1)
    {
        LL Wn = mp(g , (KCZ - 1) / (mid << 1));
        for(int R = mid << 1 , j = 0 ; j < lim ; j += R)
        {
            LL *x = A + j , *y = x + mid , w = 1;
            for(int k = 0 ; k < mid ; ++k)
            {
                LL u = *x , v = w * *y % KCZ;
                *x = add(u , v);
                *y = sub(u , v);
                ++x , ++y , w = w * Wn % KCZ;
            }
        }
    }
    if(type == -1)
    {
        LL ginv = mp(lim);
        rep(i , 0 , lim - 1)
            A[i] = A[i] * ginv % KCZ;
        std::reverse(A + 1 , A + lim);
    }
}

int lim , l;

void MakeRev(int n)
{
    lim = 1 , l = 0;
    while(lim < n) lim <<= 1 , l++;
    rep(i , 1 , lim - 1)
        rev[i] = (rev[i >> 1] >> 1) | ((i & 1) << (l - 1));
}

void set(LL *A , int n)
{
    rep(i , n , lim - 1) A[i] = 0;
}

void copy(LL *A , const LL *B , int n)
{
    rep(i , 0 , n - 1) A[i] = B[i];
    set(A , n);
}

void PolyInv(const LL *A , LL *B , int n)
{
    static LL C[N] , D[N];
    if(n == 1)
    {
        B[0] = mp(A[0]);
        return ;
    }
    PolyInv(A , B , (n + 1) >> 1);
    MakeRev(n << 1);
    copy(C , A , n) , copy(D , B , n);
    NTT(C , lim , 1) , NTT(D , lim , 1);
    rep(i , 0 , lim - 1)
        D[i] = sub(2ll , C[i] * D[i] % KCZ) * D[i] % KCZ;
    NTT(D , lim ,-1);
    copy(B , D , n);
}

void deriv(const LL *A , LL *B , int n)
{
    rep(i , 1 , n - 1)
        B[i - 1] = A[i] * i % KCZ;
    B[n - 1] = 0;
}

void inter(const LL *A , LL *B , int n)
{
    rep(i , 1 , n - 1)
        B[i] = A[i - 1] * mp(i) % KCZ;
    B[0] = 0;
}

// remember -> set0
void PolyLn(const LL *A , LL *B , int n)
{
    static LL C[N] , D[N];
    deriv(A , C , n) , PolyInv(A , D , n);
    MakeRev(n << 1);
    set(B , n) , set(C , n) , set(D , n);
    NTT(C , lim , 1) , NTT(D , lim , 1);
    rep(i , 0 , lim - 1)
        C[i] = C[i] * D[i] % KCZ;
    NTT(C , lim ,-1) , inter(C , B , n);
}

void PolySqrt(const LL *A , LL *B , int n)
{
    static LL C[N] , D[N] , inv2 = mp(2);
    if(n == 1)
    {
        B[0] = 1;
        return ;
    }
    PolySqrt(A , B , (n + 1) >> 1);
    PolyInv(B , D , n) , copy(C , A , n);
    MakeRev(n << 1);
    NTT(C , lim , 1) , NTT(B , lim , 1) , NTT(D , lim , 1);
    rep(i , 0 , lim - 1)
        C[i] = (C[i] + B[i] * B[i] % KCZ) % KCZ * inv2 % KCZ * D[i] % KCZ;
    NTT(C , lim ,-1) , copy(B , C , n);
}

void print(const LL *A , int n)
{
    rep(i , 0 , n - 1) print(A[i]) , pc(' ');
    pc('\n');
}

// remember -> last half -> copy
void PolyExp(const LL *A , LL *B , int n)
{
    static LL C[N] , D[N] , lnD[N];
    if(n == 1)
    {
        B[0] = 1;
        return ;
    }
    PolyExp(A , B , (n + 1) >> 1);
    PolyLn(B , lnD , n) , MakeRev(n);
    copy(C , A , n) , copy(D , B , n);
    rep(i , 0 , n - 1)
        C[i] = sub(C[i] , lnD[i]);
    set(C , n) , C[0] += 1;
    NTT(C , lim , 1) , NTT(D , lim , 1);
    rep(i , 0 , lim - 1)
        C[i] = C[i] * D[i] % KCZ;
    NTT(C , lim ,-1);
    rep(i , (n + 1) >> 1 , n) B[i] = C[i];
}

void PolyPow(const LL *A , LL *B , int n , LL d)
{
    static LL C[N];
    PolyLn(A , C , n);
    rep(i , 0 , n - 1)
        C[i] = C[i] * d % KCZ;
    PolyExp(C , B , n);
}

// remember F -> set0 > d
void PolyDiv(const LL *A , const LL *B , LL *C , LL *D , int n , int m)
{
    static LL F[N] , G[N] , GR[N];
    rep(i , 0 , n - 1) F[i] = A[n - 1 - i];
    rep(i , 0 , m - 1) G[i] = B[m - 1 - i];
    int d = n - m + 1;
    PolyInv(G , GR , d);
    MakeRev(n << 1);
    set(F , n) , set(G , m) , set(GR , d);
    NTT(F , lim , 1) , NTT(GR , lim , 1);
    rep(i , 0 , lim - 1)
        F[i] = F[i] * GR[i] % KCZ;
    NTT(F , lim ,-1);
    std::reverse(F , F + d);
    set(F , d) , copy(C , F , d);
    copy(G , B , m);
    NTT(F , lim , 1) , NTT(G , lim , 1);
    rep(i , 0 , lim - 1)
        F[i] = F[i] * G[i] % KCZ;
    NTT(F , lim ,-1);
    rep(i , 0 , m - 1) D[i] = sub(A[i] , F[i]);
}

int n , m ; LL A[N] , B[N] , C[N] , D[N];

int main()
{
    read(n) , read(m) , n += 1 , m += 1;
    rep(i , 0 , n - 1) read(A[i]);
    rep(i , 0 , m - 1) read(B[i]);
    PolyDiv(A , B , C , D , n , m);
    rep(i , 0 , n - m) print(C[i]) , pc(' ');
    pc('\n');
    rep(i , 0 , m - 2) print(D[i]) , pc(' ');
    return 0;
}
