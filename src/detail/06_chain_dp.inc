// 受限候选上的链式动态规划。把圆环切成有边界的候选链，以相邻选点代价求增加或删除方案。
// Included in fixed order by solution.cpp.

#define ZVW 8
#define ZVWR 16
#define ZWR 6
#define ZCLS_C 256
#define ZW0C 4
#define ZRCLS 64
#define ZWHL 12
#define ZFUSEW 6
#define ZNC3 4
#define ZC_HUGE 100000
#define ZW_HUGE 2
#define ZVWH 4
#define ZP0 16
#define ZP1 4
#define ZP2 1
#define ZREMK 8
#define ZW_SMALL 16
#define ZW_MID 5
#define ZW_BIG 3
#define ZC_MID 128
#define ZC_BIG 512
#define ZDENSE 6
#define ZTXK 64
#define ZQK 16
#define VC_ZK 0
#define VC_ZKLO 8
#define VC_ZKHI 32
ll vcCbar16 = 0;
#define VC_ZB2_W -1
#define VC_ZB2_LO 8
#define VC_ZB2_HI 10
#define VC_ZB2_M 3
#define VC_ZB2_T 3
namespace placement_dp {
const ll INF = 4000000000000000000LL;
const ll BIGV = 1LL << 60;
const ll BIGH = 1LL << 59;
SP2_I ll multiplyNonnegative(ll a, ll b) {
    if (a < b) {
        ll t = a;
        a = b;
        b = t;
    }
    ll r = 0;
    while (b) {
        r += a & -(b & 1);
        a <<= 1;
        b >>= 1;
    }
    return r;
}
SP2_I ll divideNonnegative(ll a, ll b) {
    if (b <= 0 || a < b)
        return 0;
    {
        int sh = __builtin_clzll(b) - __builtin_clzll(a);
        ll q = 0;
        for (; sh >= 0; sh--) {
            const ll t = b << sh;
            const ll m = -(ll)(t <= a);
            a -= t & m;
            q |= m & (1LL << sh);
        }
        return q;
    }
    int sh = 0;
    while (sh < 62 && (b << (sh + 1)) <= a && (b << (sh + 1)) > 0)
        sh++;
    ll q = 0;
    for (; sh >= 0; sh--) {
        if ((b << sh) <= a) {
            a -= (b << sh);
            q |= (1LL << sh);
        }
    }
    return q;
}
SP2_I ll absl(ll x) {
    return x < 0 ? -x : x;
}
SP2_I int pc64(ull x) {
    return __builtin_popcountll(x);
}
SP2_I int ctz64(ull x) {
    return __builtin_ctzll(x);
}
SP2_I int clz64(ull x) {
    return __builtin_clzll(x);
}
int zE = 0;
int zS = 0;
int zDone = 0;
void zFill(int p);
void zFree(int p);
void zFreeBatch(int t, int s);
SP2_I int nextNWv(int p) {
    if (p >= N)
        return -1;
    int w = p >> 6;
    ull x = vb[w] & (~0ULL << (p & 63));
    while (!x) {
        w++;
        if (w >= NW)
            return -1;
        x = vb[w];
    }
    return (w << 6) + ctz64(x);
}
SP2_I int prevNWv(int p) {
    if (p < 0)
        return -1;
    int w = p >> 6;
    int sh = 63 - (p & 63);
    ull x = (vb[w] << sh) >> sh;
    while (!x) {
        w--;
        if (w < 0)
            return -1;
        x = vb[w];
    }
    return (w << 6) + 63 - clz64(x);
}
SP2_I int nextU(int q) {
    int off = 0;
    while (q >= N) {
        q -= N;
        off += N;
    }
    while (q < 0) {
        q += N;
        off -= N;
    }
    int r = nextNWv(q);
    if (r >= 0)
        return r + off;
    r = nextNWv(0);
    if (r < 0)
        return 1 << 29;
    return r + off + N;
}
SP2_I int prevU(int q) {
    int off = 0;
    while (q >= N) {
        q -= N;
        off += N;
    }
    while (q < 0) {
        q += N;
        off -= N;
    }
    int r = prevNWv(q);
    if (r >= 0)
        return r + off;
    r = prevNWv(N - 1);
    if (r < 0)
        return -(1 << 29);
    return r + off - N;
}
int cntRange(int l, int r) {
    if (l > r)
        return 0;
    int wl = l >> 6, wr = r >> 6;
    int sh = 63 - (r & 63);
    if (wl == wr)
        return pc64(((vb[wl] & (~0ULL << (l & 63))) << sh) >> sh);
    int c = pc64(vb[wl] & (~0ULL << (l & 63)));
    for (int w = wl + 1; w < wr; w++)
        c += pc64(vb[w]);
    c += pc64((vb[wr] << sh) >> sh);
    return c;
}
int cntRangeU(int l, int r) {
    if (l > r)
        return 0;
    if (r < N)
        return cntRange(l, r);
    if (l >= N)
        return cntRange(l - N, r - N);
    return cntRange(l, N - 1) + cntRange(0, r - N);
}
ll kap(ll s) {
    if (s <= 1 || s >= N)
        return 0;
    return divideNonnegative(s << 40, multiplyNonnegative(s - 1, N - s));
}
ll S1, E1, CX, C0, THR0, THRX, CXS1, CNS;
bool remMode = false;
ll RH0[MAXN + 8], TXT[MAXN + 8], RHX[MAXN + 8];
ll LINT[MAXN + 8];
int cyBP = 0;
ll cyBV = 0;
bool cyBOK = false;
int L0 = 0, LTX = 0, LHX = 0;
int LTXM = 0;
__attribute__((noinline)) void txGrow(ll d) {
    ll nl = (ll)LTX << 1;
    if (nl < SP_LTX)
        nl = SP_LTX;
    if (nl <= d)
        nl = d + 1;
    if (nl > LTXM)
        nl = LTXM;
    ll w = multiplyNonnegative(CXS1, LTX), v = w - CNS;
    for (int k = LTX; k < nl; k++) {
        TXT[k] = v < 0 ? -v : v;
        LINT[k] = w;
        v += CXS1;
        w += CXS1;
    }
    LTX = (int)nl;
}
SP2_I ll rh0(ll g) {
    return RH0[(ull)g < (ull)L0 ? g : L0];
}
SP2_I ll tx(ll d) {
    if (d < LTX)
        return TXT[d];
    if (SP_LTX && d < LTXM) {
        txGrow(d);
        return TXT[d];
    }
    return multiplyNonnegative(CX, absl(multiplyNonnegative(S1, d) - N));
}
SP2_I ll rhx(ll g) {
    return g < LHX ? RHX[g] : 0;
}
void setWeights(ll s1, ll e1) {
    S1 = s1;
    E1 = e1;
    CX = kap(s1);
    C0 = kap(e1);
    while (CX >= (1LL << 16) || C0 >= (1LL << 16)) {
        CX >>= 1;
        C0 >>= 1;
    }
    {
        ll vw = ZVW;
        ll fe = (ll)zE << 3;
        if (fe < N)
            vw = ZVWH;
        else if (fe > multiplyNonnegative(N, 5))
            vw = ZVWL;
        {
            ll e16 = (ll)zE << 4;
            if (VC_ZB_W >= 0 && (VC_ZB_M & (remMode ? 2 : 1)) && (VC_ZB_T & (N > NM ? 2 : 1)) &&
                e16 >= multiplyNonnegative(N, VC_ZB_LO) && e16 < multiplyNonnegative(N, VC_ZB_HI))
                vw = VC_ZB_W;
            if (VC_ZB2_W >= 0 && (VC_ZB2_M & (remMode ? 2 : 1)) && (VC_ZB2_T & (N > NM ? 2 : 1)) &&
                e16 >= multiplyNonnegative(N, VC_ZB2_LO) && e16 < multiplyNonnegative(N, VC_ZB2_HI))
                vw = VC_ZB2_W;
        }
        if (BOP_ZVWM >= 0 && !remMode && N > 1000 && N <= NM)
            vw = BOP_ZVWM;
#define BOP_ZVWN -1
        if (BOP_ZVWN >= 0 && !remMode && zS == 0 && N > NM)
            vw = BOP_ZVWN;
        if (remMode)
            vw = multiplyNonnegative(vw, ZVWR) >> 4;
        if (VC_ZK > 0 && vcCbar16 > 0) {
            ll k16 = divideNonnegative((ll)zE << 9, multiplyNonnegative(vcCbar16, VC_ZK));
            if (k16 < VC_ZKLO)
                k16 = VC_ZKLO;
            if (k16 > VC_ZKHI)
                k16 = VC_ZKHI;
            vw = multiplyNonnegative(vw, k16) >> 4;
        }
        C0 = multiplyNonnegative(C0, vw) >> 4;
    }
    if (SDY_ZX && smT) {
        int f = SDY_ZXB + (int)(multiplyNonnegative(sdyLive(), SDY_ZXM) >> 4);
        if (f < SDY_ZXLO)
            f = SDY_ZXLO;
        if (f > SDY_ZXHI)
            f = SDY_ZXHI;
        if (f != 16)
            CX = multiplyNonnegative(CX, f) >> 4;
        if (CX < 1)
            CX = 1;
    }
    CXS1 = multiplyNonnegative(CX, s1);
    CNS = multiplyNonnegative(CX, N);
    THR0 = e1 > 0 ? divideNonnegative(N + e1 - 1, e1) : 0;
    THRX = s1 > 0 ? divideNonnegative(N + s1 - 1, s1) : 0;
    L0 = (int)(C0 > 0 ? THR0 : 0);
    ll v = multiplyNonnegative(C0, (ll)N << 1), dec = multiplyNonnegative(C0, e1 << 1);
    for (int g = 0; g < L0; g++) {
        RH0[g] = v;
        v -= dec;
    }
    RH0[L0] = 0;
    LTX = 0;
    LHX = 0;
    LTXM = 0;
    cyBOK = false;
}
void buildTX(ll lim) {
    if (lim > N + 1)
        lim = N + 1;
    if (SP_LTX) {
        LTXM = (int)lim;
        return;
    }
    ll v = -multiplyNonnegative(CX, N), inc = multiplyNonnegative(CX, S1), w = 0;
    for (int d = 0; d < lim; d++) {
        TXT[d] = v < 0 ? -v : v;
        LINT[d] = w;
        v += inc;
        w += inc;
    }
    LTX = (int)lim;
}
SP2_I ll linX(ll g) {
    if (g < LTX)
        return LINT[g];
    if (SP_LTX && g < LTXM) {
        txGrow(g);
        return LINT[g];
    }
    return multiplyNonnegative(CXS1, g);
}
SP2_I ll cyAt(int p) {
    ll v = (cyBOK && p >= cyBP)
               ? cyBV + linX(p - cyBP)
               : (p >= 0 ? multiplyNonnegative(CXS1, p) : -multiplyNonnegative(CXS1, -p));
    cyBP = p;
    cyBV = v;
    cyBOK = true;
    return v;
}
void buildHX() {
    ll lim = CX > 0 ? THRX : 0;
    ll v = multiplyNonnegative(CX, (ll)N << 1), dec = multiplyNonnegative(CX, S1 << 1);
    for (int g = 0; g < lim; g++) {
        RHX[g] = v;
        v -= dec;
    }
    LHX = (int)lim;
}
SP2_I ll nodeCost(ll a, ll b) {
    return rh0(a + b) - rh0(a) - rh0(b);
}
RVEC(int) CP, CA, CB, NS, PAR, CH;
RVEC(ll) CN, F, CY;
int nc = 0, nn = 0;
SP2_I void ensureCand(int need) {
    if ((int)CP.size() < need) {
        CP.resize(need);
        CA.resize(need);
        CB.resize(need);
        CN.resize(need);
        F.resize(need);
        PAR.resize(need);
        CY.resize(need);
    }
}
SP2_I void ensureNodes(int need) {
    if ((int)NS.size() < need + 1)
        NS.resize(need + 1);
    if ((int)CH.size() < need + 1)
        CH.resize(need + 1);
}
RVEC(ull) V3;
int NW3 = 0;
void buildV3() {
    NW3 = (int)(((ll)N + N + N + 63) >> 6);
    if ((int)V3.size() < NW3 + 1)
        V3.resize(NW3 + 1);
    for (int w = 0; w <= NW3; w++)
        V3[w] = 0;
    int off = 0;
    for (int rep = 0; rep < 3; rep++, off += N) {
        int wo = off >> 6, sh = off & 63;
        for (int w = 0; w < NW; w++) {
            ull x = vb[w];
            if (!x)
                continue;
            V3[wo + w] |= x << sh;
            if (sh)
                V3[wo + w + 1] |= x >> (64 - sh);
        }
    }
}
SP2_I int next3(int p) {
    int i = p + N;
    if (i < 0)
        i = 0;
    int w = i >> 6;
    if (w >= NW3)
        return 1 << 29;
    ull x = V3[w] & (~0ULL << (i & 63));
    while (!x) {
        w++;
        if (w >= NW3)
            return 1 << 29;
        x = V3[w];
    }
    int r = (w << 6) + ctz64(x) - N;
    return r < N + N ? r : (1 << 29);
}
SP2_I int prev3(int p) {
    int i = p + N;
    if (i < 0)
        return -(1 << 29);
    int w = i >> 6;
    if (w >= NW3) {
        w = NW3 - 1;
        i = (w << 6) + 63;
    }
    int sh = 63 - (i & 63);
    ull x = (V3[w] << sh) >> sh;
    while (!x) {
        w--;
        if (w < 0)
            return -(1 << 29);
        x = V3[w];
    }
    return (w << 6) + 63 - clz64(x) - N;
}
int Lb[80], Rb[80], Mb[170];
int collect(int tgt, int lo, int hi, int W) {
    if (tgt <= lo)
        tgt = lo + 1;
    if (tgt >= hi)
        tgt = hi - 1;
    int nl = 0, nr = 0;
    int lb = tgt - N, rb = tgt + N;
    if (lb < -N)
        lb = -N;
    {
        int i = tgt + N;
        int w = i >> 6;
        ull x = w < NW3 ? (V3[w] & (~0ULL << (i & 63))) : 0;
        while (nr <= W) {
            while (!x) {
                w++;
                if (w >= NW3)
                    break;
                x = V3[w];
            }
            if (!x)
                break;
            int r = (w << 6) + ctz64(x) - N;
            if (r >= rb)
                break;
            Rb[nr++] = r;
            x &= x - 1;
        }
    }
    {
        int i = tgt - 1 + N;
        if (i >= 0) {
            int w = i >> 6;
            int sh = 63 - (i & 63);
            ull x = (V3[w] << sh) >> sh;
            while (nl <= W) {
                while (!x) {
                    w--;
                    if (w < 0)
                        break;
                    x = V3[w];
                }
                if (!x)
                    break;
                int bit = 63 - clz64(x);
                int r = (w << 6) + bit - N;
                if (r <= lb)
                    break;
                Lb[nl++] = r;
                x &= ~(1ULL << bit);
            }
        }
    }
    int len = 0;
    for (int i = nl - 1; i >= 0; i--)
        Mb[len++] = Lb[i];
    for (int i = 0; i < nr; i++)
        Mb[len++] = Rb[i];
    int i = nl - 1, j = nl, taken = 0;
    int lo_i = nl, hi_i = nl - 1;
    while (taken < W) {
        bool okL = i >= 0 && Mb[i] > lo;
        bool okR = j < len && Mb[j] < hi;
        if (!okL && !okR)
            break;
        if (okL && (!okR || tgt - Mb[i] < Mb[j] - tgt)) {
            lo_i = i;
            i--;
        } else {
            hi_i = j;
            j++;
        }
        taken++;
    }
    if (taken == 0)
        return 0;
    ll cy = 0;
    int lastp = 0;
    bool first = true;
    for (int k = lo_i; k <= hi_i; k++) {
        ll a, b;
        int pk = Mb[k];
        if (k > 0)
            a = pk - Mb[k - 1];
        else {
            int r = prev3(pk - 1);
            a = r > -(1 << 28) ? pk - r : N;
        }
        if (k + 1 < len)
            b = Mb[k + 1] - pk;
        else {
            int r = next3(pk + 1);
            b = r < (1 << 28) ? r - pk : N;
        }
        if (a > N)
            a = N;
        if (b > N)
            b = N;
        CP[nc] = pk;
        CA[nc] = (int)a;
        CB[nc] = (int)b;
        CN[nc] = nodeCost(a, b);
        if (first) {
            cy = cyAt(pk);
            first = false;
        } else
            cy += linX(pk - lastp);
        CY[nc] = cy;
        lastp = pk;
        nc++;
    }
    return taken;
}
SP2_I ull classWord(int w, int cls) {
    ull x = V3[w];
    ull lo = w > 0 ? V3[w - 1] : 0, hi = w + 1 < NW3 ? V3[w + 1] : 0;
    ull l1 = (x << 1) | (lo >> 63), r1 = (x >> 1) | (hi << 63);
    if (cls == 0)
        return x & l1 & r1;
    if (cls == 1)
        return x & (l1 | r1);
    ull l2 = (x << 2) | (lo >> 62), r2 = (x >> 2) | (hi << 62);
    if (cls == 2)
        return x & (l1 | l2) & (r1 | r2);
    return x & (l1 | l2 | r1 | r2);
}
SP2_I int nextClass(int p, int lim, int cls) {
    int i = p + N;
    if (i < 0)
        i = 0;
    int w = i >> 6, wl = (lim + N - 1) >> 6;
    if (w >= NW3)
        return 1 << 29;
    ull x = classWord(w, cls) & (~0ULL << (i & 63));
    while (!x) {
        w++;
        if (w > wl || w >= NW3)
            return 1 << 29;
        x = classWord(w, cls);
    }
    int r = (w << 6) + ctz64(x) - N;
    return r < lim ? r : (1 << 29);
}
SP2_I int prevClass(int p, int lim, int cls) {
    int i = p + N;
    if (i < 0)
        return -(1 << 29);
    int w = i >> 6, wl = (lim + N + 1) >> 6;
    if (w >= NW3)
        return -(1 << 29);
    int sh = 63 - (i & 63);
    ull x = (classWord(w, cls) << sh) >> sh;
    while (!x) {
        w--;
        if (w < wl || w < 0)
            return -(1 << 29);
        x = classWord(w, cls);
    }
    int r = (w << 6) + 63 - clz64(x) - N;
    return r > lim ? r : -(1 << 29);
}
int NCLS = 0, W0C = 6, RCLS = 64;
int Sb[64];
#define XLS_CSL 0
template <bool LIGHT> int collectST(int tgt, int lo, int hi) {
    if (tgt <= lo)
        tgt = lo + 1;
    if (tgt >= hi)
        tgt = hi - 1;
    int ns = 0;
    {
        int nr = 0, nl = 0;
        int i = tgt + N, w = i >> 6;
        ull x = w < NW3 ? (V3[w] & (~0ULL << (i & 63))) : 0;
        while (nr < W0C) {
            while (!x) {
                w++;
                if (w >= NW3)
                    break;
                x = V3[w];
            }
            if (!x)
                break;
            int r = (w << 6) + ctz64(x) - N;
            if (r >= hi)
                break;
            Rb[nr++] = r;
            x &= x - 1;
        }
        i = tgt - 1 + N;
        if (i >= 0) {
            w = i >> 6;
            int sh = 63 - (i & 63);
            x = (V3[w] << sh) >> sh;
            while (nl < W0C) {
                while (!x) {
                    w--;
                    if (w < 0)
                        break;
                    x = V3[w];
                }
                if (!x)
                    break;
                int bit = 63 - clz64(x);
                int r = (w << 6) + bit - N;
                if (r <= lo)
                    break;
                Lb[nl++] = r;
                x &= ~(1ULL << bit);
            }
        }
        int a = 0, b = 0;
        while (ns < W0C && (a < nl || b < nr)) {
            if (b >= nr || (a < nl && tgt - Lb[a] < Rb[b] - tgt))
                Sb[ns++] = Lb[a++];
            else
                Sb[ns++] = Rb[b++];
        }
    }
    int rlo = tgt - RCLS, rhi = tgt + RCLS;
    if (rlo < lo)
        rlo = lo;
    if (rhi > hi)
        rhi = hi;
    for (int cl = 0; cl < NCLS; cl++) {
        int r = nextClass(tgt, rhi, cl);
        if (r < (1 << 28))
            Sb[ns++] = r;
        r = prevClass(tgt - 1, rlo, cl);
        if (r > -(1 << 28))
            Sb[ns++] = r;
    }
    if (ns == 0)
        return 0;
    int m = 0;
    {
        int bw = tgt - 64;
        ull m0 = 0, m1 = 0;
        bool outside = false;
        for (int i2 = 0; i2 < ns; i2++) {
            int o = Sb[i2] - bw;
            outside |= (unsigned)o >= 128u;
            ull bit = 1ULL << (o & 63);
            m0 |= o < 64 ? bit : 0;
            m1 |= o >= 64 ? bit : 0;
        }
        if (!outside) {
            while (m0) {
                Sb[m++] = bw + ctz64(m0);
                m0 &= m0 - 1;
            }
            while (m1) {
                Sb[m++] = bw + 64 + ctz64(m1);
                m1 &= m1 - 1;
            }
        } else {
            for (int i2 = 1; i2 < ns; i2++) {
                int v = Sb[i2], j2 = i2 - 1;
                while (j2 >= 0 && Sb[j2] > v) {
                    Sb[j2 + 1] = Sb[j2];
                    j2--;
                }
                Sb[j2 + 1] = v;
            }
            for (int i2 = 0; i2 < ns; i2++)
                if (m == 0 || Sb[i2] != Sb[m - 1])
                    Sb[m++] = Sb[i2];
        }
    }
    ll cy = 0;
    int lastp = 0;
    for (int k = 0; k < m; k++) {
        int pk = Sb[k];
        int pr = prev3(pk - 1), nx = next3(pk + 1);
        ll a = pr > -(1 << 28) ? pk - pr : N, b = nx < (1 << 28) ? nx - pk : N;
        if (a > N)
            a = N;
        if (b > N)
            b = N;
        CP[nc] = pk;
        CN[nc] = nodeCost(a, b);
        if (!LIGHT) {
            CA[nc] = (int)a;
            CB[nc] = (int)b;
            if (k == 0)
                cy = cyAt(pk);
            else
                cy += linX(pk - lastp);
            CY[nc] = cy;
            lastp = pk;
        }
        nc++;
    }
    return m;
}
SP2_I int collectS(int tgt, int lo, int hi) {
    return collectST<false>(tgt, lo, hi);
}
int ext[(MAXN << 1) + 128];
int extE = 0;
void materializeRing() {
    int E = zE;
    extE = E;
    int k = 1;
    for (int w = 0; w < NW; w++) {
        ull x = vb[w];
        while (x) {
            ext[k++] = (w << 6) + ctz64(x);
            x &= x - 1;
        }
    }
    for (int i = 1; i <= E; i++)
        ext[i + E] = ext[i] + N;
    ext[0] = ext[E] - N;
    ext[(E << 1) + 1] = ext[1] + N + N;
}
SP2_I int extFirstAbove(int p) {
    int lo = 1, hi = (extE << 1) + 1;
    while (lo < hi) {
        int m = (lo + hi) >> 1;
        if (ext[m] > p)
            hi = m;
        else
            lo = m + 1;
    }
    return lo;
}
// 按目标间隔构造链 DP 的候选层，并裁剪到受控窗口。
void buildTargets(int k, int S, int slotType, int W, bool dense, int gs, int ge) {
    ensureCand(nc + multiplyNonnegative(k, W + 16) + 8);
    ensureNodes(k);
    ll g = slotType - S;
    ll q = divideNonnegative(g, k + 1), r = g - multiplyNonnegative(q, k + 1);
    ll acc = (k + 1) >> 1;
    ll pos = S;
    int ptr = gs, h = W >> 1;
    int m = ge - gs;
#define BOP_TBN 5000
#define BOP_TBK 2
    const bool tbOn = BOP_TB > 0 && dense && N >= BOP_TBN && k >= BOP_TBK;
    int tbR = gs;
    ll tbA = (k + 1) >> 1;
    ll tbQ = 0, tbRr = 0;
    if (tbOn) {
        tbQ = divideNonnegative(m, k + 1);
        tbRr = m - multiplyNonnegative(tbQ, k + 1);
    }
    for (int j = 0; j < k; j++) {
        pos += q;
        acc += r;
        if (acc >= k + 1) {
            acc -= k + 1;
            pos++;
        }
        NS[j] = nc;
        if (dense) {
            while (ptr < ge && ext[ptr] < pos)
                ptr++;
            int ctr = ptr;
            if (tbOn) {
                tbR += (int)tbQ;
                tbA += tbRr;
                if (tbA >= k + 1) {
                    tbA -= k + 1;
                    tbR++;
                }
                ll dd = multiplyNonnegative(tbR > ptr ? tbR - ptr : ptr - tbR, BOP_TB) >> 4;
                ctr = tbR > ptr ? ptr + (int)dd : ptr - (int)dd;
            }
            int lo = ctr - h, hi = lo + W - 1;
            int flo = gs + j, fhi = gs + m - k + j;
            if (lo < flo)
                lo = flo;
            if (hi > fhi)
                hi = fhi;
            if (lo > hi) {
                if (ptr - h > fhi) {
                    hi = fhi;
                    lo = hi - W + 1;
                    if (lo < flo)
                        lo = flo;
                } else {
                    lo = flo;
                    hi = lo + W - 1;
                    if (hi > fhi)
                        hi = fhi;
                }
            }
            ll cy = cyAt(ext[lo]);
            for (int i = lo; i <= hi; i++) {
                ll a = ext[i] - ext[i - 1], b = ext[i + 1] - ext[i];
                if (a > N)
                    a = N;
                if (b > N)
                    b = N;
                if (i > lo)
                    cy += linX(ext[i] - ext[i - 1]);
                CP[nc] = ext[i];
                CA[nc] = (int)a;
                CB[nc] = (int)b;
                CN[nc] = nodeCost(a, b);
                CY[nc] = cy;
                nc++;
            }
        } else if (NCLS > 0) {
            collectS((int)pos, S, slotType);
        } else {
            collect((int)pos, S, slotType, W);
        }
    }
    NS[k] = nc;
}
SP2_I ll pairCost(int v, int u) {
    ll m = CB[v];
    return rh0(m) + rh0(CA[v] + m + CB[u]) - rh0(CA[v] + m) - rh0(m + CB[u]);
}
#define ZW_T 32
#define ZC_T 32
#define ZW_M2 8
#define ZC_M2 256
int DQW[256];
// 固定候选窗口上的链式转移；相邻候选之间只需增加一个间隔代价。
ll chainW(int k, int S, int slotType) {
    ll YS = cyAt(S), YT = cyAt(slotType);
    if (k == 0)
        return absl(YT - YS - CNS);
    for (int j = 0; j < k; j++)
        if (NS[j + 1] == NS[j])
            return INF;
    for (int u = NS[0]; u < NS[1]; u++) {
        F[u] = (CP[u] > S && CP[u] < slotType) ? absl(CY[u] - YS - CNS) + CN[u] : BIGV;
        PAR[u] = -1;
    }
    for (int j = 1; j < k; j++) {
        int v0 = NS[j - 1], v1 = NS[j];
        int ia = v0, hi = v0, ibp = v0, head = 0, tail = 0;
        ll bestA = BIGV;
        int bestAi = -1;
        for (int u = NS[j]; u < NS[j + 1]; u++) {
            int pu = CP[u];
            ll yu = CY[u] - CNS;
            while (ibp < v1 && CP[ibp] < pu)
                ibp++;
            int ib2 = ibp;
            bool adj = false;
            if (ibp > v0 && CP[ibp - 1] == pu - CA[u]) {
                adj = true;
                ib2 = ibp - 1;
            }
            while (ia < ib2 && CY[ia] <= yu) {
                ll val = F[ia] - CY[ia];
                if (val < bestA) {
                    bestA = val;
                    bestAi = ia;
                }
                ia++;
            }
            while (hi < ib2) {
                ll val = F[hi] + CY[hi];
                while (tail > head && F[DQW[tail - 1]] + CY[DQW[tail - 1]] >= val)
                    tail--;
                DQW[tail++] = hi;
                hi++;
            }
            while (head < tail && DQW[head] < ia)
                head++;
            ll best = BIGV;
            int arg = -1;
            if (bestAi >= 0) {
                best = bestA + yu;
                arg = bestAi;
            }
            if (head < tail) {
                int v = DQW[head];
                ll val = F[v] + CY[v] - yu;
                if (val < best) {
                    best = val;
                    arg = v;
                }
            }
            if (adj) {
                int v = ibp - 1;
                ll val = F[v] + absl(CY[u] - CY[v] - CNS) + pairCost(v, u);
                if (val < best) {
                    best = val;
                    arg = v;
                }
            }
            F[u] = (arg >= 0 && pu < slotType) ? best + CN[u] : BIGV;
            PAR[u] = arg;
        }
    }
    ll best = INF;
    int bu = -1;
    for (int u = NS[k - 1]; u < NS[k]; u++) {
        if (F[u] >= BIGH)
            continue;
        ll val = F[u] + absl(YT - CY[u] - CNS);
        if (val < best) {
            best = val;
            bu = u;
        }
    }
    if (bu < 0)
        return INF;
    int u = bu;
    for (int j = k - 1; j >= 0; j--) {
        CH[j] = u;
        u = PAR[u];
    }
    return best;
}
int zWHL = ZWHL, zP0 = ZP0, zP1 = ZP1, zWS = ZW_SMALL, zWM2 = ZW_M2, zWR = ZWR;
int zWM2u[3] = {ZW_M2, ZW_M2, ZW_M2}, zWMu[3] = {ZW_MID, ZW_MID, ZW_MID},
    zWBu[3] = {ZW_BIG, ZW_BIG, ZW_BIG};
int winForU(int c, int u) {
    int w = c <= ZC_T     ? ZW_T
            : c <= ZC_MID ? zWS
            : c <= ZC_M2  ? zWM2u[u]
                          : (c <= ZC_BIG ? zWMu[u] : (c <= ZC_HUGE ? zWBu[u] : ZW_HUGE));
    return w > 64 ? 64 : w;
}
RVEC(int) posX;
int chA[MAXN + 16], bestA[MAXN + 16];
int nCh = 0, nBest = 0;
void fillAllEmpty(int t) {
    (void)t;
    int p = nextNWv(0);
    while (p >= 0) {
        int nx = nextNWv(p + 1);
        zFill(p);
        p = nx;
    }
}
void fillRest(int t, int want) {
    (void)t;
    int have = zDone;
    if (have >= want)
        return;
    int E = 0;
    for (int w = 0; w < NW; w++)
        E += pc64(vb[w]);
    int need = want - have;
    if (need > E)
        need = E;
    int acc = E >> 1, placed = 0;
    int p = nextNWv(0);
    while (p >= 0 && placed < need) {
        int nx = nextNWv(p + 1);
        acc += need;
        if (acc >= E) {
            acc -= E;
            zFill(p);
            placed++;
        }
        p = nx;
    }
    p = nextNWv(0);
    while (p >= 0 && placed < need) {
        int nx = nextNWv(p + 1);
        zFill(p);
        placed++;
        p = nx;
    }
}
int zWant = 0;
SP2_I void applyList(int t, bool fromBest) {
    (void)t;
    int n = fromBest ? nBest : nCh;
    for (int ii = 0; ii < n; ii++) {
        int p = fromBest ? bestA[ii] : chA[ii];
        if (zDone >= zWant)
            break;
        int r = p;
        while (r >= N)
            r -= N;
        while (r < 0)
            r += N;
        if ((vb[r >> 6] >> (r & 63)) & 1ULL)
            zFill(r);
    }
}
unsigned char PB[(MAXN << 6) + 128];
int LOJ[MAXN + 8];
SP2_I ll pcIdx(int v) {
    ll a = ext[v] - ext[v - 1], m = ext[v + 1] - ext[v], b = ext[v + 2] - ext[v + 1];
    return rh0(m) + rh0(a + m + b) - rh0(a + m) - rh0(m + b);
}
SP2_I ll txc(ll d) {
    d = d < 0 ? 0 : d;
    return d < LTX ? TXT[d] : tx(d);
}
#define VC_DCK 0
#define VC_FUSE8 0
template <int WW> ll denseChainK(int k, int S, int slotType, int Wr, int gs, int ge) {
    const int W = WW > 0 ? WW : Wr;
    int m = ge - gs;
    ll FB[2][72];
    int PQ[2][72];
    int cur = 0;
    for (int o = 0; o < W; o++) {
        FB[0][o] = 0;
        PQ[0][o] = 0;
        FB[1][o] = 0;
        PQ[1][o] = 0;
    }
    ll g = slotType - S;
    ll q = divideNonnegative(g, k + 1), r = g - multiplyNonnegative(q, k + 1);
    ll acc = (k + 1) >> 1;
    ll pos = S;
    int ptr = gs, h = W >> 1;
    int lop = 0, cntp = 0, base = 0;
    for (int j = 0; j < k; j++) {
        pos += q;
        acc += r;
        if (acc >= k + 1) {
            acc -= k + 1;
            pos++;
        }
        ptr += (ptr < ge && ext[ptr] < pos);
        ptr += (ptr < ge && ext[ptr] < pos);
        while (ptr < ge && ext[ptr] < pos)
            ptr++;
        int lo = ptr - h, hi = lo + W - 1;
        int flo = gs + j, fhi = gs + m - k + j;
        lo = lo < flo ? flo : lo;
        hi = hi > fhi ? fhi : hi;
        if (lo > hi) {
            if (ptr - h > fhi) {
                hi = fhi;
                lo = hi - W + 1;
                if (lo < flo)
                    lo = flo;
            } else {
                lo = flo;
                hi = lo + W - 1;
                if (hi > fhi)
                    hi = fhi;
            }
        }
        int cnt = hi - lo + 1;
        LOJ[j] = lo;
        if (j == 0) {
            for (int o = 0; o < cnt; o++) {
                int u = lo + o, pu = ext[u];
                FB[cur][o] = tx(pu - S) + nodeCost(pu - ext[u - 1], ext[u + 1] - pu);
                PQ[cur][o] = pu;
                PB[base + o] = 0;
            }
        } else {
            int dl = lo - lop, pv = cur ^ 1;
            for (int o = 0; o < (WW > 0 ? WW : cnt); o++) {
                if (WW > 0 && o >= cnt)
                    break;
                int u = lo + o, pu = ext[u];
                int vmax = dl + o;
                vmax = vmax > cntp ? cntp : vmax;
                bool adj = vmax > 0 && vmax == dl + o;
                ll pc = adj ? pcIdx(u - 1) : 0;
                ll best = BIGV;
                int bp = 0;
                for (int po = 0; po < (WW > 0 ? WW : vmax); po++) {
                    ll val = FB[pv][po] + txc(pu - PQ[pv][po]) + (po == vmax - 1 ? pc : 0);
                    val = po < vmax ? val : BIGV;
                    bool lt = val < best;
                    best = lt ? val : best;
                    bp = lt ? po : bp;
                }
                FB[cur][o] = best + nodeCost(pu - ext[u - 1], ext[u + 1] - pu);
                PQ[cur][o] = pu;
                PB[base + o] = (unsigned char)bp;
            }
        }
        cur ^= 1;
        lop = lo;
        cntp = cnt;
        if (j + 1 < k)
            base += W;
    }
    ll best = INF;
    int bo = -1;
    int pl = cur ^ 1;
    for (int o = 0; o < cntp; o++) {
        if (FB[pl][o] >= BIGH)
            continue;
        ll val = FB[pl][o] + tx(slotType - PQ[pl][o]);
        if (val < best) {
            best = val;
            bo = o;
        }
    }
    if (bo < 0)
        return INF;
    int st = nCh;
    nCh += k;
    int o = bo;
    for (int j = k - 1; j >= 0; j--) {
        chA[st + j] = ext[LOJ[j] + o];
        o = PB[base + o];
        base -= W;
    }
    return best;
}
// 稠密候选的链 DP 入口，保留圆环边界条件与最终回溯。
ll denseChain(int k, int S, int slotType, int W, int gs, int ge) {
    if (k <= 0)
        return tx(slotType - S);
    if (ge - gs < k)
        return INF;
    if (W == 3)
        return denseChainK<3>(k, S, slotType, W, gs, ge);
    if (W == 5)
        return denseChainK<5>(k, S, slotType, W, gs, ge);
    if (VC_DCK && W == 4)
        return denseChainK<4>(k, S, slotType, W, gs, ge);
    if (VC_DCK && W == 8)
        return denseChainK<8>(k, S, slotType, W, gs, ge);
    return denseChainK<0>(k, S, slotType, W, gs, ge);
}
ll solveSeg(int k, int S, int slotType, int W, bool dense, int gs, int ge) {
    if (dense && (W <= ZFUSEW || (VC_FUSE8 && W <= 8)))
        return denseChain(k, S, slotType, W, gs, ge);
    nc = 0;
    buildTargets(k, S, slotType, W, dense, gs, ge);
    ll v = chainW(k, S, slotType);
    if (v >= INF)
        return INF;
    for (int j = 0; j < k; j++)
        chA[nCh++] = CP[CH[j]];
    return v;
}
void addNewType(int t, int c) {
    int W = winForU(c, 0);
    int E = zE;
    ll mu = divideNonnegative(N, c);
    if (c >= 16 || (ZTXK > 0 && multiplyNonnegative(c, ZTXK) >= (mu << 2) + 64))
        buildTX((mu << 2) + 64);
    int P = c <= 2 ? zP0 : c <= 32 ? zP1 : ZP2;
    if (mu < P)
        P = (int)(mu < 1 ? 1 : mu);
    ll ph = divideNonnegative(mu, P);
    if (ph < 1)
        ph = 1;
    if (NCLS == 0 && THR0 > 3 && W > zWHL)
        W = zWHL;
    bool dense = NCLS == 0 && multiplyNonnegative(multiplyNonnegative(c, W), ZDENSE) >= E;
    if (dense)
        materializeRing();
    ll bestV = INF;
    nBest = 0;
    ll phase = 0;
    ensureCand(64);
    int seenA[80];
    int nSeen = 0;
    for (int i = 0; i < P; i++, phase += ph) {
        nc = 0;
        int n0 = collect((int)phase, (int)phase - N, (int)phase + N, W);
        if (n0 == 0)
            continue;
        int ba = 0;
        for (int z = 1; z < n0; z++)
            if (CN[z] < CN[ba])
                ba = z;
        int a0 = CP[ba];
        ll v = CN[ba];
        while (a0 >= N)
            a0 -= N;
        while (a0 < 0)
            a0 += N;
        nCh = 0;
        {
            int key = (a0 << 1) | (dense ? 1 : 0);
            bool seen = false;
            for (int q2 = 0; q2 < nSeen; q2++)
                seen |= seenA[q2] == key;
            if (seen)
                continue;
            if (nSeen < 80)
                seenA[nSeen++] = key;
        }
        if (c > 1) {
            int gs = dense ? extFirstAbove(a0) : 0;
            ll w = solveSeg(c - 1, a0, a0 + N, W, dense, gs, gs + E - 1);
            if (w >= INF && !dense) {
                materializeRing();
                dense = true;
                if (nSeen < 80)
                    seenA[nSeen++] = (a0 << 1) | 1;
                gs = extFirstAbove(a0);
                w = solveSeg(c - 1, a0, a0 + N, W, true, gs, gs + E - 1);
            }
            if (w >= INF)
                continue;
            v += w;
        }
        if (v < bestV) {
            bestV = v;
            nBest = 0;
            bestA[nBest++] = a0;
            for (int ii = 0; ii < nCh; ii++)
                bestA[nBest++] = chA[ii];
        }
    }
    applyList(t, true);
    fillRest(t, c);
}
int gK[MAXN + 8], gCap[MAXN + 8], gS[MAXN + 8], gE2[MAXN + 8], gHB[MAXN + 8];
ll gD[MAXN + 8];
int candI[MAXN + 8], candB[MAXN + 8];
ll FQ[MAXN + 8], DQ[MAXN + 8];
int LQ = 0;
void buildQ(int lim) {
    if (lim > N + 1)
        lim = N + 1;
    ll q = 0, d = 0;
    for (int g = 0; g < lim; g++) {
        FQ[g] = q;
        DQ[g] = d;
        d += S1;
        while (d >= N) {
            d -= N;
            q++;
        }
    }
    LQ = lim;
}
int hcnt[1024];
int HSH = 0;
SP2_I int hbucket(ll d) {
    ll b = (d + N) >> HSH;
    if (b < 0)
        b = 0;
    if (b > 1023)
        b = 1023;
    return (int)b;
}
int PCW[(MAXN >> 6) + 4];
void buildPCW() {
    int c = 0;
    for (int w = 0; w < NW; w++) {
        PCW[w] = c;
        c += pc64(vb[w]);
    }
    PCW[NW] = c;
    PCW[NW + 1] = c;
}
SP2_I int cntLess(int p) {
    int w = p >> 6;
    return PCW[w] + pc64(vb[w] & ((1ULL << (p & 63)) - 1));
}
SP2_I int cntLessU(int p) {
    return p <= N ? cntLess(p) : PCW[NW] + cntLess(p - N);
}
SP2_I int gapB(int i, int s) {
    return i + 1 < s ? posX[i + 1] : posX[0] + N;
}
SP2_I int gapCap2(int i, int s) {
    if (gCap[i] < 0)
        gCap[i] = cntLessU(gapB(i, s)) - cntLessU(posX[i] + 1);
    return gCap[i];
}
ll zbTA[MAXN + 8], zbTM[520], zbTG[MAXN + 8], zbTS[MAXN + 8], zbTN[520];
void addExisting(int t, int c) {
    int s = zS;
    int want = c;
    int W = winForU(c, 1);
    int E = zE;
    if (c >= 16 || (ZTXK > 0 && multiplyNonnegative(c, ZTXK) >= (THRX << 2) + 64))
        buildTX((THRX << 2) + 64);
    if (NCLS == 0 && THR0 > 3 && W > zWHL)
        W = zWHL;
    bool dense = NCLS == 0 && multiplyNonnegative(multiplyNonnegative(c, W), ZDENSE) >= E;
    if (dense)
        materializeRing();
    buildPCW();
    ll cap4 = (THRX << 2) + 64;
    if (ZQK == 0 || multiplyNonnegative(s, ZQK) >= cap4)
        buildQ((int)(cap4 < N + 1 ? cap4 : N + 1));
    else
        LQ = 0;
    ll R = S1;
#define BOP_ZBUM 64
#define BOP_ZBSM 0
    const int zbB =
        (BOP_ZBSM > 0 && N <= 1000) ? BOP_ZBSM : ((BOP_ZBMID > 0 && N <= NM) ? BOP_ZBMID : BOP_ZB);
    const bool zbOn = BOP_ZB > 0 && N >= BOP_ZBN && c >= (N >> BOP_ZBC) && E > c;
    ll zbR = 0, zbBN = 0;
    int zbRkP = 0;
    int zbLA = 0, zbLM = 0;
    if (zbOn) {
        zbR = divideNonnegative(multiplyNonnegative(c, N) << 16, E);
        zbBN = multiplyNonnegative(N, zbB);
        {
            zbLA = LQ > 0 ? LQ : 0;
            if (zbLA > MAXN)
                zbLA = MAXN;
            const ll ia = multiplyNonnegative(S1, 16 - zbB);
            ll v = 0;
            for (int g = 0; g < zbLA; g++) {
                zbTA[g] = v;
                v += ia;
            }
            if (BOP_ZBU > 0 && N > NM) {
                ll vg = 0, vs = 0;
                for (int g = 0; g < zbLA; g++) {
                    zbTG[g] = vg;
                    zbTS[g] = vs;
                    vg += E - c;
                    vs += S1;
                }
            }
            zbLM = 64;
            if (zbLM > E + 1)
                zbLM = E + 1;
            const ll im = multiplyNonnegative(zbR, zbB);
            v = 0;
            for (int m = 0; m < zbLM; m++) {
                zbTM[m] = v;
                v += im;
            }
            if (BOP_ZBU > 0 && N > NM) {
                v = N;
                for (int m = 0; m < zbLM; m++) {
                    zbTN[m] = v;
                    v += N;
                }
            }
        }
    }
    int rkA = 1 + cntLess(posX[0]);
    for (int i = 0; i < s; i++) {
        int a = posX[i], b = gapB(i, s);
        int g = b - a;
        if (dense) {
            int rkB = 1 + cntLessU(b);
            gS[i] = rkA;
            gE2[i] = rkB;
            gCap[i] = rkB - rkA;
            rkA = rkB;
        } else
            gCap[i] = g < 2 ? 0 : -1;
        ll q, d;
        if (zbOn) {
            int m;
            if (dense)
                m = gCap[i];
            else {
                if (i == 0)
                    zbRkP = cntLessU(a);
                if (gCap[i] == 0)
                    m = 0;
                else {
                    const int rkB2 = cntLessU(b);
                    m = rkB2 - zbRkP;
                    gCap[i] = m;
                    zbRkP = rkB2;
                }
            }
            ll sgN;
            if (g < zbLA && m < zbLM)
                sgN = (zbTA[g] + zbBN + (zbTM[m] >> 16)) >> 4;
            else
                sgN = (multiplyNonnegative(multiplyNonnegative(S1, g), 16 - zbB) + zbBN +
                       (multiplyNonnegative(multiplyNonnegative(m, zbR), zbB) >> 16)) >>
                      4;
            if (BOP_ZBU > 0 && N > NM && m < BOP_ZBUM) {
                ll add;
                if (BOP_ZBU == 1 && g < zbLA && m < zbLM) {
                    const ll tv = zbTN[m] - zbTG[g];
                    add = (tv < 0 ? 0 : tv) - zbTS[g];
                } else {
                    const ll tv = multiplyNonnegative(m + 1, N) - multiplyNonnegative(g, E - c);
                    add = multiplyNonnegative(tv < 0 ? 0 : tv, BOP_ZBU) -
                          multiplyNonnegative(multiplyNonnegative(S1, g), BOP_ZBU);
                }
                sgN += add >> 4;
                if (sgN < 0)
                    sgN = 0;
            }
            if (sgN < ((ll)N << 3)) {
                q = 0;
                d = sgN;
                while (d >= N) {
                    d -= N;
                    q++;
                }
            } else {
                q = divideNonnegative(sgN, N);
                d = sgN - multiplyNonnegative(q, N);
            }
        } else if (g < LQ) {
            q = FQ[g];
            d = DQ[g];
        } else {
            ll sg = multiplyNonnegative(S1, g);
            q = divideNonnegative(sg, N);
            d = sg - multiplyNonnegative(q, N);
        }
        if (q < 1) {
            d -= N;
            q = 1;
        }
        int k = (int)q - 1;
        R -= q;
        if (k >= 1) {
            int cp = gapCap2(i, s);
            if (k > cp) {
                ll ex = k - cp;
                k = cp;
                R += ex;
                d += multiplyNonnegative(ex, N);
            }
        }
        gK[i] = k;
        gD[i] = d;
        gHB[i] = hbucket(d);
    }
    int rounds = 0;
    while (R != 0 && rounds < 64) {
        rounds++;
        bool big = R > 0;
        int ncand = 0, blo = 1024, bhi = -1;
        if (big) {
            for (int i = 0; i < s; i++) {
                int cp = gCap[i];
                bool ok = cp != 0 && (cp < 0 || cp > gK[i]);
                if (!ok)
                    continue;
                int bk = gHB[i];
                candI[ncand] = i;
                candB[ncand] = bk;
                ncand++;
                hcnt[bk]++;
                blo = bk < blo ? bk : blo;
                bhi = bk > bhi ? bk : bhi;
            }
        } else {
            for (int i = 0; i < s; i++) {
                if (gK[i] < 1)
                    continue;
                int bk = 1023 - gHB[i];
                candI[ncand] = i;
                candB[ncand] = bk;
                ncand++;
                hcnt[bk]++;
                blo = bk < blo ? bk : blo;
                bhi = bk > bhi ? bk : bhi;
            }
        }
        if (ncand == 0)
            break;
        int need = big ? (int)R : (int)(-R);
        if (need > ncand)
            need = ncand;
        int acc = 0, B = bhi;
        while (B >= 0 && acc + hcnt[B] < need) {
            acc += hcnt[B];
            B--;
        }
        int takeB = need - acc, cntB = B >= 0 ? hcnt[B] : 0, dda = cntB >> 1;
        for (int b = blo; b <= bhi; b++)
            hcnt[b] = 0;
        for (int ci = 0; ci < ncand; ci++) {
            int bk = candB[ci];
            if (bk < B)
                continue;
            if (bk == B) {
                dda += takeB;
                if (dda >= cntB)
                    dda -= cntB;
                else
                    continue;
            }
            int i = candI[ci];
            if (big) {
                if (gapCap2(i, s) > gK[i]) {
                    gK[i]++;
                    gD[i] -= N;
                    gHB[i] = hbucket(gD[i]);
                    R--;
                }
            } else {
                gK[i]--;
                gD[i] += N;
                gHB[i] = hbucket(gD[i]);
                R++;
            }
        }
    }
    while (R < 0) {
        bool any = false;
        for (int i = 0; i < s && R < 0; i++)
            if (gK[i] > 0) {
                gK[i]--;
                gD[i] += N;
                R++;
                any = true;
            }
        if (!any)
            break;
    }
    nCh = 0;
#define LT_AWK 0
#define LT_AWKK 0
#define LT_AWC 0
    const int W0 = W;
    const bool awOn = N > LT_AWN && c >= LT_AWC;
    const int W1 = (LT_AW1 > 0 && awOn && W < LT_AW1) ? LT_AW1 : W;
    const int WK = (LT_AWK > 0 && awOn && W < LT_AWK) ? LT_AWK : W;
    ensureCand((W1 > WK ? W1 : WK) + 40);
    for (int i = 0; i < s; i++) {
        int k = gK[i];
        if (k <= 0)
            continue;
        int a = posX[i], b = gapB(i, s);
        if (LT_AW1 > 0 || LT_AWK > 0)
            W = k == 1 ? W1
                       : ((LT_AWKK == 0 || (LT_AWKK > 0 ? k <= LT_AWKK : k >= -LT_AWKK)) ? WK : W0);
        if (k == 1) {
            int mid = a + ((b - a) >> 1);
            nc = 0;
            if (dense) {
                int gs = gS[i], ge = gE2[i];
                int lo, hi;
                if (ge - gs <= W) {
                    lo = gs;
                    hi = ge - 1;
                } else {
                    int lo2 = 1 + cntLessU(mid);
                    lo = lo2 - (W >> 1);
                    hi = lo + W - 1;
                    if (lo < gs) {
                        lo = gs;
                        hi = lo + W - 1;
                    }
                    if (hi > ge - 1) {
                        hi = ge - 1;
                        lo = hi - W + 1;
                    }
                }
                ll bv = INF;
                int bpp = -1;
                for (int z = lo; z <= hi; z++) {
                    int pz = ext[z];
                    ll v = tx(pz - a) + tx(b - pz) + nodeCost(pz - ext[z - 1], ext[z + 1] - pz);
                    if (v < bv) {
                        bv = v;
                        bpp = pz;
                    }
                }
                if (bpp >= 0) {
                    chA[nCh++] = bpp;
                    continue;
                }
            } else if (NCLS > 0)
                collectST<XLS_CSL != 0>(mid, a, b);
            else
                collect(mid, a, b, W);
            ll bv = INF;
            int bp = -1;
            for (int u = 0; u < nc; u++) {
                ll v = tx(CP[u] - a) + tx(b - CP[u]) + CN[u];
                if (v < bv) {
                    bv = v;
                    bp = u;
                }
            }
            if (bp >= 0) {
                chA[nCh++] = CP[bp];
                continue;
            }
        }
        ll okv = solveSeg(k, a, b, W, dense, dense ? gS[i] : 0, dense ? gE2[i] : 0);
        if (okv >= INF && !dense) {
            int qq = a + 1, cnt = 0;
            int ne = 0;
            ext[ne++] = prevU(a);
            while (true) {
                int r2 = nextU(qq);
                if (r2 >= b)
                    break;
                ext[ne++] = r2;
                qq = r2 + 1;
                cnt++;
            }
            ext[ne++] = nextU(b);
            if (k > cnt)
                k = cnt;
            if (k > 0)
                solveSeg(k, a, b, W, true, 1, 1 + cnt);
        }
    }
    W = W0;
    (void)W;
    applyList(t, false);
    fillRest(t, want);
}
void doAdd(int t, int c, int s, int E) {
    zE = E;
    zS = s;
    zDone = 0;
    zWant = c;
    if (c <= 0)
        return;
    if (c >= E) {
        fillAllEmpty(t);
        return;
    }
    setWeights(s + c, E - c);
    buildV3();
    NCLS = 0;
    if (C0 > 0 && c <= ZCLS_C) {
        if (THR0 <= 2)
            NCLS = 2;
        else if (THR0 == 3)
            NCLS = ZNC3;
    }
    W0C = ZW0C;
    RCLS = ZRCLS;
    if (s == 0)
        addNewType(t, c);
    else
        addExisting(t, c);
}
RVEC(int) rPE, rNE;
RVEC(char) rDead;
void vacDists(int s) {
    rPE.resize(s);
    rNE.resize(s);
    int E = zE;
    if (E == 0) {
        for (int i = 0; i < s; i++) {
            rPE[i] = N;
            rNE[i] = N;
        }
        return;
    }
    buildV3();
    int pe = -1, ne = -1;
    for (int i = 0; i < s; i++) {
        int p = posX[i];
        if (!(ne > p)) {
            pe = prev3(p - 1);
            ne = next3(p + 1);
        }
        rPE[i] = p - pe;
        rNE[i] = ne - p;
    }
}
int P2A[(MAXN << 1) + 8];
ll V2A[(MAXN << 1) + 8];
unsigned char PBA[(MAXN << 6) + 128];
int LOJA[MAXN + 8];
int keptA[MAXN + 8];
char rDeadA[MAXN + 8];
ll Y2A[(MAXN << 1) + 8];
int LCNT[MAXN + 8];
int latticeDP3(int k, int s, int s1, int ra, int A) {
    {
        ll q = divideNonnegative(N, s1), rr = N - multiplyNonnegative(q, s1);
        ll acc = s1 >> 1;
        ll pos = A;
        int ptr = ra + 1;
        int last = ra + s - 1;
        int flo = ra + 1, fhi = ra + s - s1 + 1;
        for (int j = 0; j < k; j++, flo++, fhi++) {
            pos += q;
            acc += rr;
            ll ov = acc >= s1 ? s1 : 0;
            acc -= ov;
            pos += ov != 0;
            ptr += (int)((ptr <= last) & (P2A[ptr] < pos));
            ptr += (int)((ptr <= last) & (P2A[ptr] < pos));
            while (ptr <= last && P2A[ptr] < pos)
                ptr++;
            int lo = ptr - 1, hi = lo + 2;
            lo = lo < flo ? flo : lo;
            hi = hi > fhi ? fhi : hi;
            if (lo > hi) {
                if (ptr - 1 > fhi) {
                    hi = fhi;
                    lo = hi - 2;
                    if (lo < flo)
                        lo = flo;
                } else {
                    lo = flo;
                    hi = lo + 2;
                    if (hi > fhi)
                        hi = fhi;
                }
            }
            LOJA[j] = lo;
            LCNT[j] = hi - lo + 1;
        }
    }
    const ll cns = CNS;
    ll a0, a1, a2, b0, b1, b2, f0 = 0, f1 = 0, f2 = 0;
    int lop, cntp;
    {
        int lo = LOJA[0], cnt = LCNT[0];
        ll pvA = V2A[ra + 1];
        ll FCt[3] = {0, 0, 0}, AT[3] = {0, 0, 0}, BT[3] = {0, 0, 0};
        for (int o = 0; o < cnt; o++) {
            int u = lo + o;
            FCt[o] = tx(P2A[u] - A) + V2A[u] - pvA;
            PBA[o] = 0;
            ll gg = FCt[o] - V2A[u + 1];
            AT[o] = gg + Y2A[u];
            BT[o] = gg - Y2A[u];
        }
        a0 = AT[0];
        a1 = AT[1];
        a2 = AT[2];
        b0 = BT[0];
        b1 = BT[1];
        b2 = BT[2];
        f0 = FCt[0];
        f1 = FCt[1];
        f2 = FCt[2];
        lop = lo;
        cntp = cnt;
    }
    int base = 3;
    for (int j = 1; j < k; j++, base += 3) {
        int lo = LOJA[j];
        int dl = lo - lop;
        ll na[3], nb[3], nf[3];
        for (int o = 0; o < 3; o++) {
            int u = lo + o;
            ll yu = Y2A[u], up = yu - cns, um = cns - yu;
            int vmax = dl + o;
            vmax = vmax > cntp ? cntp : vmax;
            ll c0 = b0 + up, c1 = b1 + up, c2 = b2 + up;
            ll e0 = a0 + um, e1 = a1 + um, e2 = a2 + um;
            c0 = c0 > e0 ? c0 : e0;
            c1 = c1 > e1 ? c1 : e1;
            c2 = c2 > e2 ? c2 : e2;
            c0 = vmax > 0 ? c0 : BIGV;
            c1 = vmax > 1 ? c1 : BIGV;
            c2 = vmax > 2 ? c2 : BIGV;
            ll best = BIGV;
            int bp = 0;
            bool lt = c0 < best;
            best = lt ? c0 : best;
            bp = lt ? 0 : bp;
            lt = c1 < best;
            best = lt ? c1 : best;
            bp = lt ? 1 : bp;
            lt = c2 < best;
            best = lt ? c2 : best;
            bp = lt ? 2 : bp;
            ll fu = best + V2A[u];
            nf[o] = fu;
            ll gg = fu - V2A[u + 1];
            na[o] = gg + yu;
            nb[o] = gg - yu;
            PBA[base + o] = (unsigned char)bp;
        }
        a0 = na[0];
        a1 = na[1];
        a2 = na[2];
        b0 = nb[0];
        b1 = nb[1];
        b2 = nb[2];
        f0 = nf[0];
        f1 = nf[1];
        f2 = nf[2];
        lop = lo;
        cntp = LCNT[j];
    }
    base -= 3;
    ll FC[3] = {f0, f1, f2};
    ll best = INF;
    int bo = -1;
    ll pvE = V2A[ra + s];
    for (int o = 0; o < cntp; o++) {
        if (FC[o] >= BIGH)
            continue;
        int u = lop + o;
        ll val = FC[o] + tx(A + N - P2A[u]) + pvE - V2A[u + 1];
        if (val < best) {
            best = val;
            bo = o;
        }
    }
    if (bo < 0)
        return 0;
    int nk = 0;
    keptA[nk++] = ra;
    int o = bo;
    for (int j = k - 1; j >= 0; j--) {
        keptA[nk++] = LOJA[j] + o;
        o = PBA[base + o];
        base -= 3;
    }
    return nk;
}
template <int WW>
// 在删除形成的间隔格点上作动态规划，兼顾剩余服务与新增空位。
int latticeDP(int k, int Wr, int s, int s1, int ra, int A) {
    const int W = WW > 0 ? WW : Wr;
    ll AB[2][72], BB[2][72], FC[72];
    int cur = 0;
    for (int o = 0; o < 72; o++) {
        AB[0][o] = 0;
        AB[1][o] = 0;
        BB[0][o] = 0;
        BB[1][o] = 0;
        FC[o] = 0;
    }
    ll q = divideNonnegative(N, s1), rr = N - multiplyNonnegative(q, s1);
    ll acc = s1 >> 1;
    ll pos = A;
    int ptr = ra + 1, h = W >> 1;
    int last = ra + s - 1;
    int lop = 0, cntp = 0, base = 0;
    ll pvA = V2A[ra + 1];
    const ll cns = CNS;
    for (int j = 0; j < k; j++) {
        pos += q;
        acc += rr;
        if (acc >= s1) {
            acc -= s1;
            pos++;
        }
        ptr += (ptr <= last && P2A[ptr] < pos);
        ptr += (ptr <= last && P2A[ptr] < pos);
        while (ptr <= last && P2A[ptr] < pos)
            ptr++;
        int lo = ptr - h, hi = lo + W - 1;
        int flo = ra + 1 + j, fhi = ra + s - s1 + 1 + j;
        lo = lo < flo ? flo : lo;
        hi = hi > fhi ? fhi : hi;
        if (lo > hi) {
            if (ptr - h > fhi) {
                hi = fhi;
                lo = hi - W + 1;
                if (lo < flo)
                    lo = flo;
            } else {
                lo = flo;
                hi = lo + W - 1;
                if (hi > fhi)
                    hi = fhi;
            }
        }
        int cnt = hi - lo + 1;
        LOJA[j] = lo;
        if (j == 0) {
            for (int o = 0; o < cnt; o++) {
                int u = lo + o;
                FC[o] = tx(P2A[u] - A) + V2A[u] - pvA;
                PBA[base + o] = 0;
                ll gg = FC[o] - V2A[u + 1];
                AB[cur][o] = gg + Y2A[u];
                BB[cur][o] = gg - Y2A[u];
            }
        } else if (WW == 3) {
            int dl = lo - lop, pv = cur ^ 1;
            ll a0 = AB[pv][0], a1 = AB[pv][1], a2 = AB[pv][2];
            ll b0 = BB[pv][0], b1 = BB[pv][1], b2 = BB[pv][2];
            for (int o = 0; o < 3; o++) {
                int u = lo + o;
                ll yu = Y2A[u], up = yu - cns, um = cns - yu;
                int vmax = dl + o;
                vmax = vmax > cntp ? cntp : vmax;
                ll c0 = b0 + up, c1 = b1 + up, c2 = b2 + up;
                ll e0 = a0 + um, e1 = a1 + um, e2 = a2 + um;
                c0 = c0 > e0 ? c0 : e0;
                c1 = c1 > e1 ? c1 : e1;
                c2 = c2 > e2 ? c2 : e2;
                c0 = vmax > 0 ? c0 : BIGV;
                c1 = vmax > 1 ? c1 : BIGV;
                c2 = vmax > 2 ? c2 : BIGV;
                ll best = BIGV;
                int bp = 0;
                bool lt = c0 < best;
                best = lt ? c0 : best;
                bp = lt ? 0 : bp;
                lt = c1 < best;
                best = lt ? c1 : best;
                bp = lt ? 1 : bp;
                lt = c2 < best;
                best = lt ? c2 : best;
                bp = lt ? 2 : bp;
                ll fu = best + V2A[u];
                FC[o] = fu;
                ll gg = fu - V2A[u + 1];
                AB[cur][o] = gg + yu;
                BB[cur][o] = gg - yu;
                PBA[base + o] = (unsigned char)bp;
            }
        } else {
            int pv = cur ^ 1;
            for (int o = 0; o < cnt; o++) {
                int u = lo + o;
                ll yu = Y2A[u], up = yu - cns, um = cns - yu;
                int vmax = u - lop;
                if (vmax > cntp)
                    vmax = cntp;
                ll best = BIGV;
                int bp = 0;
                for (int po = 0; po < (WW > 0 ? WW : vmax); po++) {
                    ll c1 = BB[pv][po] + up, e1 = AB[pv][po] + um;
                    ll val = c1 > e1 ? c1 : e1;
                    if (WW > 0)
                        val = po < vmax ? val : BIGV;
                    bool lt = val < best;
                    best = lt ? val : best;
                    bp = lt ? po : bp;
                }
                ll fu = best + V2A[u];
                FC[o] = fu;
                ll gg = fu - V2A[u + 1];
                AB[cur][o] = gg + yu;
                BB[cur][o] = gg - yu;
                PBA[base + o] = (unsigned char)bp;
            }
        }
        cur ^= 1;
        lop = lo;
        cntp = cnt;
        if (j + 1 < k)
            base += W;
    }
    ll best = INF;
    int bo = -1;
    ll pvE = V2A[ra + s];
    for (int o = 0; o < cntp; o++) {
        if (FC[o] >= BIGH)
            continue;
        int u = lop + o;
        ll val = FC[o] + tx(A + N - P2A[u]) + pvE - V2A[u + 1];
        if (val < best) {
            best = val;
            bo = o;
        }
    }
    if (bo < 0)
        return 0;
    int nk = 0;
    keptA[nk++] = ra;
    int o = bo;
    for (int j = k - 1; j >= 0; j--) {
        keptA[nk++] = LOJA[j] + o;
        o = PBA[base + o];
        base -= W;
    }
    return nk;
}
void removeLattice(int t, int c, int W) {
    int s = (int)posX.size();
    int s1 = s - c;
    buildTX((THRX << 2) + 64);
    V2A[0] = 0;
    if (zE == 0) {
        ll f = rh0(N) + rh0(N) - rh0(N + N);
        for (int r = 0; r < s; r++) {
            V2A[r + 1] = V2A[r] + f;
            P2A[r] = posX[r];
        }
    } else {
        int firstV = nextNWv(0), lastV = prevNWv(N - 1);
        int pe = -1, ne = -1;
        for (int r = 0; r < s; r++) {
            int p = posX[r];
            if (!(ne > p)) {
                int a1 = prevNWv(p - 1);
                pe = a1 >= 0 ? a1 : lastV - N;
                int b1 = nextNWv(p + 1);
                ne = b1 >= 0 ? b1 : firstV + N;
            }
            ll a = p - pe, b = ne - p;
            ll f = rh0(a) + rh0(b) - rh0(a + b);
            V2A[r + 1] = V2A[r] + f;
            P2A[r] = p;
        }
    }
    Y2A[0] = 0;
    for (int r = 1; r < s; r++)
        Y2A[r] = Y2A[r - 1] + linX(posX[r] - posX[r - 1]);
    int ra = 0;
    for (int r = 1; r < W && r < s; r++)
        if (V2A[r + 1] - V2A[r] > V2A[ra + 1] - V2A[ra])
            ra = r;
    {
        ll tot = V2A[s], yn = multiplyNonnegative(CXS1, N);
        int re = s + ra + 3;
        if (re > (s << 1))
            re = s << 1;
        for (int r = s; r < re; r++) {
            P2A[r] = posX[r - s] + N;
            V2A[r + 1] = V2A[r - s + 1] + tot;
            Y2A[r] = Y2A[r - s] + yn;
        }
    }
    int A = P2A[ra];
    int k = s1 - 1;
    int nk = 1;
    keptA[0] = ra;
    if (k > 0) {
        nk = W == 3   ? latticeDP3(k, s, s1, ra, A)
             : W == 5 ? latticeDP<5>(k, W, s, s1, ra, A)
             : W == 6 ? latticeDP<6>(k, W, s, s1, ra, A)
                      : latticeDP<0>(k, W, s, s1, ra, A);
        if (nk == 0) {
            int acc2 = s >> 1;
            for (int i = 0; i < s; i++) {
                acc2 += c;
                if (acc2 >= s) {
                    acc2 -= s;
                    zFree(posX[i]);
                }
            }
            return;
        }
    }
    for (int i = 0; i < s; i++)
        rDeadA[i] = 1;
    for (int i = 0; i < nk; i++) {
        int r = keptA[i];
        rDeadA[r >= s ? r - s : r] = 0;
    }
    zFreeBatch(t, s);
}
void removeBlocks(int t, int c) {
    int s = (int)posX.size();
    buildHX();
    vacDists(s);
    rDead.assign(s, 0);
    int acc = 0, st = 0, lastPick = -5;
    for (int b = 0; b < c; b++) {
        int en = st;
        while (true) {
            acc += c;
            en++;
            if (acc >= s) {
                acc -= s;
                break;
            }
        }
        ll bc = INF;
        int bi = -1;
        for (int i = st; i < en && i < s; i++) {
            if (i == lastPick + 1)
                continue;
            int p = posX[i];
            ll gL = p - posX[i ? i - 1 : s - 1];
            if (gL <= 0)
                gL += N;
            ll gR = posX[i + 1 < s ? i + 1 : 0] - p;
            if (gR <= 0)
                gR += N;
            ll a = rPE[i], bb = rNE[i];
            ll v = rhx(gL + gR) - rhx(gL) - rhx(gR) + rh0(a) + rh0(bb) - rh0(a + bb);
            if (v < bc) {
                bc = v;
                bi = i;
            }
        }
        if (bi < 0)
            bi = st < s ? st : s - 1;
        rDead[bi] = 1;
        lastPick = bi;
        st = en;
    }
    for (int i = 0; i < s; i++)
        if (rDead[i])
            zFree(posX[i]);
    for (int i = 0; i < s && zDone < c; i++)
        if (!rDead[i]) {
            zFree(posX[i]);
            rDead[i] = 1;
        }
}
void doRemove(int t, int c, int s, int E) {
    zE = E;
    zS = s;
    zDone = 0;
    remMode = true;
    setWeights(s - c, E + c);
    remMode = false;
    if (multiplyNonnegative(c, ZREMK) >= s) {
        int wr = winForU(s - c, 2);
        if (wr > zWR)
            wr = zWR;
        removeLattice(t, c, wr);
    } else
        removeBlocks(t, c);
}
} // namespace placement_dp
