// 当前布局、类型计数、同类环链与空位位图。以整数间隔惩罚建立可增量计算的均匀度代价，并记录本次操作的改动。
// Included in fixed order by solution.cpp.

namespace {
typedef long long ll;
typedef unsigned long long ull;
#if defined(__NO_INLINE__)
#define SP2_O0CMD 1
#else
#define SP2_O0CMD 0
#endif
#if (SP2_AI0 == 1 && defined(__NO_INLINE__)) ||                                                    \
    (SP2_AI0 == 2 && defined(__NO_INLINE__) && defined(__OPTIMIZE__) && !defined(__clang__)) ||    \
    (SP2_AI0 == 3 && defined(__GNUC__) && !defined(__clang__))
#define SP2_I __attribute__((always_inline)) inline
#else
#define SP2_I inline
#endif
#if SP2_RV == 1 || (SP2_RV == 2 && SP2_O0CMD) ||                                                   \
    (SP2_RV == 3 && (SP2_O0CMD || (defined(__GNUC__) && !defined(__clang__))))
template <class V> struct RV {
    typedef typename vector<V>::pointer iterator;
    typedef typename vector<V>::const_pointer const_iterator;
    vector<V> v;
    iterator p;
    size_t n;
    RV() : p(nullptr), n(0) {}
    __attribute__((always_inline)) void sync() {
        p = v.data();
        n = v.size();
    }
    __attribute__((always_inline)) void trim() {
        if (v.size() > n)
            v.resize(n);
    }
    __attribute__((always_inline)) V &operator[](size_t i) {
        return p[i];
    }
    __attribute__((always_inline)) const V &operator[](size_t i) const {
        return p[i];
    }
    __attribute__((always_inline)) size_t size() const {
        return n;
    }
    __attribute__((always_inline)) bool empty() const {
        return n == 0;
    }
    __attribute__((always_inline)) iterator begin() {
        return p;
    }
    __attribute__((always_inline)) iterator end() {
        return p + n;
    }
    __attribute__((always_inline)) const_iterator begin() const {
        return p;
    }
    __attribute__((always_inline)) const_iterator end() const {
        return p + n;
    }
    __attribute__((always_inline)) iterator data() {
        return p;
    }
    __attribute__((always_inline)) const_iterator data() const {
        return p;
    }
    __attribute__((always_inline)) V &back() {
        return p[n - 1];
    }
    __attribute__((always_inline)) void clear() {
        n = 0;
    }
    __attribute__((always_inline)) void pop_back() {
        n--;
    }
    __attribute__((always_inline)) void push_back(const V &x) {
        if (n < v.size()) {
            p[n] = x;
            n++;
        } else {
            v.push_back(x);
            sync();
        }
    }
    void resize(size_t k) {
        if (k <= v.size()) {
            for (size_t i = n; i < k; i++)
                p[i] = V();
            n = k;
        } else {
            trim();
            v.resize(k);
            sync();
        }
    }
    void resize(size_t k, const V &x) {
        if (k <= v.size()) {
            for (size_t i = n; i < k; i++)
                p[i] = x;
            n = k;
        } else {
            trim();
            v.resize(k, x);
            sync();
        }
    }
    void assign(size_t k, const V &x) {
        if (k == v.size()) {
            for (size_t i = 0; i < k; i++)
                p[i] = x;
            n = k;
        } else {
            v.assign(k, x);
            sync();
        }
    }
    void reserve(size_t k) {
        size_t m = n;
        v.reserve(k);
        p = v.data();
        n = m;
    }
    void swap(RV &o) {
        v.swap(o.v);
        const size_t t_ = n;
        n = o.n;
        o.n = t_;
        p = v.data();
        o.p = o.v.data();
    }
    void swap(vector<V> &o) {
        trim();
        v.swap(o);
        sync();
    }
    void erase(iterator a, iterator b) {
        trim();
        v.erase(v.begin() + (a - p), v.begin() + (b - p));
        sync();
    }
};
#define RVEC(V) RV<V>
#define RVSTD(x) (x).v
#else
#define RVEC(V) vector<V>
#define RVSTD(x) x
#endif
int blGAMMA, blHVK, blBFR, blQB, blRQ_POLR, blRQ_PW, blRQ_PWB, blRQ_PH, blCCAPB, blSH_LSK, blSH_LSH;
int blPBUD16 = 0;
#define HMIN 20
#define MIDW 2
#define WIN 32
#define INITB 4
#define RW 4
#define NSCALE 8192
#define CCAP 64
#define RBDS 2
#define TRIG 0
#define LAM 12
#define CHK 16
#define MINGAP 16
#define BIGMIN 4
#define BIGADD 1
#define INITOM 1
// 非负整数移位乘法；算法中的乘法统一通过受限算术实现。
SP2_I ll multiplyNonnegative(ll a, ll b) {
    if (a >= 0 && a < b) {
        const ll t = a;
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
SP2_I ll mulm(ll a, ll b) {
    if (a < b) {
        ll t = a;
        a = b;
        b = t;
    }
    return multiplyNonnegative(a, b);
}
// 非负整数二进制除法；保留原有位宽与内建位扫描优化。
SP2_I ll divideNonnegative(ll a, ll b) {
    if (a < b)
        return 0;
    if (b > 0) {
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
const int MAXN = 16384 + 192;
const int MAXT = 16384 + 16;
int N = 0, NW = 0, NS = 0;
RVEC(int) publicGrid;
int slotType[MAXN];
int nextSame[MAXN], prevSame[MAXN];
int changeStamp[MAXN], originalValue[MAXN];
char inq[MAXN];
ull vb[(MAXN >> 6) + 2];
ull vs[4];
int operationStamp = 0;
int svWarming = 0;
int svWarmForce = 0;
int operationCount = 0;
#define SM_HI 1000
#define SM_MNCAP 0
#define SM_MNP 0
#define SM_MNPR 0
#define SM_MNSRC 0
#define SM_WL2 -1
#define SM_H4 0
#define SM_H4R 0
#define SM_GP 0
#define SM_GH 0
#define SM_GSW 256
#define SM_GSRC 4096
#define SM_GEV 100000
#define SM_CHK 0
#define SM_MINGAP -1
#define SM_BUDB -1
#define SM_BUDC -1
#define SM_NSC 0
#define SM_RVB 0
#define SM_HCRW 0
#define SM_HCFM -1
int smT = 0;
#define SDY_HS 16
int sdyHf = 16, sdyHr = 16;
#define SDY_HSALL 0
#define SDY_HT (SDY_HSALL ? (N > 100) : smT)
SP2_I int sdyH(int h) {
    if (!SDY_HSON || !SDY_HT || sdyHf == 16)
        return h;
    int r = (int)(multiplyNonnegative(h, sdyHf) >> 4);
    return r < 1 ? 1 : r;
}
SP2_I int sdyR(int h) {
    if (!SDY_HSON || !SDY_HT || sdyHr == 16)
        return h;
    int r = (int)(multiplyNonnegative(h, sdyHr) >> 4);
    return r < 1 ? 1 : r;
}
#define SDY_HRM -1
#define SDY_HRB 16
#define SDY_HRLO 8
#define SDY_HRHI 32
#define SQ_MHQB 8
#define MQ_LO 1000
#define MQ_HI 4999
int mqT = 0;
#define HVM_G 0
#define HVM_SH 5
#define HVM_EV 0
#define HVM_EVN 0
#define HVM_BIGMIN -1
#define HVM_BIGREM 0
#define HVM_TAU 0
#define HVM_TAUA 0
#define HVM_DDS 0
#define HVM_DDD 0
#define HVM_BKA 0
#define HVM_BKB 0
#define HVM_RVB 0
#define HVM_PRE 0
#define HVM_PREH4 12
#define HVM_PREW 64
#define HVM_PREV 100000
#define HVM_PREP 64
#define HVM_PREV0 1
#define HVM_PREPOS 0
#define HVM_RX 0
#define HVM_RXH 2
#define HVM_RXT 4
#define HVM_FW 0
#define HVM_FK 3
#define HVM_FD 2
#define HVM_FH 8
#define HVM_FR 1
#define HVM_FV0 0
#define HVM_FA 0
#define HVM_ZW 0
#define HVM_ZWS 16
#define HVM_ZWM2 8
#define HVM_ZWM 5
#define HVM_ZWB 3
#define HVM_DEF 0
#define HVM_DEFR 3
#define HVM_DEFMAX 64
#define HVM_DEFN 2
#define HVM_VR1 0
#define HVM_VR1H 4
#define HVM_VR1K 8
#define HVM_VR1S 0
#define HVM_LMN 0
#define HVM_EVC 0
#define HVM_EVCAP 1000000
#define HVM_EV0 0
#define HVM_EVNS 0
#define HVM_BR 0
#define HVM_B0 64
#define HVM_BA 3
#define HVM_BAC 0
#define HVM_WP 0
#define HVM_WPO 64
#define HVM_WPR 0
#define HVM_TB 0
#define HVM_TB0 32
#define HVM_TBR 0
#define HVM_TBC 1000000
#define HVM_TBN 0
#define HVM_CCAP 0
#define HVM_BUDC 0
#define MQ_MNC 0
#define MQ_MNCAP 0
#define MQ_MNC0 0
#define MQ_MNP 0
#define MQ_MNPR 0
#define MQ_MNSRC 0
#define MQ_MNSRCR 0
#define MQ_MNW 0
#define MQ_MNM -1
#define MQ_MNR -1
#define MQ_MNK 0
#define MQ_MEDW -1
#define MQ_ZW -1
#define MQ_WL2 -1
#define MQ_STS -2
#define MQ_STV -2
#define MQ_H4 0
#define MQ_H4R 0
#define MQ_MN2 0
#define MQ_MN2P 0
#define MQ_NBS 0
#define MQ_NBV 0
#define MQ_NBK 0
#define MQ_TNB 0
#define MQ_GATE 0
#define MQ_GATEM 31
int mqRich = 1;
#define MQG(b) (!(MQ_GATE > 0 && (MQ_GATEM & (b))) || mqRich)
#define LGM_SRC 0
#define LGM_FAIL 0
#define LGM_NOXR 1
#define LGM_MNCX 0
#define LGM_RBH 0
#define LGM_MNC 0
#define LGM_MNCAP 0
#define LGM_PART 0
#define LGM_RVB 0
#define LGM_NORV 0
#define LGM_ANY                                                                                    \
    (LGM_MNCS > 0 || LGM_MNCX > 0 || LGM_NORV > 0 || LGM_PART > 0 || LGM_RVB > 0 || LGM_RBW > 0 || \
     LGM_RBS > 0 || LGM_RBH > 0 || LGM_RBP != 0 || LGM_MNC > 0 || LGM_MNCAP > 0 || LGM_MNW > 0 ||  \
     LGM_SRC > 0 || LGM_STV >= 0 || LGM_STT >= 0 || LGM_FAIL > 0 || LGM_RBT > 0 || LGM_NOX > 0 ||  \
     LGM_MNOFF > 0)
int lgmAdd = 0;
int lgmL = 0;
#define MQ_V0R 0
#define MQ_V0S -1
#define MQ_CHK 0
#define MQ_MINGAP -1
#define MQ_TAU -1
#define MQ_TAUA -1
#define MQ_LAM -1
#define MQ_DDS -1
#define MQ_DDD -1
#define MQ_BUDB -1
#define MQ_BUDC -1
#define MQ_RBPOL -1
#define MQ_BIGSH -1
#define SM_NBK 0
#define SM_NBV 0
int smNbSt[MAXN];
#define SM_PART 0
#define SM_ZWS 0
#define SM_ZWM2 0
#define SM_ZWM 0
#define SM_ZWHL 0
#define SM_ZWR 0
unsigned char hcT[MAXT];
#define SM_NOX 0
#define SM_VSW 0
#define SM_HCTS 0
#define MNCHL ((SM_MNCH > 0 && smT) ? SM_MNCH : MNCH)
#define SM_V0S -1
#define SM_DDD 0
#define SM_DDS 0
#define SM_HVK0 -1
#define SM_HVK1 -1
#define SM_HVK2 -1
#define SM_HVK3 -1
#define SM_LAM0 -1
#define SM_LAM1 -1
#define SM_LAM2 -1
#define SM_LAM3 -1
#define SM_TAUA0 -1
#define SM_TAUA1 -1
#define SM_TAUA2 -1
#define SM_TAUA3 -1
#define SM_SA 0
#define SM_SAW 8
#define SM_SAT 16
#define SM_SAH 28
#define SM_SAL 0
#define SM_VCT 0
#define SM_LSH 0
#define SM_HC 0
#define SM_VH 4
#define SM_VW 8
#define SM_VACT 0
#define SM_SWK 0
#define SM_SWN 3
#define SM_SWH 8
#define SM_SWW 4
#define SM_SWV 1
#define SM_RCH 0
#define SM_RCT 0
#define XCW 1
#define PENDNEW 1
#define ZARS 0
#define ZAMAX 1000000000
#define ZABLK 1
#define ZAS1MAX 1000000
#define ZREMKL 8
#define RBMODE 0
int pZACX = 0, pRBMF = 0, pINITOM = 1;
int pBUDB, pBUDC, pBUDBB, pTAU, pTAUA, pCHK, pMINGAP, pBIGSH, pDDS, pDDD, pINITB, pTRIG, pLAM,
    pRBPOL, pZAC, pZACR, pRBMODE;
unordered_map<int, int> typeIndex;
int typeSlotCount = 0;
int serviceId[MAXT], typeSize[MAXT], qv[MAXT], rv[MAXT], typeHead[MAXT];
ll F[MAXT];
ll PtC[MAXT];
unsigned char typePenaltyDirty[MAXT];
#define TBITS 1
ull TBit[TBITS ? (MAXT << 8) : 1];
#define TBSET(t, p) (TBit[((t) << 8) + ((p) >> 6)] |= 1ULL << ((p) & 63))
#define TBCLR(t, p) (TBit[((t) << 8) + ((p) >> 6)] &= ~(1ULL << ((p) & 63)))
RVEC(int) freeList;
int vacancyCount = 0;
int seedA[(MAXN << 2) + 16];
int nSeeds = 0, seedCap = 0;
ll thrM = 0;
SP2_I int dist(int u, int v) {
    int d = v - u;
    if (d <= 0)
        d += N;
    return d;
}
SP2_I int sdisp(int u, int w) {
    int d = w - u;
    int h = N >> 1;
    if (d > h)
        d -= N;
    else if (d < -h)
        d += N;
    return d;
}
ll mt[MAXT << 6];
ll wmt[MAXT << 6];
ll wrv[MAXT];
ll wdt[MAXT << 6];
const int TB = 512;
ll ctab0[TB], wctab0[TB];
int TBe = TB;
void buildNib(ll arr[], int b, ll v) {
    ll a = 0, c = 0, d = 0, v16 = v << 4, v256 = v << 8;
    for (int j = 0; j < 16; j++) {
        arr[b + j] = a;
        arr[b + 16 + j] = c;
        arr[b + 32 + j] = d;
        a += v;
        c += v16;
        d += v256;
    }
}
int stcMS[MAXT];
int stcN[MAXT], stcS[MAXT], stcQ[MAXT], stcR[MAXT];
ll stcF0[MAXT];
int stcWN[MAXT], stcWS[MAXT];
ll stcWF[MAXT];
int tb0N = 0, tb0S = 0, tb0WN = 0, tb0WS = 0;
ll tb0WF = 0;
void buildTab0() {
    if (tb0N == N && tb0S == typeSize[0]) {
        if (tb0WN == N && tb0WS == typeSize[0] && tb0WF == F[0])
            return;
        ll f = F[0];
        ll wv = -multiplyNonnegative(N, f), ws = multiplyNonnegative(typeSize[0], f);
        for (int g = 0; g < TBe; g++) {
            wctab0[g] = wv < 0 ? -wv : wv;
            wv += ws;
        }
        tb0WN = N;
        tb0WS = typeSize[0];
        tb0WF = f;
        return;
    }
    tb0N = N;
    tb0S = typeSize[0];
    tb0WN = N;
    tb0WS = typeSize[0];
    tb0WF = F[0];
    int te = qv[0] + qv[0] + qv[0] + 64;
    TBe = te < 260 ? 260 : (te > TB ? TB : te);
    if (TBe > N + 1 && N < 192)
        TBe = N + 1;
    if (typeSize[0] <= 1 || typeSize[0] >= N)
        TBe = TB;
    ll v = -(ll)N;
    for (int g = 0; g < TBe; g++) {
        ctab0[g] = v < 0 ? -v : v;
        v += typeSize[0];
    }
    ll f = F[0];
    ll wv = -multiplyNonnegative(N, f), ws = multiplyNonnegative(typeSize[0], f);
    for (int g = 0; g < TBe; g++) {
        wctab0[g] = wv < 0 ? -wv : wv;
        wv += ws;
    }
}
#define RM_HVK0 -1
#define RM_HVK1 -1
#define RM_HVK2 -1
#define RM_HVK3 -1
#define RM_LAM0 -1
#define RM_LAM1 -1
#define RM_LAM2 -1
#define RM_LAM3 -1
#define RM_TAUA0 -1
#define RM_TAUA1 -1
#define RM_TAUA2 -1
#define RM_TAUA3 -1
#define RM_H41 -1
#define RM_H42 -1
#define RM_H43 -1
#define RM_NOX1 -1
#define RM_NOX2 -1
#define RM_NOX3 -1
#define RM_VSW0 -1
#define RM_VSW1 -1
#define RM_VSW2 -1
#define RM_VSW3 -1
#define RM_NOREP3 0
int rmCls = 2;
SP2_I int rmPick(int k, int a0, int a1, int a2, int a3) {
    return k == 0 ? a0 : (k == 1 ? a1 : (k == 2 ? a2 : a3));
}
int ehV0k = 16;
int rmKOn = 0;
#define SDY_TWB 16
#define SDY_TWM 0
#define SDY_TWLO 8
#define SDY_TWHI 32
int sdyTw = 16;
#define SDY_VRL 0
#define SDY_VSH 1
#define SDY_VVH 4
#define SDY_VVW 4
#define SDY_VVR 1
#define SDY_ZX 0
#define SDY_ZXB 16
#define SDY_ZXM 0
#define SDY_ZXLO 4
#define SDY_ZXHI 64
int sdyLiveOp = -1, sdyLiveV = 0;
int sdyLive() {
    if (sdyLiveOp == operationStamp)
        return sdyLiveV;
    int m = 0;
    for (int t = 1; t < typeSlotCount; t++)
        m += typeSize[t] > 0;
    sdyLiveOp = operationStamp;
    sdyLiveV = m;
    return m;
}
int rmK[MAXT];
// 按该类型当前目标数量更新 gap 惩罚系数及相关查表。
void setType(int t) {
    int s = typeSize[t];
    int b = t << 6;
    if (stcMS[t] != s) {
        buildNib(mt, b, s);
        stcMS[t] = s;
    }
    if (s <= 1 || s >= N) {
        F[t] = 0;
        qv[t] = 0;
        rv[t] = 0;
    } else {
        if (stcN[t] == N && stcS[t] == s) {
            F[t] = stcF0[t];
            qv[t] = stcQ[t];
            rv[t] = stcR[t];
        } else {
            ll den = multiplyNonnegative(s - 1, N - s);
            F[t] = divideNonnegative(multiplyNonnegative(s, N) << 8, den);
            ll q = divideNonnegative(N, s);
            qv[t] = (int)q;
            rv[t] = (int)(N - multiplyNonnegative(q, s));
            stcN[t] = N;
            stcS[t] = s;
            stcF0[t] = F[t];
            stcQ[t] = qv[t];
            stcR[t] = rv[t];
        }
        if (t == 0 && ehV0k < 16)
            F[0] = multiplyNonnegative(F[0], ehV0k) >> 4;
        if (t != 0 && rmKOn && rmK[t] != 16)
            F[t] = multiplyNonnegative(F[t], rmK[t]) >> 4;
        if (SDY_TW && t != 0 && sdyTw != 16)
            F[t] = multiplyNonnegative(F[t], sdyTw) >> 4;
    }
    if (stcWN[t] == N && stcWS[t] == s && stcWF[t] == F[t]) {
        if (t == 0)
            buildTab0();
        return;
    }
    stcWN[t] = N;
    stcWS[t] = s;
    stcWF[t] = F[t];
    ll fs = multiplyNonnegative(s, F[t]);
    buildNib(wmt, b, fs);
    ll wr = multiplyNonnegative(rv[t], F[t]);
    wrv[t] = wr;
    {
        ll v = wr + (fs << 5);
        for (int k = 0; k <= 32; k++) {
            wdt[b + k] = v;
            v -= fs;
        }
        v = fs - wr;
        for (int k = 33; k < 64; k++) {
            wdt[b + k] = v;
            v += fs;
        }
    }
    if (t == 0)
        buildTab0();
}
SP2_I ll nibMul(const ll arr[], int b, int ak) {
    return arr[b + (ak & 15)] + arr[b + 16 + ((ak >> 4) & 15)] + arr[b + 32 + (ak >> 8)];
}
SP2_I ll cstg(int t, int g) {
    int k = g - qv[t];
    int ak = k < 0 ? -k : k;
    ll v = ak < 4096 ? nibMul(mt, t << 6, ak) : mulm(typeSize[t], ak);
    return k > 0 ? v - rv[t] : rv[t] + v;
}
SP2_I ll cst(int t, int g) {
    if (t == 0 && g < TBe)
        return ctab0[g];
    return cstg(t, g);
}
__attribute__((noinline)) ll wcstSlow(int t, int k) {
    return mulm(wmt[(t << 6) + 1], k);
}
#define SP_AI __attribute__((always_inline)) inline
SP_AI ll wcstg(int t, int g) {
    int k = g - qv[t];
    if ((unsigned)(k + 32) < 64u)
        return wdt[(t << 6) + k + 32];
    int ak = k < 0 ? -k : k;
    ll v = ak < 4096 ? nibMul(wmt, t << 6, ak) : wcstSlow(t, ak);
    return k > 0 ? v - wrv[t] : wrv[t] + v;
}
SP_AI ll wcst(int t, int g) {
    if (t == 0 && g < TBe)
        return wctab0[g];
    return wcstg(t, g);
}
int getIdx(int id) {
    auto it = typeIndex.find(id);
    if (it != typeIndex.end())
        return it->second;
    int t;
    if (!freeList.empty()) {
        t = freeList.back();
        freeList.pop_back();
    } else {
        t = typeSlotCount++;
        qv[t] = 0;
        rv[t] = 0;
    }
    serviceId[t] = id;
    typeSize[t] = 0;
    F[t] = 0;
    typeHead[t] = -1;
    typePenaltyDirty[t] = 1;
    if (TBITS)
        for (int w = 0; w < NW; w++)
            TBit[(t << 8) + w] = 0;
    typeIndex[id] = t;
    return t;
}
SP2_I void vbSet(int p) {
    int w = p >> 6;
    vb[w] |= (1ULL << (p & 63));
    vs[w >> 6] |= (1ULL << (w & 63));
}
SP2_I void vbClr(int p) {
    int w = p >> 6;
    vb[w] &= ~(1ULL << (p & 63));
    if (!vb[w])
        vs[w >> 6] &= ~(1ULL << (w & 63));
}
int prevWord(int w) {
    for (int pass = 0; pass < 2; pass++) {
        int hi = pass == 0 ? w - 1 : NW - 1;
        int lo = pass == 0 ? 0 : w;
        if (hi < lo)
            continue;
        int sw = hi >> 6, sb = hi & 63;
        ull m = vs[sw] & (sb == 63 ? ~0ULL : ((2ULL << sb) - 1));
        for (;;) {
            if (m) {
                int r = (sw << 6) + 63 - __builtin_clzll(m);
                return r >= lo ? r : -1;
            }
            sw--;
            if (sw < 0 || (sw << 6) + 63 < lo)
                break;
            m = vs[sw];
        }
    }
    return -1;
}
int nextWord(int w) {
    for (int pass = 0; pass < 2; pass++) {
        int lo = pass == 0 ? w + 1 : 0;
        int hi = pass == 0 ? NW - 1 : w;
        if (hi < lo)
            continue;
        int sw = lo >> 6, sb = lo & 63;
        ull m = vs[sw] & ~((1ULL << sb) - 1);
        for (;;) {
            if (m) {
                int r = (sw << 6) + __builtin_ctzll(m);
                return r <= hi ? r : -1;
            }
            sw++;
            if (sw > NS - 1 || (sw << 6) > hi)
                break;
            m = vs[sw];
        }
    }
    return -1;
}
__attribute__((noinline)) int prevVacSlow(int p) {
    int w = p >> 6;
    int w2 = prevWord(w);
    if (w2 < 0)
        return -1;
    if (w2 == w) {
        ull m = vb[w];
        return m ? (w << 6) + 63 - __builtin_clzll(m) : -1;
    }
    return (w2 << 6) + 63 - __builtin_clzll(vb[w2]);
}
__attribute__((noinline)) int nextVacSlow(int p) {
    int w = p >> 6;
    int w2 = nextWord(w);
    if (w2 < 0)
        return -1;
    if (w2 == w) {
        ull m = vb[w];
        return m ? (w << 6) + __builtin_ctzll(m) : -1;
    }
    return (w2 << 6) + __builtin_ctzll(vb[w2]);
}
SP2_I int prevVac(int p) {
    int w = p >> 6, b = p & 63;
    ull m = vb[w] & ((1ULL << b) - 1);
    if (m)
        return (w << 6) + 63 - __builtin_clzll(m);
    return prevVacSlow(p);
}
SP2_I int nextVac(int p) {
    int w = p >> 6, b = p & 63;
    ull m = vb[w] & ((~0ULL << b) << 1);
    if (m)
        return (w << 6) + __builtin_ctzll(m);
    return nextVacSlow(p);
}
SP2_I ull bitsAt(int pos) {
    int w = pos >> 6, sh = pos & 63;
    ull v = sh ? ((vb[w] >> sh) | (vb[w + 1] << (64 - sh))) : vb[w];
    int rem = N - pos;
    if (rem < 64)
        v |= vb[0] << rem;
    return v;
}
SP2_I ull lowMask(int k) {
    return k >= 64 ? ~0ULL : ((1ULL << k) - 1);
}
#define SX_VQ 8
void vacShort(int q, int &nle, ll &sle, int &first, int &last, int &cnt) {
    int ck[64];
    for (int k = 1; k <= q; k++)
        ck[k] = 0;
    first = -1;
    last = -1;
    cnt = 0;
    for (int w = 0; w < NW; w++) {
        const ull v = vb[w];
        if (!v)
            continue;
        if (first < 0)
            first = (w << 6) + __builtin_ctzll(v);
        last = (w << 6) + 63 - __builtin_clzll(v);
        cnt += __builtin_popcountll(v);
        const ull nx = vb[w + 1];
        ull z = v;
        for (int k = 1; k <= q; k++) {
            const ull e = (v >> k) | (nx << (64 - k));
            ck[k] += __builtin_popcountll(z & e);
            z &= ~e;
            if (!z)
                break;
        }
    }
    nle = 0;
    sle = 0;
    for (int k = 1; k <= q; k++) {
        nle += ck[k];
        sle += multiplyNonnegative(ck[k], k);
    }
}
ull xlsSB[(MAXN >> 6) + 2];
int xlsSBon = 0;
#define XSB(p_)                                                                                    \
    {                                                                                              \
        if (xlsSBon)                                                                               \
            xlsSB[(p_) >> 6] |= 1ULL << ((p_) & 63);                                               \
    }
SP2_I void markChange(int i) {
    if (changeStamp[i] != operationStamp) {
        changeStamp[i] = operationStamp;
        originalValue[i] = publicGrid[i];
        XSB(i)
    }
}
SP2_I int changedNow(int i) {
    return (changeStamp[i] == operationStamp && publicGrid[i] != originalValue[i]) ? 1 : 0;
}
SP2_I int changedIf(int i, int nv) {
    int o = changeStamp[i] == operationStamp ? originalValue[i] : publicGrid[i];
    return nv != o ? 1 : 0;
}
SP2_I int prvT(int i, int t) {
    return t ? prevSame[i] : prevVac(i);
}
SP2_I int nxtT(int i, int t) {
    return t ? nextSame[i] : nextVac(i);
}
#define XLS_HIA
XLS_HIA void unlinkCell(int i) {
    int t = slotType[i];
    if (t == 0) {
        vbClr(i);
        return;
    }
    int L = prevSame[i], R = nextSame[i];
    if (L == i) {
        typeHead[t] = -1;
        return;
    }
    nextSame[L] = R;
    prevSame[R] = L;
    if (typeHead[t] == i)
        typeHead[t] = R;
}
XLS_HIA void linkAfter(int i, int t, int L) {
    if (t == 0) {
        vbSet(i);
        return;
    }
    if (L < 0) {
        nextSame[i] = i;
        prevSame[i] = i;
        typeHead[t] = i;
        return;
    }
    int R = nextSame[L];
    nextSame[L] = i;
    prevSame[i] = L;
    nextSame[i] = R;
    prevSame[R] = i;
}
int findPrevT(int t, int p) {
    if (typeHead[t] < 0)
        return -1;
    int c = p;
    for (;;) {
        c--;
        if (c < 0)
            c += N;
        if (slotType[c] == t)
            return c;
    }
}
void setCell(int p, int nt, int L) {
    if (TBITS) {
        int ot = slotType[p];
        if (ot)
            TBCLR(ot, p);
        if (nt)
            TBSET(nt, p);
    }
    unlinkCell(p);
    markChange(p);
    slotType[p] = nt;
    publicGrid[p] = serviceId[nt];
    if (nt != 0 && L == -2)
        L = findPrevT(nt, p);
    linkAfter(p, nt, L);
}
SP2_I void freeCell(int p) {
    int t = slotType[p];
    int L = prevSame[p], R = nextSame[p];
    if (L == p)
        typeHead[t] = -1;
    else {
        nextSame[L] = R;
        prevSame[R] = L;
        if (typeHead[t] == p)
            typeHead[t] = R;
    }
    markChange(p);
    if (TBITS)
        TBCLR(t, p);
    slotType[p] = 0;
    publicGrid[p] = 0;
    vbSet(p);
}
bool findNb(int b, int u, int w, int &L, int &R) {
    int s = typeSize[b];
    if (s == 1) {
        L = -1;
        R = -1;
        return true;
    }
    int Lu = prvT(u, b), Ru = nxtT(u, b);
    if (s == 2) {
        L = Lu;
        R = Lu;
        return true;
    }
    if (dist(Lu, w) < dist(Lu, Ru)) {
        L = Lu;
        R = Ru;
        return true;
    }
    int d = sdisp(u, w);
    if (b == 0) {
        if (d > 0) {
            int c = prevVac(w);
            if (c == u)
                return false;
            L = c;
            R = nextVac(c);
            if (R == u)
                R = Ru;
        } else {
            int c = nextVac(w);
            if (c == u)
                return false;
            R = c;
            L = prevVac(c);
            if (L == u)
                L = Lu;
        }
        return true;
    }
    if (d > 0) {
        int c = w;
        for (int k = 0; k < d; k++) {
            c--;
            if (c < 0)
                c += N;
            if (slotType[c] == b && c != u)
                break;
        }
        if (slotType[c] != b || c == u)
            return false;
        L = c;
        R = nextSame[c];
        if (R == u)
            R = nextSame[u];
    } else {
        int c = w, dd = -d;
        for (int k = 0; k < dd; k++) {
            c++;
            if (c >= N)
                c -= N;
            if (slotType[c] == b && c != u)
                break;
        }
        if (slotType[c] != b || c == u)
            return false;
        R = c;
        L = prevSame[c];
        if (L == u)
            L = prevSame[u];
    }
    return true;
}
const ll INVALID = (ll)1 << 62;
SP_AI ll wcst2(int t, int g1, int g2);
#define SP3_W4(t, a, b, c, d) (wcst2((t), (a), (b)) - wcst2((t), (c), (d)))
XLS_HIA bool findNbFar(int b, int u, int w, int Lu, int Ru, int &L, int &R);
XLS_HIA bool findNbF(int b, int u, int w, int &L, int &R);
// 移动一个颗粒的局部惩罚差：旧位置合并 gap，新位置拆分 gap。
ll dMoveW(int b, int u, int w) {
    int s = typeSize[b];
    if (s <= 1 || F[b] == 0)
        return 0;
    int Lu = prvT(u, b), Ru = nxtT(u, b);
    if (s >= 3) {
        int g1 = dist(Lu, u), g2 = dist(u, Ru);
        int gw = dist(Lu, w);
        if (gw < g1 + g2)
            return SP3_W4(b, gw, g1 + g2 - gw, g1, g2);
        if (TBITS) {
            int L, R;
            if (!findNbFar(b, u, w, Lu, Ru, L, R))
                return INVALID;
            return (wcst(b, g1 + g2) - wcst(b, g1) - wcst(b, g2)) +
                   (wcst(b, dist(L, w)) + wcst(b, dist(w, R)) - wcst(b, dist(L, R)));
        }
    }
    ll rem;
    if (s == 2)
        rem = wcst(b, N) - wcst(b, dist(Lu, u)) - wcst(b, dist(u, Lu));
    else
        rem = wcst(b, dist(Lu, Ru)) - wcst(b, dist(Lu, u)) - wcst(b, dist(u, Ru));
    int L, R;
    if (!findNb(b, u, w, L, R))
        return INVALID;
    ll ins;
    if (s == 2)
        ins = wcst(b, dist(L, w)) + wcst(b, dist(w, L)) - wcst(b, N);
    else
        ins = wcst(b, dist(L, w)) + wcst(b, dist(w, R)) - wcst(b, dist(L, R));
    return rem + ins;
}
__attribute__((always_inline)) inline ll dMoveWI(int b, int u, int w) {
    const int s = typeSize[b];
    if (s <= 1 || F[b] == 0)
        return 0;
    if (s >= 3) {
        int Lu = prvT(u, b), Ru = nxtT(u, b);
        int g1 = dist(Lu, u), g2 = dist(u, Ru);
        int gw = dist(Lu, w);
        if (gw < g1 + g2)
            return SP3_W4(b, gw, g1 + g2 - gw, g1, g2);
        if (TBITS) {
            int L, R;
            if (!findNbFar(b, u, w, Lu, Ru, L, R))
                return INVALID;
            return (wcst(b, g1 + g2) - wcst(b, g1) - wcst(b, g2)) +
                   (wcst(b, dist(L, w)) + wcst(b, dist(w, R)) - wcst(b, dist(L, R)));
        }
    }
    return dMoveW(b, u, w);
}
// 执行不同类型位置交换，同时维护环链、空位位图和改动记录。
void doSwap(int i, int j) {
    int a = slotType[i], b = slotType[j];
    typePenaltyDirty[a] = 1;
    typePenaltyDirty[b] = 1;
    int La = -1, Ra = -1, Lb = -1, Rb = -1;
    if (TBITS) {
        if (a != 0 && typeSize[a] >= 2)
            findNbF(a, i, j, La, Ra);
        if (b != 0 && typeSize[b] >= 2)
            findNbF(b, j, i, Lb, Rb);
    } else {
        if (a != 0 && typeSize[a] >= 2)
            findNb(a, i, j, La, Ra);
        if (b != 0 && typeSize[b] >= 2)
            findNb(b, j, i, Lb, Rb);
    }
    unlinkCell(i);
    unlinkCell(j);
    markChange(i);
    markChange(j);
    if (TBITS) {
        if (a) {
            TBCLR(a, i);
            TBSET(a, j);
        }
        if (b) {
            TBCLR(b, j);
            TBSET(b, i);
        }
    }
    slotType[i] = b;
    slotType[j] = a;
    int g = publicGrid[i];
    publicGrid[i] = publicGrid[j];
    publicGrid[j] = g;
    linkAfter(j, a, La);
    linkAfter(i, b, Lb);
}
