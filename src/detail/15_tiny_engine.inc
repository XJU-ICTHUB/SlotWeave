// 极小圆环的专用搜索器。以完整邻接信息、局部下降和有节点上限的分支定界探索更多合法布局。
// Included in fixed order by solution.cpp.

#define TE_H04 6
#define TE_HCAP4 8
#define TE_HCAPA 6
#define TE_HCAPC 10
#define TE_HN1 12
#define TE_HN2 64
#define TE_HSH 2
#define TE_ILSE 4000000
#define TE_INODES 2000000
#define TE_IRS 40
#define TE_LSE 8000
#define TE_NB 12
#define TE_NF 12
#define TE_NODES 5000
#define TE_NT 100
#define TE_P 24
#define TE_SEEDX 1
#define TE_W 8
#define TE_NTA 12
#define TE_NTB 101
#include <vector>
#include <utility>
#include <algorithm>
namespace tiny_search {
using std::vector;
using std::pair;
typedef long long ll;
inline ll multiplyNonnegative(ll a, ll b) {
    ll r = 0;
    while (b) {
        if (b & 1)
            r += a;
        a <<= 1;
        b >>= 1;
    }
    return r;
}
inline ll divideNonnegative(ll a, ll b) {
    if (a < b)
        return 0;
    int sh = 0;
    while (sh < 60 && (b << (sh + 1)) <= a)
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
int N = 0, nS = 1, nops = 0;
vector<int> publicGrid;
vector<int> slotType, OT;
vector<int> sid, typeSize, lc;
vector<ll> WH;
vector<int> tcS;
vector<ll> tcH;
vector<ll> TCf;
vector<int> PLf, NRf;
vector<int> toff, roff;
vector<int> live;
vector<ll> BMk;
vector<int> seedQ, inq;
vector<ll> gsc;
vector<int> cand;
ll BM = 0;
ll BMd[5];
void setBMd() {
    BMd[0] = -(BM << 1);
    BMd[1] = -BM;
    BMd[2] = 0;
    BMd[3] = BM;
    BMd[4] = BM << 1;
}
ll lsEvals = 0;
inline int dist(int u, int v) {
    int d = v - u;
    return d + (N & ((d - 1) >> 31));
}
void ensureSlots(int n) {
    while ((int)sid.size() < n) {
        sid.push_back(0);
        typeSize.push_back(0);
        lc.push_back(0);
        WH.push_back(0);
        tcS.push_back(-1);
        tcH.push_back(-1);
        toff.push_back((int)TCf.size());
        TCf.resize(TCf.size() + N + 1, 0);
        roff.push_back((int)PLf.size());
        PLf.resize(PLf.size() + N, -1);
        NRf.resize(NRf.size() + N, -1);
    }
}
int findSlot(int id) {
    for (int t = 1; t < nS; t++)
        if (typeSize[t] > 0 && sid[t] == id)
            return t;
    return -1;
}
int newSlot(int id) {
    for (int t = 1; t < nS; t++)
        if (typeSize[t] == 0 && lc[t] == 0) {
            sid[t] = id;
            return t;
        }
    nS++;
    ensureSlots(nS);
    sid[nS - 1] = id;
    typeSize[nS - 1] = 0;
    lc[nS - 1] = 0;
    return nS - 1;
}
void buildRow(int t) {
    int o = roff[t];
    int last = -1, first = -1;
    for (int j = N - 1; j >= 0; j--)
        if (slotType[j] == t) {
            last = j;
            break;
        }
    if (last < 0)
        return;
    for (int j = 0; j < N; j++)
        if (slotType[j] == t) {
            first = j;
            break;
        }
    int cur = last;
    for (int j = 0; j < N; j++) {
        PLf[o + j] = cur;
        if (slotType[j] == t)
            cur = j;
    }
    cur = first;
    for (int j = N - 1; j >= 0; j--) {
        NRf[o + j] = cur;
        if (slotType[j] == t)
            cur = j;
    }
}
void rebuildAll() {
    for (int t = 0; t < nS; t++)
        lc[t] = 0;
    for (int j = 0; j < N; j++)
        lc[slotType[j]]++;
    for (int t = 0; t < nS; t++)
        if (lc[t] > 0)
            buildRow(t);
}
void rowsInsert(int t, int j) {
    int o = roff[t];
    if (lc[t] == 0) {
        for (int k = 0; k < N; k++) {
            PLf[o + k] = j;
            NRf[o + k] = j;
        }
        return;
    }
    int p = PLf[o + j], n = NRf[o + j], k = j;
    do {
        k++;
        if (k >= N)
            k = 0;
        PLf[o + k] = j;
    } while (k != n);
    k = j;
    do {
        k--;
        if (k < 0)
            k = N - 1;
        NRf[o + k] = j;
    } while (k != p);
}
void rowsErase(int t, int j) {
    if (lc[t] <= 1)
        return;
    int o = roff[t];
    int p = PLf[o + j], n = NRf[o + j], k = j;
    do {
        k++;
        if (k >= N)
            k = 0;
        PLf[o + k] = p;
    } while (k != n);
    k = j;
    do {
        k--;
        if (k < 0)
            k = N - 1;
        NRf[o + k] = n;
    } while (k != p);
}
void setCell(int p, int t) {
    int o = slotType[p];
    if (o == t)
        return;
    rowsErase(o, p);
    lc[o]--;
    rowsInsert(t, p);
    lc[t]++;
    slotType[p] = t;
}
void buildTC(int t, ll H4) {
    int s = typeSize[t];
    tcS[t] = s;
    tcH[t] = H4;
    ll hq = (H4 << 3) + (H4 << 1) + H4;
    ll w = 0;
    if (s >= 2 && s < N)
        w = multiplyNonnegative(divideNonnegative((ll)s << TE_P, multiplyNonnegative(s - 1, N - s)),
                                hq);
    WH[t] = w;
    int o = toff[t];
    if (w == 0) {
        for (int g = 0; g <= N; g++)
            TCf[o + g] = 0;
        return;
    }
    ll acc = -multiplyNonnegative(w, N), step = multiplyNonnegative(w, s);
    for (int g = 0; g <= N; g++) {
        TCf[o + g] = acc < 0 ? -acc : acc;
        acc += step;
    }
}
void setWeights(int K, ll H4) {
    live.clear();
    for (int t = 0; t < nS; t++) {
        if (typeSize[t] <= 0) {
            WH[t] = 0;
            tcS[t] = -1;
            continue;
        }
        live.push_back(t);
        if (tcS[t] != typeSize[t] || tcH[t] != H4)
            buildTC(t, H4);
    }
    BM = N > K ? divideNonnegative(multiplyNonnegative((ll)N, 56) << TE_P, (ll)(N - K)) : 0;
    if ((int)BMk.size() != N + 2)
        BMk.assign(N + 2, 0);
    ll acc = 0;
    for (int k = 0; k <= N + 1; k++) {
        BMk[k] = acc;
        acc += BM;
    }
    setBMd();
}
inline ll remD(int t, int i) {
    int to = toff[t];
    if (lc[t] == 1)
        return -TCf[to + N];
    int ro = roff[t];
    int p = PLf[ro + i], n = NRf[ro + i];
    return TCf[to + dist(p, n)] - TCf[to + dist(p, i)] - TCf[to + dist(i, n)];
}
inline ll insD(int t, int j) {
    int to = toff[t];
    if (lc[t] == 0)
        return TCf[to + N];
    int ro = roff[t];
    int p = PLf[ro + j], n = NRf[ro + j];
    return TCf[to + dist(p, j)] + TCf[to + dist(j, n)] - TCf[to + dist(p, n)];
}
inline ll moveD(int t, int i, int j) {
    if (lc[t] <= 1 || WH[t] == 0)
        return 0;
    int to = toff[t], ro = roff[t];
    int p = PLf[ro + i], n = NRf[ro + i];
    ll d = TCf[to + dist(p, n)] - TCf[to + dist(p, i)] - TCf[to + dist(i, n)];
    int pj = PLf[ro + j];
    if (pj == i)
        pj = p;
    int nj = NRf[ro + j];
    if (nj == i)
        nj = n;
    d += TCf[to + dist(pj, j)] + TCf[to + dist(j, nj)] - TCf[to + dist(pj, nj)];
    return d;
}
inline ll moveLS(int t, int i, int j) {
    int to = toff[t], ro = roff[t];
    int p = PLf[ro + i], n = NRf[ro + i];
    int pj = PLf[ro + j];
    pj = pj == i ? p : pj;
    int nj = NRf[ro + j];
    nj = nj == i ? n : nj;
    return TCf[to + dist(p, n)] - TCf[to + dist(p, i)] - TCf[to + dist(i, n)] +
           TCf[to + dist(pj, j)] + TCf[to + dist(j, nj)] - TCf[to + dist(pj, nj)];
}
inline ll swapD(int i, int j) {
    int a = slotType[i], b = slotType[j];
    ll d = moveD(a, i, j) + moveD(b, j, i);
    int oi = OT[i], oj = OT[j];
    int dm = (b != oi ? 1 : 0) - (a != oi ? 1 : 0) + (a != oj ? 1 : 0) - (b != oj ? 1 : 0);
    if (dm > 0)
        d += BMk[dm];
    else if (dm < 0)
        d -= BMk[-dm];
    return d;
}
inline void doSwap(int i, int j) {
    int a = slotType[i], b = slotType[j];
    setCell(i, b);
    setCell(j, a);
}
ll totalCost() {
    vector<int> f(nS, -1), l(nS, -1);
    ll c = 0;
    for (int j = 0; j < N; j++) {
        int t = slotType[j];
        if (l[t] >= 0)
            c += TCf[toff[t] + j - l[t]];
        else
            f[t] = j;
        l[t] = j;
        if (t != OT[j])
            c += BM;
    }
    for (int t = 0; t < nS; t++)
        if (l[t] >= 0)
            c += TCf[toff[t] + f[t] + N - l[t]];
    return c;
}
void lsFull(ll budget) {
    bool imp = true;
    while (imp && lsEvals < budget) {
        imp = false;
        for (int i = 0; i < N && lsEvals < budget; i++) {
            for (int j = i + 1; j < N; j++) {
                if (slotType[i] == slotType[j])
                    continue;
                lsEvals++;
                if (swapD(i, j) < 0) {
                    doSwap(i, j);
                    imp = true;
                }
            }
        }
    }
}
inline void pushSeed(int i) {
    if (!inq[i]) {
        inq[i] = 1;
        seedQ.push_back(i);
    }
}
void lsSeeds(ll budget, int W) {
    if (W > ((N - 1) >> 1))
        W = (N - 1) >> 1;
    size_t h = 0;
    while (h < seedQ.size() && lsEvals < budget) {
        int i = seedQ[h++];
        inq[i] = 0;
        bool acc = false, stale = true;
        int a = 0, ta = 0, ra = 0, pa = 0, na = 0, oi = OT[i];
        bool am = false;
        ll remA = 0;
        int j = i - W;
        if (j < 0)
            j += N;
        for (int d = -W; d <= W; d++, j++) {
            if (j >= N)
                j -= N;
            if (stale) {
                a = slotType[i];
                ta = toff[a];
                ra = roff[a];
                am = lc[a] > 1 && WH[a] != 0;
                if (am) {
                    pa = PLf[ra + i];
                    na = NRf[ra + i];
                    remA = TCf[ta + dist(pa, na)] - TCf[ta + dist(pa, i)] - TCf[ta + dist(i, na)];
                }
                stale = false;
            }
            int bt = slotType[j];
            if (d == 0 || bt == a)
                continue;
            lsEvals++;
            ll D = moveLS(bt, j, i);
            if (am) {
                int pj = PLf[ra + j];
                if (pj == i)
                    pj = pa;
                int nj = NRf[ra + j];
                if (nj == i)
                    nj = na;
                D += remA + TCf[ta + dist(pj, j)] + TCf[ta + dist(j, nj)] - TCf[ta + dist(pj, nj)];
            }
            int oj = OT[j];
            D += BMd[2 + (bt != oi ? 1 : 0) - (a != oi ? 1 : 0) + (a != oj ? 1 : 0) -
                     (bt != oj ? 1 : 0)];
            if (D < 0) {
                doSwap(i, j);
                acc = true;
                stale = true;
                pushSeed(j);
            }
        }
        if (acc)
            pushSeed(i);
    }
    for (size_t k = h; k < seedQ.size(); k++)
        inq[seedQ[k]] = 0;
    seedQ.clear();
}
const int TE_NBMAX = 16;
ll SPA[TE_NBMAX + 8][TE_NBMAX + 1][TE_NBMAX + 1];
vector<int> bT, cT, fst, lst, rem, suf, ord0;
ll bestC = 0, part = 0, nodes = 0, nodeCap = 0;
int mlb = 0;
void buildSPL() {
    for (int li = 0; li < (int)live.size(); li++) {
        int t = live[li];
        int s = typeSize[t];
        int to = toff[t];
        for (int k = 1; k <= s; k++) {
            for (int D = 0; D <= N; D++)
                SPA[t][k][D] = 0;
            ll c = 0;
            for (int u = 0; u < k; u++)
                c += TCf[to + 1];
            int q = 1, r = 0;
            SPA[t][k][k] = c;
            for (int D = k; D < N; D++) {
                c += TCf[to + q + 1] - TCf[to + q];
                SPA[t][k][D + 1] = c;
                r++;
                if (r == k) {
                    r = 0;
                    q++;
                }
            }
        }
    }
}
inline int mterm(int t) {
    int v = suf[t] - rem[t];
    return v > 0 ? v : 0;
}
inline ll lbTight(int u, int p1) {
    int k, D, a;
    if (lst[u] < 0) {
        k = typeSize[u];
        D = N;
        a = p1 + 1;
    } else {
        k = rem[u] + 1;
        D = fst[u] + N - lst[u];
        a = p1 - lst[u];
    }
    if (k <= 1)
        return SPA[u][1][D];
    if (a >= 2 && a <= D - (k - 1)) {
        int to = toff[u];
        ll ha = TCf[to + a] + SPA[u][k - 1][D - a];
        ll hb = TCf[to + a - 1] + SPA[u][k - 1][D - a + 1];
        if (ha > hb)
            return ha;
    }
    return SPA[u][k][D];
}
int fixFirst = -1;
void dfs(int p) {
    if (nodes >= nodeCap)
        return;
    nodes++;
    if (p == N) {
        if (part < bestC) {
            bestC = part;
            bT = cT;
        }
        return;
    }
    int o = OT[p];
    int first0 = ord0[p];
    int nl = (int)live.size();
    ll S = 0;
    for (int k = 0; k < nl; k++) {
        int u = live[k];
        if (rem[u] > 0)
            S += lbTight(u, p + 1);
    }
    for (int k = -2; k < nl; k++) {
        int t;
        if (k == -2)
            t = first0;
        else if (k == -1) {
            t = o;
            if (t == first0)
                continue;
        } else {
            t = live[k];
            if (t == first0 || t == o)
                continue;
        }
        if (t < 0 || rem[t] <= 0)
            continue;
        if (p == 0 && fixFirst >= 0 && t != fixFirst)
            continue;
        ll lt0 = lbTight(t, p + 1);
        ll add = t != o ? BM : 0;
        int of = fst[t], ol = lst[t];
        if (ol >= 0)
            add += TCf[toff[t] + p - ol];
        else
            fst[t] = p;
        lst[t] = p;
        int before = mterm(o) + (t != o ? mterm(t) : 0);
        rem[t]--;
        suf[o]--;
        int after = mterm(o) + (t != o ? mterm(t) : 0);
        ll nlb;
        if (rem[t] == 0) {
            add += TCf[toff[t] + fst[t] + N - p];
            nlb = 0;
        } else
            nlb = SPA[t][rem[t] + 1][fst[t] + N - p];
        int nm = mlb - before + after;
        if (part + add + (S - lt0 + nlb) + BMk[nm] < bestC) {
            part += add;
            mlb = nm;
            cT[p] = t;
            dfs(p + 1);
            part -= add;
            mlb = nm - after + before;
        }
        rem[t]++;
        suf[o]++;
        fst[t] = of;
        lst[t] = ol;
        if (nodes >= nodeCap)
            return;
    }
}
// 有节点上限的分支定界入口；在已固定位置之外继续搜索并记录最好布局。
void bnb(ll cap, int fix0) {
    if (N > TE_NBMAX || nS > TE_NBMAX + 8)
        return;
    buildSPL();
    bT = slotType;
    cT = slotType;
    ord0 = slotType;
    bestC = totalCost();
    fst.assign(nS, -1);
    lst.assign(nS, -1);
    rem.assign(nS, 0);
    suf.assign(nS, 0);
    for (int li = 0; li < (int)live.size(); li++) {
        int t = live[li];
        rem[t] = typeSize[t];
    }
    for (int j = 0; j < N; j++)
        suf[OT[j]]++;
    mlb = 0;
    for (int t = 0; t < nS; t++)
        mlb += mterm(t);
    part = 0;
    nodes = 0;
    nodeCap = cap;
    fixFirst = fix0;
    if (fix0 >= 0)
        ord0[0] = fix0;
    dfs(0);
    fixFirst = -1;
    bool ch = false;
    for (int j = 0; j < N; j++)
        if (slotType[j] != bT[j]) {
            slotType[j] = bT[j];
            ch = true;
        }
    if (ch)
        rebuildAll();
}
void writeG() {
    for (int j = 0; j < N; j++)
        publicGrid[j] = sid[slotType[j]];
}
ll horizon4() {
    ll h = (ll)TE_H04 + ((ll)nops << TE_HSH);
    ll cap = N <= TE_HN1 ? TE_HCAPA : (N <= TE_HN2 ? TE_HCAP4 : TE_HCAPC);
    if (h > cap)
        h = cap;
    if (h < 1)
        h = 1;
    return h;
}
void improve(int x) {
    lsEvals = 0;
    if (N <= TE_NF)
        lsFull(TE_LSE);
    else {
        if ((int)inq.size() < N)
            inq.assign(N, 0);
        if (TE_SEEDX) {
            for (int j = 0; j < N; j++)
                if (slotType[j] != OT[j] || slotType[j] == x)
                    pushSeed(j);
        } else {
            for (int j = 0; j < N; j++)
                if (slotType[j] != OT[j]) {
                    pushSeed(j);
                    int t = slotType[j], o = OT[j];
                    if (lc[t] > 1) {
                        pushSeed(PLf[roff[t] + j]);
                        pushSeed(NRf[roff[t] + j]);
                    }
                    if (lc[o] > 0) {
                        pushSeed(PLf[roff[o] + j]);
                        pushSeed(NRf[roff[o] + j]);
                    }
                }
        }
        lsSeeds(TE_LSE, TE_W);
    }
    if (N <= TE_NB && N >= 2)
        bnb(TE_NODES, -1);
}
inline int xrand(unsigned int &st, int n) {
    unsigned int m = 1;
    while ((int)m < n)
        m = (m << 1) | 1;
    while (true) {
        st ^= st << 13;
        st ^= st >> 17;
        st ^= st << 5;
        int r = (int)(st & m);
        if (r < n)
            return r;
    }
}
// 初始化极小规模搜索器的类型索引、代价表和合法初始布局。
void eInit(int n, const vector<pair<int, int> > &services) {
    N = n;
    nS = 1;
    nops = 0;
    sid.clear();
    typeSize.clear();
    lc.clear();
    WH.clear();
    tcS.clear();
    tcH.clear();
    TCf.clear();
    PLf.clear();
    NRf.clear();
    toff.clear();
    roff.clear();
    BMk.clear();
    seedQ.clear();
    inq.assign(N, 0);
    gsc.assign(N, 0);
    ensureSlots(1);
    sid[0] = 0;
    publicGrid.assign(N, 0);
    slotType.assign(N, 0);
    OT.assign(N, 0);
    int used = 0;
    for (int i = 0; i < (int)services.size(); i++) {
        int id = services[i].first, c = services[i].second;
        if (c <= 0 || id == 0 || used + c > N)
            continue;
        int t = findSlot(id);
        if (t < 0)
            t = newSlot(id);
        typeSize[t] += c;
        used += c;
    }
    typeSize[0] = N - used;
    vector<pair<int, int> > ord;
    for (int t = 0; t < nS; t++)
        if (typeSize[t] > 0)
            ord.push_back(pair<int, int>(-typeSize[t], t));
    std::sort(ord.begin(), ord.end());
    vector<int> fr(N), keep;
    for (int j = 0; j < N; j++) {
        fr[j] = j;
        slotType[j] = -1;
    }
    int F = N;
    for (int oi = 0; oi < (int)ord.size(); oi++) {
        int t = ord[oi].second, s = typeSize[t];
        int acc = 0;
        keep.clear();
        for (int u = 0; u < F; u++) {
            acc += s;
            if (acc >= F) {
                acc -= F;
                slotType[fr[u]] = t;
            } else
                keep.push_back(fr[u]);
        }
        F = (int)keep.size();
        for (int u = 0; u < F; u++)
            fr[u] = keep[u];
    }
    for (int j = 0; j < N; j++)
        if (slotType[j] < 0)
            slotType[j] = 0;
    OT = slotType;
    int fix0 = ord.empty() ? -1 : ord[0].second;
    if (N >= 2) {
        setWeights(0, 4);
        BM = 0;
        for (int k = 0; k < (int)BMk.size(); k++)
            BMk[k] = 0;
        setBMd();
        rebuildAll();
        lsEvals = 0;
        lsFull(TE_ILSE);
        if (N <= TE_NB)
            bnb(TE_INODES, fix0);
        else if (TE_IRS > 0) {
            vector<int> bestT = slotType;
            ll bestV = totalCost();
            unsigned int rs = 2463534242u + (unsigned int)N;
            int P = (N >> 3) + 2;
            for (int it = 0; it < TE_IRS; it++) {
                for (int k = 0; k < P; k++) {
                    int i = xrand(rs, N), j = xrand(rs, N);
                    if (slotType[i] != slotType[j]) {
                        int a2 = slotType[i];
                        slotType[i] = slotType[j];
                        slotType[j] = a2;
                    }
                }
                rebuildAll();
                lsEvals = 0;
                lsFull(TE_ILSE);
                ll v = totalCost();
                if (v < bestV) {
                    bestV = v;
                    bestT = slotType;
                } else
                    slotType = bestT;
            }
            slotType = bestT;
        }
    }
    rebuildAll();
    writeG();
}
// 极小规模的增加入口：更新目标数量后，用局部搜索和分支定界改进。
void eAdd(int id, int count) {
    int fr = typeSize[0];
    int K = count < fr ? count : fr;
    if (count <= 0 || id == 0)
        K = 0;
    OT = slotType;
    int x = -1;
    if (K > 0) {
        x = findSlot(id);
        if (x < 0)
            x = newSlot(id);
        typeSize[x] += K;
        typeSize[0] -= K;
    }
    setWeights(K, horizon4());
    if (N >= 2) {
        if (K > 0) {
            int rx = roff[x];
            cand.clear();
            for (int v = 0; v < N; v++)
                if (slotType[v] == 0)
                    cand.push_back(v);
            bool all = true;
            for (int k = 0; k < K; k++) {
                int nc = (int)cand.size();
                if (all) {
                    for (int u = 0; u < nc; u++) {
                        int v = cand[u];
                        gsc[v] = insD(x, v) + remD(0, v);
                    }
                    all = false;
                }
                int bu = 0;
                ll bd = gsc[cand[0]];
                for (int u = 1; u < nc; u++) {
                    ll d = gsc[cand[u]];
                    if (d < bd) {
                        bd = d;
                        bu = u;
                    }
                }
                int bv = cand[bu];
                cand.erase(cand.begin() + bu);
                bool firstX = lc[x] == 0;
                int pv = PLf[roff[0] + bv], nv = NRf[roff[0] + bv];
                setCell(bv, x);
                if (k + 1 == K)
                    break;
                if (firstX || lc[0] <= 2) {
                    all = true;
                    continue;
                }
                int px = PLf[rx + bv], nx = NRf[rx + bv];
                for (int j = px + 1;; j++) {
                    if (j >= N)
                        j -= N;
                    if (j == nx)
                        break;
                    if (slotType[j] == 0)
                        gsc[j] = insD(x, j) + remD(0, j);
                }
                gsc[pv] = insD(x, pv) + remD(0, pv);
                gsc[nv] = insD(x, nv) + remD(0, nv);
            }
        }
        improve(x);
    } else if (K > 0) {
        setCell(0, x);
    }
    nops++;
    writeG();
}
// 极小规模的删除入口：处理截断数量，并重建受影响的局部代价。
void eRemove(int id, int count) {
    int x = id == 0 ? -1 : findSlot(id);
    int K = 0;
    if (x >= 0 && count > 0)
        K = count < typeSize[x] ? count : typeSize[x];
    OT = slotType;
    if (K > 0) {
        typeSize[x] -= K;
        typeSize[0] += K;
    }
    setWeights(K, horizon4());
    if (K > 0) {
        if (typeSize[x] == 0) {
            for (int j = 0; j < N; j++)
                if (slotType[j] == x)
                    setCell(j, 0);
        } else {
            int r0 = roff[0], rx = roff[x];
            cand.clear();
            for (int i = 0; i < N; i++)
                if (slotType[i] == x)
                    cand.push_back(i);
            bool all = true;
            for (int k = 0; k < K; k++) {
                int nc = (int)cand.size();
                if (all) {
                    for (int u = 0; u < nc; u++) {
                        int i = cand[u];
                        gsc[i] = remD(x, i) + insD(0, i);
                    }
                    all = false;
                }
                int bu = 0;
                ll bd = gsc[cand[0]];
                for (int u = 1; u < nc; u++) {
                    ll d = gsc[cand[u]];
                    if (d < bd) {
                        bd = d;
                        bu = u;
                    }
                }
                int bi = cand[bu];
                cand.erase(cand.begin() + bu);
                bool first0 = lc[0] == 0;
                int px = PLf[rx + bi], nx = NRf[rx + bi];
                setCell(bi, 0);
                if (k + 1 == K)
                    break;
                if (first0 || lc[x] <= 2) {
                    all = true;
                    continue;
                }
                int pv = PLf[r0 + bi], nv = NRf[r0 + bi];
                for (int j = pv + 1;; j++) {
                    if (j >= N)
                        j -= N;
                    if (j == nv)
                        break;
                    if (slotType[j] == x)
                        gsc[j] = remD(x, j) + insD(0, j);
                }
                gsc[px] = remD(x, px) + insD(0, px);
                gsc[nx] = remD(x, nx) + insD(0, nx);
            }
        }
    }
    if (N >= 2)
        improve(K > 0 && typeSize[x] > 0 ? x : -1);
    nops++;
    writeG();
}
} // namespace tiny_search
