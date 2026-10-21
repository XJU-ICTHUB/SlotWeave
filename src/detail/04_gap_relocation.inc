// 同类颗粒和空位的局部迁移。统一考虑移出类型、移入类型与稳定性成本，修复过密或过疏区间。
// Included in fixed order by solution.cpp.

#define RQ_SMAX 100000
#define RQ_WB 0
#define RQ_CW 100000
#define RQ_HOT 0
#define RQ_GATE 0
#define RQ_SWK 0
#define RQ_SWN 3
#define RQ_SWH 8
#define RQ_SWW 4
#define RQ_SWV 1
#define RQ_PBSH 5
#define RQ_UPD 0
#define RQ_PIT 1
ll totalLayoutPenalty();
const int RQW_MAX = 8;
int rqA[MAXN];
ll rqNCf[(MAXN << 4) + MAXN];
int rqOff[MAXN], rqPart[MAXN];
unsigned char rqCh[MAXN][(RQW_MAX << 1) + 1];
unsigned char rqAct[MAXN];
int rqLo[MAXN], rqHi[MAXN];
int rqChg[MAXT];
ll rqWork = 0;
ll rqWBv = RQ_WB;
int rqActM = 0, rqBud = 0, rqActR = RQ_ACT;
int rqStG = 0;
int rqTSt[MAXT];
ll rqTIV[MAXT];
SP2_I ll rqMoveW(int y, int b, int a) {
    const int s = typeSize[y];
    if (s <= 1 || F[y] == 0)
        return 0;
    if (s == 2)
        return dMoveW(y, b, a);
    int Lu = prvT(b, y), Ru = nxtT(b, y);
    int g1 = dist(Lu, b), g2 = dist(b, Ru);
    int gw = dist(Lu, a);
    if (gw < g1 + g2)
        return wcst(y, gw) + wcst(y, g1 + g2 - gw) - wcst(y, g1) - wcst(y, g2);
    if (rqTSt[y] != rqStG) {
        rqTSt[y] = rqStG;
        int L, R;
        if (!findNb(y, b, a, L, R))
            rqTIV[y] = INVALID;
        else
            rqTIV[y] = wcst(y, dist(L, a)) + wcst(y, dist(a, R)) - wcst(y, dist(L, R));
    }
    if (rqTIV[y] == INVALID)
        return INVALID;
    return wcst(y, dist(Lu, Ru)) - wcst(y, dist(Lu, b)) - wcst(y, dist(b, Ru)) + rqTIV[y];
}
int zchMask = 0;
// 沿目标附近寻找更合适的同类位置，计算完整局部移动收益。
__attribute__((noinline)) int relat(int x, int w, ll thr) {
    int s = typeSize[x];
    if (s < 3 || F[x] == 0 || w < 1 || N < 8)
        return 0;
    if (w > RQW_MAX)
        w = RQW_MAX;
    int k = 0;
    for (int ww = 0; ww < NW; ww++) {
        ull m = x ? TBit[(x << 8) + ww] : vb[ww];
        while (m) {
            rqA[k++] = (ww << 6) + __builtin_ctzll(m);
            m &= m - 1;
        }
    }
    if (k != s)
        return 0;
    if (RQ_GATE) {
        ll cur0 = 0;
        for (int j = 1; j < s; j++)
            cur0 += wcst(x, rqA[j] - rqA[j - 1]);
        cur0 += wcst(x, rqA[0] + N - rqA[s - 1]);
        ll r = rv[x];
        ll pmin = multiplyNonnegative(multiplyNonnegative(r, s - r) << 1, F[x]);
        if (cur0 - pmin <= multiplyNonnegative(thr, RQ_GATE) >> 4)
            return 0;
    }
    int W = (w << 1) + 1;
    const ll INF = (ll)1 << 60;
    int nact = 0;
    if (RQ_ACT > 0) {
        const int q = qv[x];
        for (int j = 0; j < s; j++)
            rqAct[j] = 0;
        int last = -1000000;
        for (int j = 0; j < s; j++) {
            int g = (j + 1 < s ? rqA[j + 1] : rqA[0] + N) - rqA[j];
            bool hot;
            if (rqActM == 1) {
                int cj = rqA[j];
                hot = changeStamp[cj] == operationStamp && publicGrid[cj] != originalValue[cj];
            } else if (rqActM == 2) {
                hot = g < q - RQ_HOT || g > q + 1 + RQ_HOT;
                if (hot) {
                    int cj = rqA[j], cn = j + 1 < s ? rqA[j + 1] : rqA[0];
                    hot =
                        (changeStamp[cj] == operationStamp &&
                         publicGrid[cj] != originalValue[cj]) ||
                        (changeStamp[cn] == operationStamp && publicGrid[cn] != originalValue[cn]);
                }
            } else
                hot = g < q - RQ_HOT || g > q + 1 + RQ_HOT;
            if (hot) {
                int lo = j - rqActR + 1, hi = j + rqActR;
                for (int t2 = lo; t2 <= hi; t2++) {
                    int jj = t2;
                    if (jj < 0)
                        jj += s;
                    else if (jj >= s)
                        jj -= s;
                    if (jj >= 0 && jj < s)
                        rqAct[jj] = 1;
                }
                nact++;
            }
        }
        (void)last;
        if (nact == 0)
            return 0;
        if (rqWBv > 0 && rqBud) {
            int na = 0;
            for (int j = 0; j < s; j++)
                na += rqAct[j];
            while (w > 1 &&
                   multiplyNonnegative(na, multiplyNonnegative((w << 1) + 1, (w << 1) + 1)) > rqWBv)
                w--;
            if (multiplyNonnegative(na, 9) > rqWBv)
                return 0;
            W = (w << 1) + 1;
        }
    } else
        for (int j = 0; j < s; j++)
            rqAct[j] = 1;
    rqAct[0] = 0;
    {
        int na = 0;
        for (int j = 0; j < s; j++)
            na += rqAct[j];
        rqWork += s + multiplyNonnegative(na, (w << 1) + 1) + multiplyNonnegative(na, (w << 1) + 1);
    }
    int off = 0;
    const int op_ = operationStamp;
    int rqP[(RQW_MAX << 1) + 4];
    ll rqWG[(RQW_MAX << 1) + 4];
    const bool vwOn = N >= 64 && x != 0 && typeSize[0] >= 3 && F[0] != 0;
    ll tv[5];
    tv[0] = -(thr << 1);
    tv[1] = -thr;
    tv[2] = 0;
    tv[3] = thr;
    tv[4] = thr << 1;
    for (int j = 1; j < s; j++) {
        if (!rqAct[j])
            continue;
        rqOff[j] = off;
        off += W;
        int a = rqA[j];
        const int ga = publicGrid[a], oa = changeStamp[a] == op_ ? originalValue[a] : ga,
                  cna = oa != ga;
        int lo = -w, hi = w;
        {
            int gl = a - rqA[j - 1], gr = (j + 1 < s ? rqA[j + 1] : rqA[0] + N) - a;
            if (lo < 1 - gl)
                lo = 1 - gl;
            if (hi > gr - 1)
                hi = gr - 1;
        }
        rqLo[j] = lo + w;
        rqHi[j] = hi + w;
        rqStG++;
        int nP = 0, kv = 1;
        ll insV = 0;
        if (vwOn) {
            int ps = a + lo;
            if (ps < 0)
                ps += N;
            int pe = a + hi;
            if (pe >= N)
                pe -= N;
            ull vwm = bitsAt(ps) & lowMask(hi - lo + 1);
            rqP[0] = lo - dist(prevVac(ps), ps);
            nP = 1;
            while (vwm) {
                rqP[nP++] = lo + __builtin_ctzll(vwm);
                vwm &= vwm - 1;
            }
            rqP[nP++] = hi + dist(pe, nextVac(pe));
            int p0 = 0;
            for (int k = 0; k + 1 < nP; k++) {
                rqWG[k] = wcst(0, rqP[k + 1] - rqP[k]);
                if (rqP[k] < 0)
                    p0 = k;
            }
            insV = wcst(0, -rqP[p0]) + wcst(0, rqP[p0 + 1]) - rqWG[p0];
        }
        for (int d = lo; d <= hi; d++) {
            ll v;
            if (d == 0)
                v = 0;
            else {
                int b = a + d;
                if (b >= N)
                    b -= N;
                else if (b < 0)
                    b += N;
                int y = slotType[b];
                int ad = d < 0 ? -d : d;
                if (y == x)
                    v = INF;
                else if (zchMask && ((y == 0 && !(zchMask & 1)) || (y != 0 && !(zchMask & 2)) ||
                                     ((zchMask & 4) && !cna)))
                    v = INF;
                else if (RQ_PRUNE && y != 0 && typeSize[y] > 1 && ad > qv[y] + RQ_PRUNE - 1)
                    v = INF;
                else {
                    ll dy;
                    if (y == 0 && vwOn) {
                        while (rqP[kv] < d)
                            kv++;
                        const int Lo = rqP[kv - 1], Ro = rqP[kv + 1];
                        if (Lo < 0 && Ro > 0)
                            dy = wcst(0, -Lo) + wcst(0, Ro) - rqWG[kv - 1] - rqWG[kv];
                        else
                            dy = wcst(0, Ro - Lo) - rqWG[kv - 1] - rqWG[kv] + insV;
                    } else
                        dy = rqMoveW(y, b, a);
                    if (dy == INVALID)
                        v = INF;
                    else {
                        const int gb = publicGrid[b],
                                  ob = changeStamp[b] == op_ ? originalValue[b] : gb;
                        int dm = (gb != oa) - cna + (ga != ob) - (gb != ob);
                        v = dy + tv[dm + 2];
                    }
                }
            }
            rqNCf[rqOff[j] + d + w] = v;
        }
    }
    ll V[(RQW_MAX << 1) + 1], Vn[(RQW_MAX << 1) + 1], gc[(RQW_MAX << 2) + 1],
        gc2[(RQW_MAX << 2) + 1];
    int gcKey = -1, gcKey2 = -1;
    ll rqKA[(RQW_MAX << 1) + 1];
    int rqPA[(RQW_MAX << 1) + 1], rqPB[(RQW_MAX << 1) + 1], rqSA[(RQW_MAX << 1) + 1];
    const ll fsx = wmt[(x << 6) + 1];
    for (int d = 0; d < W; d++)
        V[d] = INF;
    V[w] = 0;
    int prevAct = 0;
    ll curS = 0;
    for (int j = 1; j < s; j++) {
        int a0 = rqA[j - 1], a1 = rqA[j];
        int g0 = a1 - a0;
        int act = rqAct[j];
        if (!act && !prevAct) {
            const ll c0 = wcst(x, g0);
            curS += c0;
            V[w] += c0;
            rqCh[j][w] = (unsigned char)w;
            continue;
        }
        curS += wcst(x, g0);
        if (!act && !prevAct) {
            V[w] += wcst(x, g0);
            rqCh[j][w] = (unsigned char)w;
            continue;
        }
        {
            const int dlo = act ? rqLo[j] : w, dhi = act ? rqHi[j] : w;
            const int plo = prevAct ? rqLo[j - 1] : w, phi = prevAct ? rqHi[j - 1] : w;
            const int ob = act ? rqOff[j] : 0;
            const int qx = qv[x];
            for (int d1 = 0; d1 < W; d1++)
                Vn[d1] = INF;
            {
                ll ka = 0;
                ll bA = INF + INF, bB = INF + INF;
                int iA = -1, iB = -1;
                for (int d0 = plo; d0 <= phi; d0++) {
                    ll av = V[d0] + ka, bv = V[d0] - ka;
                    rqKA[d0] = av;
                    if (bv < bB) {
                        bB = bv;
                        iB = d0;
                    }
                    rqPB[d0] = iB;
                    if (av < bA) {
                        bA = av;
                        iA = d0;
                    }
                    rqPA[d0] = iA;
                    ka += fsx;
                }
                bA = INF + INF;
                iA = -1;
                for (int d0 = phi; d0 >= plo; d0--) {
                    if (rqKA[d0] <= bA) {
                        bA = rqKA[d0];
                        iA = d0;
                    }
                    rqSA[d0] = iA;
                }
            }
            for (int d1 = dlo; d1 <= dhi; d1++) {
                ll nc = act ? rqNCf[ob + d1] : 0;
                if (nc >= INF) {
                    rqCh[j][d1] = (unsigned char)w;
                    continue;
                }
                ll best = INF;
                int bd = w;
                const int t0 = d1 + g0;
                int rhi = t0 - qx - 1;
                if (rhi > phi)
                    rhi = phi;
                if (rhi >= plo) {
                    int c = rqPB[rhi];
                    if (V[c] < INF) {
                        best = V[c] + wcst(x, t0 - c);
                        bd = c;
                    }
                }
                int llo = t0 - qx;
                if (llo < plo)
                    llo = plo;
                int lhi = t0 - 1;
                if (lhi > phi)
                    lhi = phi;
                if (llo <= lhi) {
                    int c;
                    if (lhi == phi)
                        c = rqSA[llo];
                    else if (llo == plo)
                        c = rqPA[lhi];
                    else {
                        c = llo;
                        ll m = rqKA[llo];
                        for (int d0 = llo + 1; d0 <= lhi; d0++)
                            if (rqKA[d0] < m) {
                                m = rqKA[d0];
                                c = d0;
                            }
                    }
                    if (V[c] < INF) {
                        ll v = V[c] + wcst(x, t0 - c);
                        if (v < best) {
                            best = v;
                            bd = c;
                        }
                    }
                }
                Vn[d1] = best >= INF ? INF : best + nc;
                rqCh[j][d1] = (unsigned char)bd;
            }
            for (int d = 0; d < W; d++)
                V[d] = Vn[d];
            prevAct = act;
            continue;
        }
        if (g0 != gcKey) {
            if (g0 == gcKey2) {
                for (int e = 0; e <= (w << 2); e++) {
                    ll tmp = gc[e];
                    gc[e] = gc2[e];
                    gc2[e] = tmp;
                }
                gcKey2 = gcKey;
                gcKey = g0;
            } else {
                for (int e = 0; e <= (w << 2); e++)
                    gc2[e] = gc[e];
                gcKey2 = gcKey;
                gcKey = g0;
                for (int e = -(w << 1); e <= (w << 1); e++) {
                    int g = g0 + e;
                    gc[e + (w << 1)] = g >= 1 ? wcst(x, g) : INF;
                }
            }
        }
        int dlo = act ? rqLo[j] : w, dhi = act ? rqHi[j] : w;
        int plo = prevAct ? rqLo[j - 1] : w, phi = prevAct ? rqHi[j - 1] : w;
        for (int d1 = 0; d1 < W; d1++)
            Vn[d1] = INF;
        const int o2 = (w << 1);
        const int ob = act ? rqOff[j] : 0;
        for (int d1 = dlo; d1 <= dhi; d1++) {
            ll nc = act ? rqNCf[ob + d1] : 0;
            if (nc >= INF) {
                rqCh[j][d1] = (unsigned char)w;
                continue;
            }
            ll best = INF;
            int bd = w;
            const int gb = d1 + o2;
            for (int d0 = plo; d0 <= phi; d0++) {
                ll v = V[d0] + gc[gb - d0];
                bool lt = v < best;
                best = lt ? v : best;
                bd = lt ? d0 : bd;
            }
            Vn[d1] = best >= INF ? INF : best + nc;
            rqCh[j][d1] = (unsigned char)bd;
        }
        for (int d = 0; d < W; d++)
            V[d] = Vn[d];
        prevAct = act;
    }
    ll best = INF;
    int bd = -1;
    for (int d = 0; d < W; d++) {
        if (V[d] >= INF)
            continue;
        int g = rqA[0] + N - (rqA[s - 1] + d - w);
        if (g < 1)
            continue;
        ll v = V[d] + wcst(x, g);
        if (v < best) {
            best = v;
            bd = d;
        }
    }
    if (bd < 0)
        return 0;
    const ll cur = curS + wcst(x, rqA[0] + N - rqA[s - 1]);
    if (best >= cur)
        return 0;
    int d = bd, nsw = 0;
    for (int j = s - 1; j >= 1; j--) {
        int pd = rqCh[j][d];
        if (d != w) {
            int a = rqA[j], b = a + d - w;
            if (b >= N)
                b -= N;
            else if (b < 0)
                b += N;
            rqPart[j] = b;
            nsw++;
        } else
            rqPart[j] = -1;
        d = pd;
    }
    for (int j = 1; j < s; j++) {
        int b = rqPart[j];
        if (b >= 0 && slotType[rqA[j]] == x && slotType[b] != x)
            doSwap(rqA[j], b);
    }
    return nsw;
}
#define VC_VRL 0
#define VC_VSH 1
#define VC_VSL 0
#define VC_VW 4
#define VC_VH 4
#define VC_VR 1
#define VC_DRY 0
#define VC_REF 0
#define MQ_VRL 0
#define MQ_VSH 0
ull vcVb0[(MAXN >> 6) + 2];
ull vcAct[(MAXN >> 6) + 2];
int vcSeg[MAXN + 8];
int vcSegPart[MAXN + 8];
unsigned char vcCh[MAXN + 8][(RQW_MAX << 1) + 1];
ll vcNC[((MAXN + 8) << 4) + MAXN + 8];
int vcOff[MAXN + 8];
int vcLo[MAXN + 8], vcHi[MAXN + 8];
__attribute__((noinline)) int vcRelat0(int w, ll thr, int R) {
    const int s = typeSize[0];
    if (s < 3 || F[0] == 0 || w < 1 || N < 8)
        return 0;
    if (w > RQW_MAX)
        w = RQW_MAX;
    const int W = (w << 1) + 1;
    const ll INF = (ll)1 << 60;
    int anchor = -1;
    for (int ww = 0; ww < NW; ww++)
        if (vb[ww]) {
            anchor = (ww << 6) + __builtin_ctzll(vb[ww]);
            break;
        }
    if (anchor < 0)
        return 0;
    const ll vrfT = BOP_VRF > 0 ? (multiplyNonnegative(thr, BOP_VRF) >> 4) : 0;
    int nh = 0;
    for (int ww = 0; ww < NW; ww++) {
        ull m = vb[ww] & ~vcVb0[ww];
        while (m) {
            int p = (ww << 6) + __builtin_ctzll(m);
            m &= m - 1;
            if (BOP_VRF > 0) {
                const int a = dist(prevVac(p), p), b = dist(p, nextVac(p));
                const ll base = wcst(0, a) + wcst(0, b);
                ll gbest = 0;
                for (int d = -w; d <= w; d++) {
                    if (d == 0 || a + d < 1 || b - d < 1)
                        continue;
                    const ll gv = base - wcst(0, a + d) - wcst(0, b - d);
                    if (gv > gbest)
                        gbest = gv;
                }
                if (gbest <= vrfT)
                    continue;
            }
            nh++;
            int q = p;
            vcAct[q >> 6] |= 1ULL << (q & 63);
            for (int k = 1; k < R; k++) {
                q = prevVac(q);
                vcAct[q >> 6] |= 1ULL << (q & 63);
            }
            q = p;
            for (int k = 0; k < R; k++) {
                q = nextVac(q);
                vcAct[q >> 6] |= 1ULL << (q & 63);
            }
        }
    }
    if (nh == 0)
        return 0;
    vcAct[anchor >> 6] &= ~(1ULL << (anchor & 63));
    int na = 0;
    for (int ww = 0; ww < NW; ww++) {
        ull m = vcAct[ww];
        vcAct[ww] = 0;
        while (m) {
            vcSeg[na++] = (ww << 6) + __builtin_ctzll(m);
            m &= m - 1;
        }
    }
    if (na == 0 || VC_DRY == 3)
        return 0;
    const int op_ = operationStamp;
    ll tv[5];
    tv[0] = -(thr << 1);
    tv[1] = -thr;
    tv[2] = 0;
    tv[3] = thr;
    tv[4] = thr << 1;
    ll totCur = 0, totBest = 0;
    ll V[(RQW_MAX << 1) + 1], Vn[(RQW_MAX << 1) + 1];
    int k0 = 0;
    while (k0 < na) {
        int k1 = k0 + 1;
        while (k1 < na && nextVac(vcSeg[k1 - 1]) == vcSeg[k1])
            k1++;
        const int pL = prevVac(vcSeg[k0]);
        const int pR = nextVac(vcSeg[k1 - 1]);
        int offA = 0;
        for (int k = k0; k < k1; k++) {
            vcOff[k] = offA;
            offA += W;
            const int a = vcSeg[k];
            const int ga = publicGrid[a], oa = changeStamp[a] == op_ ? originalValue[a] : ga,
                      cna = oa != ga;
            int lo = -w, hi = w;
            {
                int gl = dist(k == k0 ? pL : vcSeg[k - 1], a),
                    gr = dist(a, k + 1 < k1 ? vcSeg[k + 1] : pR);
                if (lo < 1 - gl)
                    lo = 1 - gl;
                if (hi > gr - 1)
                    hi = gr - 1;
            }
            vcLo[k] = lo + w;
            vcHi[k] = hi + w;
            rqStG++;
            const int off = vcOff[k];
            for (int d = lo; d <= hi; d++) {
                ll v;
                if (d == 0)
                    v = 0;
                else {
                    int b = a + d;
                    if (b >= N)
                        b -= N;
                    else if (b < 0)
                        b += N;
                    int y = slotType[b];
                    int ad = d < 0 ? -d : d;
                    if (y == 0)
                        v = INF;
                    else if (RQ_PRUNE && typeSize[y] > 1 && ad > qv[y] + RQ_PRUNE - 1)
                        v = INF;
                    else {
                        ll dy = rqMoveW(y, b, a);
                        if (dy == INVALID)
                            v = INF;
                        else {
                            const int gb = publicGrid[b],
                                      ob = changeStamp[b] == op_ ? originalValue[b] : gb;
                            int dm = (gb != oa) - cna + (ga != ob) - (gb != ob);
                            v = dy + tv[dm + 2];
                        }
                    }
                }
                vcNC[off + d + w] = v;
            }
        }
        if (VC_DRY == 2) {
            k0 = k1;
            continue;
        }
        ll cur = 0;
        for (int d = 0; d < W; d++)
            V[d] = INF;
        V[w] = 0;
        int plo = w, phi = w;
        int prevPos = pL;
        for (int k = k0; k < k1; k++) {
            const int a = vcSeg[k];
            const int g0 = dist(prevPos, a);
            cur += wcst(0, g0);
            const int dlo = vcLo[k], dhi = vcHi[k], off = vcOff[k];
            for (int d1 = 0; d1 < W; d1++)
                Vn[d1] = INF;
            for (int d1 = dlo; d1 <= dhi; d1++) {
                ll nc = vcNC[off + d1];
                if (nc >= INF) {
                    vcCh[k][d1] = (unsigned char)w;
                    continue;
                }
                ll best = INF;
                int bd = w;
                for (int d0 = plo; d0 <= phi; d0++) {
                    if (V[d0] >= INF)
                        continue;
                    int g = g0 + d1 - d0;
                    if (g < 1)
                        continue;
                    ll v = V[d0] + wcst(0, g);
                    if (v < best) {
                        best = v;
                        bd = d0;
                    }
                }
                Vn[d1] = best >= INF ? INF : best + nc;
                vcCh[k][d1] = (unsigned char)bd;
            }
            for (int d = 0; d < W; d++)
                V[d] = Vn[d];
            plo = dlo;
            phi = dhi;
            prevPos = a;
        }
        const int gR = dist(prevPos, pR);
        cur += wcst(0, gR);
        ll best = INF;
        int bd = -1;
        for (int d0 = plo; d0 <= phi; d0++) {
            if (V[d0] >= INF)
                continue;
            int g = gR - (d0 - w);
            if (g < 1)
                continue;
            ll v = V[d0] + wcst(0, g);
            if (v < best) {
                best = v;
                bd = d0;
            }
        }
        if (bd < 0)
            return 0;
        totCur += cur;
        totBest += best;
        int d = bd;
        for (int k = k1 - 1; k >= k0; k--) {
            vcSegPart[k] = -1;
            if (d != w) {
                int b = vcSeg[k] + d - w;
                if (b >= N)
                    b -= N;
                else if (b < 0)
                    b += N;
                vcSegPart[k] = b;
            }
            d = vcCh[k][d];
        }
        k0 = k1;
    }
    if (totBest >= totCur || VC_DRY)
        return 0;
    int nsw = 0;
    for (int k = 0; k < na; k++) {
        int b = vcSegPart[k];
        if (b >= 0) {
            nsw++;
            if (slotType[vcSeg[k]] == 0 && slotType[b] != 0)
                doSwap(vcSeg[k], b);
        }
    }
    return nsw;
}
#define BOP_VR1H 4
__attribute__((noinline)) int bopVr1(ll thr) {
    if (typeSize[0] < 3 || F[0] == 0 || N < 8)
        return 0;
    const int op_ = operationStamp;
    ll tv[5];
    tv[0] = -(thr << 1);
    tv[1] = -thr;
    tv[2] = 0;
    tv[3] = thr;
    tv[4] = thr << 1;
    int nsw = 0;
    for (int ww = 0; ww < NW; ww++) {
        ull m = vb[ww] & ~vcVb0[ww];
        while (m) {
            const int p = (ww << 6) + __builtin_ctzll(m);
            m &= m - 1;
            if (slotType[p] != 0)
                continue;
            const int L = prevVac(p), R = nextVac(p);
            const int gl = dist(L, p), gr = dist(p, R);
            const ll v0 = wcst(0, gl) + wcst(0, gr);
            const int ga = publicGrid[p], oa = changeStamp[p] == op_ ? originalValue[p] : ga,
                      cna = oa != ga;
            ll best = 0;
            int bb = -1;
            for (int sd = 0; sd < 2; sd++) {
                int b = sd == 0 ? p - 1 : p + 1;
                if (b < 0)
                    b += N;
                else if (b >= N)
                    b -= N;
                if ((sd == 0 ? gl : gr) < 2)
                    continue;
                const int y = slotType[b];
                if (y == 0)
                    continue;
                const ll dv =
                    wcst(0, sd == 0 ? gl - 1 : gl + 1) + wcst(0, sd == 0 ? gr + 1 : gr - 1) - v0;
                const int gb = publicGrid[b], ob = changeStamp[b] == op_ ? originalValue[b] : gb;
                const int dm = (gb != oa) - cna + (ga != ob) - (gb != ob);
                const ll vb0 = dv + tv[dm + 2];
                if (vb0 - (wmt[(y << 6) + 1] << 1) >= best)
                    continue;
                ll dy = 0;
                if (typeSize[y] >= 2 && F[y] != 0) {
                    const int Ly = prvT(b, y), Ry = nxtT(b, y);
                    dy = wcst(y, dist(Ly, p)) + wcst(y, dist(p, Ry)) - wcst(y, dist(Ly, b)) -
                         wcst(y, dist(b, Ry));
                }
                const ll v = dy + vb0;
                if (v < best) {
                    best = v;
                    bb = b;
                }
            }
            if (bb >= 0) {
                const int y = slotType[bb];
                typePenaltyDirty[y] = 1;
                typePenaltyDirty[0] = 1;
                const int Ly = prevSame[bb], Ry = nextSame[bb];
                markChange(p);
                markChange(bb);
                if (Ly == bb) {
                    nextSame[p] = p;
                    prevSame[p] = p;
                    typeHead[y] = p;
                } else {
                    nextSame[Ly] = p;
                    prevSame[p] = Ly;
                    nextSame[p] = Ry;
                    prevSame[Ry] = p;
                    if (typeHead[y] == bb)
                        typeHead[y] = Ry;
                }
                vbClr(p);
                vbSet(bb);
                if (TBITS) {
                    TBCLR(y, bb);
                    TBSET(y, p);
                }
                slotType[p] = y;
                slotType[bb] = 0;
                publicGrid[p] = publicGrid[bb];
                publicGrid[bb] = 0;
                nsw++;
            }
        }
    }
    return nsw;
}
#define BO_LSC 0
#define BO_LSB 64
#define BO_LSK 16
#define BO_LSH 4
#define BO_RXC 5
#define BO_RXT 2
#define BO_RXG 0
#define BO_RPR 0
#define BO_RPRH 4
#define BOP_RXMAXH 4
const int RX_MAXH = BOP_RXMAXH;
ll r2VacExcess() {
    const int sc = typeSize[0];
    if (sc < 2 || F[0] == 0)
        return 0;
    const int q = qv[0];
    ll A = 0;
    int Gc = 0;
    int first = -1, last = -1;
    if (SX_VQ > 0 && q >= 1 && q <= SX_VQ && multiplyNonnegative(q, NW) <= sc) {
        int nle, e;
        ll sle;
        vacShort(q, nle, sle, first, last, e);
        const int ngt = e - 1 - nle;
        const ll sgt = (ll)(last - first) - sle;
        A = (multiplyNonnegative(q, nle) - sle) + (sgt - multiplyNonnegative(q, ngt));
        Gc = ngt;
    } else
        for (int w = 0; w < NW; w++) {
            ull m = vb[w];
            while (m) {
                int i = (w << 6) + __builtin_ctzll(m);
                m &= m - 1;
                if (last >= 0) {
                    int dg = i - last - q;
                    A += dg < 0 ? -dg : dg;
                    Gc += dg > 0;
                } else
                    first = i;
                last = i;
            }
        }
    if (first >= 0) {
        int dg = first + N - last - q;
        A += dg < 0 ? -dg : dg;
        Gc += dg > 0;
    }
    const int nd = sc - (Gc << 1);
    const ll sd = multiplyNonnegative(A, sc) +
                  (nd >= 0 ? multiplyNonnegative(rv[0], nd) : -multiplyNonnegative(rv[0], -nd));
    const ll r = rv[0];
    return multiplyNonnegative(sd, F[0]) -
           multiplyNonnegative(multiplyNonnegative(r, sc - r) << 1, F[0]);
}
int rxP[(MAXN << 1) + 64];
int rxQ[(MAXN << 1) + 72];
ll rxNode[MAXN + 8];
ll rxPair[MAXN + 8];
unsigned char rxIsX[MAXN + 8];
int rxI[MAXN + 8];
unsigned char rxCh[MAXN + 8][(RX_MAXH << 1) + 1];
int rxFrom[MAXN + 8], rxTo[MAXN + 8];
int rxSt[MAXN + 8];
int rxSer = 0;
ll rxGX[MAXN + 8];
static SP2_I ll rxW0(int g) {
    return g < TBe ? wctab0[g] : wcstg(0, g);
}
template <int HC> int relx4B(int x, int h, ll thr);
// 针对空位间隔实施有界迁移，缓解过密和过疏位置的相邻惩罚。
int relx4(int x, int h, ll thr) {
    int s = typeSize[x];
    int E = typeSize[0];
    if (x == 0 || s < 3 || E < 1 || F[x] == 0 || N < 16)
        return 0;
    if (h > RX_MAXH)
        h = RX_MAXH;
    if (h < 1)
        return 0;
    if (h == 1)
        return relx4B<1>(x, h, thr);
    return relx4B<0>(x, h, thr);
}
template <int HC> int relx4B(int x, int h_, ll thr) {
    const int h = HC > 0 ? HC : h_;
    int s = typeSize[x];
    int E = typeSize[0];
    int n = 0, ns = 0;
    for (int w = 0; w < NW; w++) {
        ull mx = TBit[(x << 8) + w], m = mx | vb[w];
        while (m) {
            int b = __builtin_ctzll(m);
            m &= m - 1;
            int isx = (int)((mx >> b) & 1);
            rxIsX[n] = (unsigned char)isx;
            rxI[ns] = n;
            ns += isx;
            rxP[n++] = (w << 6) + b;
        }
    }
    if (n != s + E || ns != s)
        return 0;
    if (++rxSer >= (1 << 30)) {
        rxSer = 1;
        for (int k = 0; k < MAXN + 8; k++)
            rxSt[k] = 0;
    }
    const int ser = rxSer;
    const int xid = serviceId[x];
    const int op_ = operationStamp;
    int GXM = (qv[x] << 2) + 64;
    if (GXM > N)
        GXM = N;
    for (int g = 1; g <= GXM; g++)
        rxGX[g] = wcstg(x, g);
#define RXGX(g) ((g) <= GXM ? rxGX[g] : wcstg(x, (g)))
    const bool vac = E >= 2 && F[0] != 0;
    rxQ[0] = rxP[n - 1] - N;
    for (int k = 0; k < n; k++)
        rxQ[k + 1] = rxP[k];
    rxQ[n + 1] = rxP[0] + N;
    rxQ[n + 2] = rxP[1] + N;
    for (int k = 0; k < n; k++)
        rxP[n + k] = rxP[k] + N;
#define RXNODE(k)                                                                                  \
    do {                                                                                           \
        if (rxSt[k] != ser) {                                                                      \
            rxSt[k] = ser;                                                                         \
            int p_ = rxP[k];                                                                       \
            ll nd_ = 0, pc_ = 0;                                                                   \
            if (vac) {                                                                             \
                int a_ = p_ - rxQ[k], b_ = rxQ[(k) + 2] - p_, c_ = rxQ[(k) + 3] - rxQ[(k) + 2];    \
                ll wab_ = rxW0(a_ + b_), wb_ = rxW0(b_);                                           \
                nd_ = wab_ - rxW0(a_) - wb_;                                                       \
                pc_ = rxW0(a_ + b_ + c_) - wab_ - rxW0(b_ + c_) + wb_;                             \
            }                                                                                      \
            int o_ = changeStamp[p_] == op_ ? originalValue[p_] : publicGrid[p_];                  \
            nd_ += o_ == xid ? -thrOld : (o_ == 0 ? thr : 0);                                      \
            rxNode[k] = nd_;                                                                       \
            rxPair[k] = pc_;                                                                       \
        }                                                                                          \
    } while (0)
#define BOP_RXOLD 0
    const ll thrOld = thr << BOP_RXOLD;
    const int W = (h << 1) + 1;
    const ll INF = (ll)1 << 60;
    const int a0 = rxI[0];
    ll V[(RX_MAXH << 1) + 1], Vn[(RX_MAXH << 1) + 1];
    for (int d = 0; d < W; d++)
        V[d] = INF;
    RXNODE(a0);
    V[h] = rxNode[a0];
    ll cur = rxNode[a0];
    int prevI = a0;
    const int hiLim = a0 + n;
    for (int k = 1; k < s; k++) {
        const int ik = rxI[k];
        RXNODE(ik);
        cur += rxNode[ik] + RXGX(rxP[ik] - rxP[prevI]);
        if (ik == prevI + 1)
            cur += rxPair[prevI];
#define BOP_RXSTRICT 0
        bool strictK = false;
        if (BOP_RXSTRICT) {
            int p_ = rxP[ik];
            int o_ = changeStamp[p_] == op_ ? originalValue[p_] : publicGrid[p_];
            strictK = o_ == xid;
        }
#define BOP_RXPR 0
        if (BOP_RXPR > 0) {
            int ev[(RX_MAXH << 1) + 1], ne = 0;
            for (int e = 0; e < W; e++)
                if (V[e] < INF)
                    ev[ne++] = e;
            ll mn = INF;
            for (int d = 0; d < W; d++) {
                const int u = ik + d - h;
                if (u <= a0 || u >= hiLim || (strictK && d != h)) {
                    Vn[d] = INF;
                    rxCh[k][d] = (unsigned char)h;
                    continue;
                }
                const int pu = rxP[u];
                ll best = INF;
                int bd = h;
                for (int j = 0; j < ne; j++) {
                    const int e = ev[j];
                    const int v = prevI + e - h;
                    if (v >= u)
                        break;
                    ll cv = V[e] + RXGX(pu - rxP[v]);
                    if (v + 1 == u) {
                        int vk = v >= n ? v - n : v;
                        RXNODE(vk);
                        cv += rxPair[vk];
                    }
                    if (cv < best) {
                        best = cv;
                        bd = e;
                    }
                }
                if (best < INF) {
                    int uk = u >= n ? u - n : u;
                    RXNODE(uk);
                    Vn[d] = best + rxNode[uk];
                    if (Vn[d] < mn)
                        mn = Vn[d];
                } else
                    Vn[d] = INF;
                rxCh[k][d] = (unsigned char)bd;
            }
            const ll lim = mn + multiplyNonnegative(thr, BOP_RXPR);
            for (int d = 0; d < W; d++)
                V[d] = Vn[d] > lim ? INF : Vn[d];
            prevI = ik;
            continue;
        }
        for (int d = 0; d < W; d++) {
            const int u = ik + d - h;
            if (u <= a0 || u >= hiLim || (strictK && d != h)) {
                Vn[d] = INF;
                rxCh[k][d] = (unsigned char)h;
                continue;
            }
            const int pu = rxP[u];
            ll best = INF;
            int bd = h;
            for (int e = 0; e < W; e++) {
                if (V[e] >= INF)
                    continue;
                const int v = prevI + e - h;
                if (v >= u)
                    break;
                ll cv = V[e] + RXGX(pu - rxP[v]);
                if (v + 1 == u) {
                    int vk = v >= n ? v - n : v;
                    RXNODE(vk);
                    cv += rxPair[vk];
                }
                if (cv < best) {
                    best = cv;
                    bd = e;
                }
            }
            if (best < INF) {
                int uk = u >= n ? u - n : u;
                RXNODE(uk);
                Vn[d] = best + rxNode[uk];
            } else
                Vn[d] = INF;
            rxCh[k][d] = (unsigned char)bd;
        }
        for (int d = 0; d < W; d++)
            V[d] = Vn[d];
        prevI = ik;
    }
    cur += RXGX(rxP[a0] + N - rxP[prevI]);
    if (prevI == n - 1 && a0 == 0)
        cur += rxPair[n - 1];
    ll best = INF;
    int bd = -1;
    for (int d = 0; d < W; d++) {
        if (V[d] >= INF)
            continue;
        int v = prevI + d - h;
        ll cv = V[d] + RXGX(rxP[a0] + N - rxP[v]);
        if (v + 1 == hiLim) {
            int vk = v >= n ? v - n : v;
            RXNODE(vk);
            cv += rxPair[vk];
        }
        if (cv < best) {
            best = cv;
            bd = d;
        }
    }
#undef RXNODE
#undef RXGX
    if (bd < 0 || best >= cur)
        return 0;
    int nm = 0;
    {
        int d = bd;
        for (int k = s - 1; k >= 1; k--) {
            if (d != h) {
                int u = rxI[k] + d - h;
                if (u >= n)
                    u -= n;
                rxFrom[nm] = rxI[k];
                rxTo[nm] = u;
                nm++;
            }
            d = rxCh[k][d];
        }
    }
    if (nm == 0)
        return 0;
    for (int i = 0; i < nm; i++)
        rxSt[rxFrom[i]] = -1;
    for (int i = 0; i < nm; i++)
        rxSt[rxTo[i]] = rxSt[rxTo[i]] == -1 ? -3 : -2;
    int nch = 0;
    for (int i = 0; i < nm; i++) {
        int k = rxFrom[i];
        if (rxSt[k] != -1)
            continue;
        rxSt[k] = 0;
        int p = rxP[k];
        markChange(p);
        TBCLR(x, p);
        slotType[p] = 0;
        publicGrid[p] = 0;
        vbSet(p);
        pushSeed(p);
        nch++;
    }
    for (int i = 0; i < nm; i++) {
        int k = rxTo[i];
        if (rxSt[k] != -2)
            continue;
        rxSt[k] = 0;
        int p = rxP[k];
        markChange(p);
        vbClr(p);
        slotType[p] = x;
        publicGrid[p] = xid;
        TBSET(x, p);
        pushSeed(p);
        nch++;
    }
    for (int i = 0; i < nm; i++) {
        rxSt[rxFrom[i]] = 0;
        rxSt[rxTo[i]] = 0;
    }
    if (nch) {
        int first = -1, last = -1;
        for (int w = 0; w < NW; w++) {
            ull m = TBit[(x << 8) + w];
            while (m) {
                int p = (w << 6) + __builtin_ctzll(m);
                m &= m - 1;
                if (last >= 0) {
                    nextSame[last] = p;
                    prevSame[p] = last;
                } else
                    first = p;
                last = p;
            }
        }
        typeHead[x] = first;
        if (first >= 0) {
            nextSame[last] = first;
            prevSame[first] = last;
        }
        typePenaltyDirty[x] = 1;
    }
    return nch;
}
#define BOP_RA 0
#define BOP_RAH 6
#define BOP_RAC 6
#define BOP_RAN 5000
#define BOP_RAV 16
const int BRA_MAXH = 16;
int braP[MAXN + 8];
int braOL[MAXN + 8];
int braO[MAXN + 8];
ll braOG[MAXN + 8];
ll braNd[MAXN + 8], braPc[MAXN + 8];
int braSt[MAXN + 8];
int braSer = 0;
unsigned char braNew[MAXN + 8];
int braW[MAXN + 8], braLo[MAXN + 8], braHi[MAXN + 8], braU[MAXN + 8];
ll braV[2][(BRA_MAXH << 1) + 2];
ll braY[MAXN + 8], braA[MAXN + 8], braB[MAXN + 8];
unsigned char braCh[MAXN + 8][(BRA_MAXH << 1) + 1];
static SP2_I ll braW0(int g) {
    return g < TBe ? wctab0[g] : wcstg(0, g);
}
int bopReAdd(int x, int h) {
    const int s1 = typeSize[x], E1 = typeSize[0];
    if (x == 0 || s1 < 3 || E1 < 2 || F[x] == 0 || N < 64)
        return 0;
    if (h > BRA_MAXH)
        h = BRA_MAXH;
    const int op_ = operationStamp, xid = serviceId[x];
    int anchor = -1;
    for (int w = 0; w < NW && anchor < 0; w++) {
        ull m = TBit[(x << 8) + w];
        while (m) {
            int p = (w << 6) + __builtin_ctzll(m);
            m &= m - 1;
            if (!(changeStamp[p] == op_ && originalValue[p] == 0)) {
                anchor = p;
                break;
            }
        }
    }
    if (anchor < 0)
        return 0;
    int s0 = 0, e0 = 0, K = 0;
    for (int pass = 0; pass < 2; pass++) {
        const int wlo = pass == 0 ? (anchor >> 6) : 0, whi = pass == 0 ? NW - 1 : (anchor >> 6);
        const int off = pass == 0 ? 0 : N;
        for (int w = wlo; w <= whi; w++) {
            ull mx = TBit[(x << 8) + w], mv = vb[w];
            ull m = mx | mv;
            if (pass == 0 && w == (anchor >> 6))
                m &= (~0ULL << (anchor & 63));
            if (pass == 1 && w == (anchor >> 6))
                m &= ((1ULL << (anchor & 63)) - 1);
            while (m) {
                const int b = __builtin_ctzll(m);
                m &= m - 1;
                const int p = (w << 6) + b;
                if ((mv >> b) & 1) {
                    braP[e0] = p + off;
                    braNew[e0] = 0;
                    braOL[e0] = s0 - 1;
                    e0++;
                } else if (changeStamp[p] == op_ && originalValue[p] == 0) {
                    braP[e0] = p + off;
                    braNew[e0] = 1;
                    braOL[e0] = s0 - 1;
                    braW[K++] = e0;
                    e0++;
                } else
                    braO[s0++] = p + off;
            }
        }
    }
    if (K < 2 || s0 < 1 || e0 != E1 + K || s0 + K != s1)
        return 0;
    braO[s0] = anchor + N;
#define BRGX(g) wcstg(x, (g))
    braOG[0] = 0;
    for (int t = 0; t < s0; t++)
        braOG[t + 1] = braOG[t] + BRGX(braO[t + 1] - braO[t]);
    for (int j = 0; j < K; j++) {
        int lo = braW[j] - h, hi = braW[j] + h;
        if (lo < 1)
            lo = braW[j] < 1 ? braW[j] : 1;
        if (hi > e0 - 2)
            hi = braW[j] > e0 - 2 ? braW[j] : e0 - 2;
        if (j > 0 && lo <= braLo[j - 1])
            lo = braLo[j - 1] + 1;
        braLo[j] = lo;
        braHi[j] = hi;
    }
    for (int j = K - 2; j >= 0; j--)
        if (braHi[j] >= braHi[j + 1])
            braHi[j] = braHi[j + 1] - 1;
    if (++braSer >= (1 << 30)) {
        braSer = 1;
        for (int k = 0; k < MAXN + 8; k++)
            braSt[k] = 0;
    }
    const int ser = braSer;
    const bool vac = F[0] != 0;
#define BRNODE(i)                                                                                  \
    do {                                                                                           \
        if (braSt[i] != ser) {                                                                     \
            braSt[i] = ser;                                                                        \
            ll nd_ = 0, pc_ = 0;                                                                   \
            if (vac) {                                                                             \
                const int pi_ = braP[i];                                                           \
                const int pp_ = (i) > 0 ? braP[(i) - 1] : braP[e0 - 1] - N;                        \
                const int pn_ = (i) + 1 < e0 ? braP[(i) + 1] : braP[0] + N;                        \
                const int pnn_ = (i) + 2 < e0 ? braP[(i) + 2] : braP[(i) + 2 - e0] + N;            \
                const int a_ = pi_ - pp_, b_ = pn_ - pi_, c_ = pnn_ - pn_;                         \
                const ll wab_ = braW0(a_ + b_), wb_ = braW0(b_);                                   \
                nd_ = wab_ - braW0(a_) - wb_;                                                      \
                pc_ = braW0(a_ + b_ + c_) - wab_ - braW0(b_ + c_) + wb_;                           \
            }                                                                                      \
            braNd[i] = nd_;                                                                        \
            braPc[i] = pc_;                                                                        \
        }                                                                                          \
    } while (0)
#define BRA_A(v) (BRGX(braO[braOL[v] + 1] - braP[v]) - braOG[braOL[v] + 1])
#define BRA_B(u) (braOG[braOL[u]] + BRGX(braP[u] - braO[braOL[u]]))
    ll cur = 0;
    {
        int pv = -1;
        for (int j = 0; j < K; j++) {
            const int u = braW[j];
            BRNODE(u);
            cur += braNd[u];
            if (pv < 0)
                cur += BRA_B(u);
            else {
                cur += braOL[pv] == braOL[u] ? BRGX(braP[u] - braP[pv]) : BRA_A(pv) + BRA_B(u);
                if (pv + 1 == u)
                    cur += braPc[pv];
            }
            pv = u;
        }
        cur += BRA_A(pv) + braOG[s0];
    }
    const ll INF = (ll)1 << 60;
    int cb = 0;
#define BOP_RAF 1
    if (BOP_RAF) {
        const int ilo = braLo[0], ihi = braHi[K - 1];
        const ll fs = multiplyNonnegative(s1, F[x]);
        const ll FN = multiplyNonnegative(fs, qv[x]) + wrv[x];
        {
            ll y = multiplyNonnegative(fs, braP[ilo] - anchor);
            for (int i = ilo; i <= ihi; i++) {
                if (i > ilo)
                    y += multiplyNonnegative(braP[i] - braP[i - 1], fs);
                braY[i] = y;
                BRNODE(i);
                const int ol = braOL[i];
                braA[i] = BRGX(braO[ol + 1] - braP[i]) - braOG[ol + 1];
                braB[i] = braOG[ol] + BRGX(braP[i] - braO[ol]);
            }
        }
        {
            const int lo = braLo[0], hi = braHi[0];
            for (int u = lo; u <= hi; u++)
                braV[cb][u - lo] = braNd[u] + braB[u];
        }
        ll SPm[(BRA_MAXH << 1) + 2], QPv[(BRA_MAXH << 1) + 2], PPv[(BRA_MAXH << 1) + 2],
            PMf[(BRA_MAXH << 1) + 2];
        int PAf[(BRA_MAXH << 1) + 2];
        for (int j = 1; j < K; j++) {
            const int plo = braLo[j - 1], phi = braHi[j - 1], lo = braLo[j], hi = braHi[j];
            auto &Vp = braV[cb];
            auto &Vn = braV[cb ^ 1];
            {
                ll mn = INF;
                int am = 0;
                for (int v = plo; v <= phi; v++) {
                    const int k = v - plo;
                    const ll pv = Vp[k];
                    const ll sa = pv + braA[v];
                    const bool lt = sa < mn;
                    mn = lt ? sa : mn;
                    am = lt ? k : am;
                    PMf[k] = mn;
                    PAf[k] = am;
                    PPv[k] = pv + braY[v];
                    QPv[k] = pv - braY[v];
                    SPm[k] = sa;
                }
            }
            int vs = plo - 1;
            for (int u = lo; u <= hi; u++) {
                const int olu = braOL[u];
                while (vs + 1 <= phi && braOL[vs + 1] < olu)
                    vs++;
                const ll yu = braY[u], c1 = FN - yu, c2 = yu - FN, bu_ = braB[u];
                ll best = INF;
                int bv = 0;
                int lim = vs < u - 2 ? vs : u - 2;
                if (lim >= plo) {
                    best = PMf[lim - plo] + bu_;
                    bv = PAf[lim - plo];
                }
                int d0 = vs + 1 > plo ? vs + 1 : plo;
                int d1 = u - 2 < phi ? u - 2 : phi;
                for (int v = d0; v <= d1; v++) {
                    const int k = v - plo;
                    const ll a1 = PPv[k] + c1, a2 = QPv[k] + c2;
                    const ll cv = a1 > a2 ? a1 : a2;
                    const bool lt = cv < best;
                    best = lt ? cv : best;
                    bv = lt ? k : bv;
                }
                const int vq = u - 1;
                if (vq >= plo && vq <= phi) {
                    const int k = vq - plo;
                    ll cv;
                    if (vq <= vs)
                        cv = SPm[k] + bu_;
                    else {
                        const ll a1 = PPv[k] + c1, a2 = QPv[k] + c2;
                        cv = a1 > a2 ? a1 : a2;
                    }
                    cv += braPc[vq];
                    if (cv < best) {
                        best = cv;
                        bv = k;
                    }
                }
                Vn[u - lo] = best >= (INF >> 1) ? INF : best + braNd[u];
                braCh[j][u - lo] = (unsigned char)bv;
            }
            cb ^= 1;
        }
    } else {
        {
            const int lo = braLo[0], hi = braHi[0];
            for (int u = lo; u <= hi; u++) {
                BRNODE(u);
                braV[cb][u - lo] = braNd[u] + BRA_B(u);
            }
        }
        ll SA[(BRA_MAXH << 1) + 2], PM[(BRA_MAXH << 1) + 2];
        int PA[(BRA_MAXH << 1) + 2];
        for (int j = 1; j < K; j++) {
            const int plo = braLo[j - 1], phi = braHi[j - 1], lo = braLo[j], hi = braHi[j];
            auto &Vp = braV[cb];
            auto &Vn = braV[cb ^ 1];
            {
                ll mn = INF;
                int am = -1;
                for (int v = plo; v <= phi; v++) {
                    const ll sa = Vp[v - plo] >= INF ? INF : Vp[v - plo] + BRA_A(v);
                    SA[v - plo] = sa;
                    if (sa < mn) {
                        mn = sa;
                        am = v - plo;
                    }
                    PM[v - plo] = mn;
                    PA[v - plo] = am;
                }
            }
            int vs = plo - 1;
            for (int u = lo; u <= hi; u++) {
                BRNODE(u);
                const int olu = braOL[u];
                while (vs + 1 <= phi && braOL[vs + 1] < olu)
                    vs++;
                ll best = INF;
                int bv = 0;
                int lim = vs < u - 2 ? vs : u - 2;
                if (lim > phi)
                    lim = phi;
                if (lim >= plo && PM[lim - plo] < INF) {
                    best = PM[lim - plo] + BRA_B(u);
                    bv = PA[lim - plo];
                }
                int v0 = lim + 1 > plo ? lim + 1 : plo;
                int v1 = u - 1 < phi ? u - 1 : phi;
                for (int v = v0; v <= v1; v++) {
                    const ll pv = Vp[v - plo];
                    if (pv >= INF)
                        continue;
                    ll cv = pv + (braOL[v] == olu ? BRGX(braP[u] - braP[v]) : BRA_A(v) + BRA_B(u));
                    if (v + 1 == u) {
                        BRNODE(v);
                        cv += braPc[v];
                    }
                    if (cv < best) {
                        best = cv;
                        bv = v - plo;
                    }
                }
                Vn[u - lo] = best >= INF ? INF : best + braNd[u];
                braCh[j][u - lo] = (unsigned char)bv;
            }
            cb ^= 1;
        }
    }
    ll best = INF;
    int bu = -1;
    {
        const int lo = braLo[K - 1], hi = braHi[K - 1];
        for (int u = lo; u <= hi; u++) {
            const ll v = braV[cb][u - lo];
            if (v >= INF)
                continue;
            const ll t = v + BRA_A(u) + braOG[s0];
            if (t < best) {
                best = t;
                bu = u - lo;
            }
        }
    }
#undef BRNODE
#undef BRA_A
#undef BRA_B
#undef BRGX
    if (bu < 0 || best >= cur)
        return 0;
    {
        int o = bu;
        for (int j = K - 1; j >= 0; j--) {
            braU[j] = braLo[j] + o;
            if (j > 0)
                o = braCh[j][o];
        }
    }
    int nch = 0;
    for (int j = 0; j < K; j++)
        braSt[braW[j]] = -1;
    for (int j = 0; j < K; j++)
        braSt[braU[j]] = braSt[braU[j]] == -1 ? -3 : -2;
    for (int j = 0; j < K; j++) {
        const int i = braW[j];
        if (braSt[i] != -1)
            continue;
        braSt[i] = 0;
        int p = braP[i];
        if (p >= N)
            p -= N;
        markChange(p);
        TBCLR(x, p);
        slotType[p] = 0;
        publicGrid[p] = 0;
        vbSet(p);
        pushSeed(p);
        nch++;
    }
    for (int j = 0; j < K; j++) {
        const int i = braU[j];
        if (braSt[i] != -2)
            continue;
        braSt[i] = 0;
        int p = braP[i];
        if (p >= N)
            p -= N;
        markChange(p);
        vbClr(p);
        slotType[p] = x;
        publicGrid[p] = xid;
        TBSET(x, p);
        pushSeed(p);
        nch++;
    }
    for (int j = 0; j < K; j++) {
        braSt[braW[j]] = 0;
        braSt[braU[j]] = 0;
    }
    if (nch) {
        int first = -1, last = -1;
        for (int w = 0; w < NW; w++) {
            ull m = TBit[(x << 8) + w];
            while (m) {
                int p = (w << 6) + __builtin_ctzll(m);
                m &= m - 1;
                if (last >= 0) {
                    nextSame[last] = p;
                    prevSame[p] = last;
                } else
                    first = p;
                last = p;
            }
        }
        typeHead[x] = first;
        if (first >= 0) {
            nextSame[last] = first;
            prevSame[first] = last;
        }
        typePenaltyDirty[x] = 1;
    }
    return nch;
}
