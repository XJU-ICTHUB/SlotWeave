// 从受影响位置生成局部搜索种子。以交换或移动的局部 gap 差值评估候选，避免每次重算完整圆环。
// Included in fixed order by solution.cpp.

SP2_I void pushSeed(int i) {
    const int ii = i & ~(i >> 31);
    const int ok = (nSeeds < seedCap) & (i >= 0) & (inq[ii] == 0);
    seedA[nSeeds] = i;
    inq[ii] |= (char)ok;
    nSeeds += ok;
}
SP_AI ll wcst2(int t, int g1, int g2);
int hvbH = 0, hvbHr = 0, hvbX = 0;
ll hvbVol = 0;
#define HVB_RD 0
#define HVB_RDE 3
#define HVB_DDS 0
#define HVB_RVB 0
#define HVB_KEEP 0
#define HVB_RDR 0
int vpmMvOn = 0, vpmMvN = 0;
int vpmMv[MAXN + 8];
// 从变化附近展开有预算的局部搜索，收益同时计入均匀度与改动价格。
void runLocalSearch(int budget) {
    int h = 0;
    int lsFail = 0;
    const int lsFailMax = (BF_LSF > 0 && N > NM) ? BF_LSF : 0x7fffffff;
    const int mw_ = N > NM ? RB_MIDW : MIDW;
#define LT_LSB 0
    const bool lsbOn = LT_LSB && N > NM && !SP3_LSK;
    int cj[((MIDW > RB_MIDW ? MIDW : RB_MIDW) << 1) + 1];
    ll ca[((MIDW > RB_MIDW ? MIDW : RB_MIDW) << 1) + 1];
    while (h < nSeeds && budget > 0) {
        int i = seedA[h++];
        inq[i] = 0;
        if (!lsbOn)
            budget--;
        int a = slotType[i];
        int sa = typeSize[a];
        if (sa < 3 || F[a] == 0)
            continue;
        int L = prvT(i, a), R = nxtT(i, a);
        int g1 = dist(L, i), g2 = dist(i, R), gl = g1 + g2;
        if (gl < 4)
            continue;
        {
            int q = qv[a];
            int lo = g1 < g2 ? g1 : g2, hi = gl - lo;
            if (hi - lo < 2 || lo > q || hi <= q)
                continue;
        }
        ll base = wcst2(a, g1, g2);
        int h1 = gl >> 1;
        ll mg = base - wcst2(a, h1, gl - h1);
        if (mg <= thrM)
            continue;
        if (lsbOn)
            budget--;
        int m = L + h1;
        if (m >= N)
            m -= N;
        int nc = 0;
        const int qa_ = qv[a];
        const bool tabA = a ? ((h1 - mw_ - qa_ >= -32) & (h1 + mw_ - qa_ <= 31) &
                               (gl - h1 - mw_ - qa_ >= -32) & (gl - h1 + mw_ - qa_ <= 31))
                            : (gl + mw_ < TBe);
        auto wrow = a ? (wdt + (a << 6)) : wctab0;
        const int woff = a ? 32 - qa_ : 0;
        for (int d = -mw_; d <= mw_; d++) {
            int j = m + d;
            if (j >= N)
                j -= N;
            else if (j < 0)
                j += N;
            if (j == i || j == L || j == R || slotType[j] == a)
                continue;
            int gj = h1 + d;
            if (gj <= 0 || gj >= gl)
                continue;
            ll cv = (tabA ? wrow[gj + woff] + wrow[gl - gj + woff] : wcst2(a, gj, gl - gj)) - base;
            int k = nc++;
            while (k > 0 && ca[k - 1] > cv) {
                ca[k] = ca[k - 1];
                cj[k] = cj[k - 1];
                k--;
            }
            ca[k] = cv;
            cj[k] = j;
        }
        ll best = 0;
        int bj = -1;
        for (int it = 0; it < nc; it++) {
            ll av = ca[it];
            int j = cj[it];
            if (av + thrM >= best)
                break;
            budget -= 2;
            int b = slotType[j];
            ll db = dMoveWI(b, j, i);
            if (db == INVALID)
                continue;
            ll v = av + db;
            int dm = changedIf(i, publicGrid[j]) - changedNow(i) + changedIf(j, publicGrid[i]) -
                     changedNow(j);
            if (dm > 0)
                v += dm == 1 ? thrM : multiplyNonnegative(thrM, dm);
            else if (dm < 0)
                v -= dm == -1 ? thrM : multiplyNonnegative(thrM, -dm);
            if (v < best) {
                best = v;
                bj = j;
            }
            if (budget <= 0)
                break;
        }
        if (bj >= 0) {
            int b = slotType[bj];
            int Lb = prvT(bj, b), Rb = nxtT(bj, b);
            doSwap(i, bj);
            if (vpmMvOn && vpmMvN < MAXN && (a == 0 || b == 0)) {
                vpmMv[vpmMvN++] = i;
                vpmMv[vpmMvN++] = bj;
            }
            pushSeed(L);
            pushSeed(R);
            pushSeed(Lb);
            pushSeed(Rb);
            pushSeed(prvT(i, b));
            pushSeed(nxtT(i, b));
            pushSeed(i);
            pushSeed(bj);
            lsFail = 0;
        } else if (nc > 0 && ++lsFail >= lsFailMax)
            break;
    }
    for (int k = h; k < nSeeds; k++)
        inq[seedA[k]] = 0;
    nSeeds = 0;
}
#define TSP 64
#define TSH 2
#define TSC 1000000
#define TSHF 1
#define TIN 0
#define TIR 32
XLS_HIA int prevCellT(int t, int p) {
    int base = t << 8, w = p >> 6, b = p & 63;
    ull m = TBit[base + w] & ((1ULL << b) - 1);
    if (m)
        return (w << 6) + 63 - __builtin_clzll(m);
    for (int k = w - 1; k >= 0; k--) {
        ull mm = TBit[base + k];
        if (mm)
            return (k << 6) + 63 - __builtin_clzll(mm);
    }
    for (int k = NW - 1; k >= w; k--) {
        ull mm = TBit[base + k];
        if (mm)
            return (k << 6) + 63 - __builtin_clzll(mm);
    }
    return -1;
}
XLS_HIA int nextCellT(int t, int p) {
    int base = t << 8, w = p >> 6, b = p & 63;
    ull m = b < 63 ? (TBit[base + w] & ~((2ULL << b) - 1)) : 0;
    if (m)
        return (w << 6) + __builtin_ctzll(m);
    for (int k = w + 1; k < NW; k++) {
        ull mm = TBit[base + k];
        if (mm)
            return (k << 6) + __builtin_ctzll(mm);
    }
    for (int k = 0; k <= w; k++) {
        ull mm = TBit[base + k];
        if (mm)
            return (k << 6) + __builtin_ctzll(mm);
    }
    return -1;
}
XLS_HIA bool findNbFar(int b, int u, int w, int Lu, int Ru, int &L, int &R) {
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
        int c = prevCellT(b, w);
        if (c < 0 || c == u)
            return false;
        L = c;
        R = nextSame[c];
        if (R == u)
            R = nextSame[u];
    } else {
        int c = nextCellT(b, w);
        if (c < 0 || c == u)
            return false;
        R = c;
        L = prevSame[c];
        if (L == u)
            L = prevSame[u];
    }
    return true;
}
XLS_HIA bool findNbF(int b, int u, int w, int &L, int &R) {
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
    return findNbFar(b, u, w, Lu, Ru, L, R);
}
ll dMoveWF(int b, int u, int w) {
    int s = typeSize[b];
    if (s <= 1 || F[b] == 0)
        return 0;
    int Lu = prvT(u, b), Ru = nxtT(u, b);
    if (s >= 3) {
        int g1 = dist(Lu, u), g2 = dist(u, Ru);
        int gw = dist(Lu, w);
        if (gw < g1 + g2)
            return SP3_W4(b, gw, g1 + g2 - gw, g1, g2);
    }
    ll rem;
    if (s == 2)
        rem = wcst(b, N) - wcst(b, dist(Lu, u)) - wcst(b, dist(u, Lu));
    else
        rem = wcst(b, dist(Lu, Ru)) - wcst(b, dist(Lu, u)) - wcst(b, dist(u, Ru));
    int L, R;
    if (!(TBITS ? findNbF(b, u, w, L, R) : findNb(b, u, w, L, R)))
        return INVALID;
    ll ins;
    if (s == 2)
        ins = wcst(b, dist(L, w)) + wcst(b, dist(w, L)) - wcst(b, N);
    else
        ins = wcst(b, dist(L, w)) + wcst(b, dist(w, R)) - wcst(b, dist(L, R));
    return rem + ins;
}
SP2_I ll stabD(int i, int nv) {
    int dm = changedIf(i, nv) - changedNow(i);
    return dm > 0 ? thrM : (dm < 0 ? -thrM : 0);
}
ll hzWork = 0, hzLim = 0;
#define TOW 4000
#define TIW 1000000
ull hzRng = 88172645463325252ULL;
SP2_I ull hzRand() {
    hzRng ^= hzRng << 13;
    hzRng ^= hzRng >> 7;
    hzRng ^= hzRng << 17;
    return hzRng;
}
SP2_I ll swapVal(int i, int j) {
    int a = slotType[i], b = slotType[j];
    ll da = dMoveW(a, i, j);
    if (da == INVALID)
        return INVALID;
    ll db = dMoveW(b, j, i);
    if (db == INVALID)
        return INVALID;
    ll v = da + db;
    if (thrM) {
        int dm = changedIf(i, publicGrid[j]) - changedNow(i) + changedIf(j, publicGrid[i]) -
                 changedNow(j);
        if (dm > 0) {
            v += thrM;
            if (dm > 1)
                v += thrM;
        } else if (dm < 0) {
            v -= thrM;
            if (dm < -1)
                v -= thrM;
        }
    }
    return v;
}
#define TSF 0
ll hzLb[MAXN];
ll hzIns[MAXT];
int hzCand[MAXN];
const ll HZBIG = (ll)1 << 60;
SP_AI ll wcst2(int t, int g1, int g2) {
    if (t == 0)
        return (g1 < TBe ? wctab0[g1] : wcstg(0, g1)) + (g2 < TBe ? wctab0[g2] : wcstg(0, g2));
    const int q = qv[t], b = (t << 6) + 32;
    const int k1 = g1 - q, k2 = g2 - q;
    if ((unsigned)(k1 + 32) < 64u && (unsigned)(k2 + 32) < 64u)
        return wdt[b + k1] + wdt[b + k2];
    return wcstg(t, g1) + wcstg(t, g2);
}
SP_AI ll bestSplit(int t, int g) {
    int h = g >> 1;
    return SP_WC2 ? wcst2(t, h, g - h) : wcst(t, h) + wcst(t, g - h);
}
int tinyDescentFull(int maxSw);
SP2_I ll lbCell(int i, int t, int st) {
    int L = prvT(i, t), R = nxtT(i, t);
    int g1 = dist(L, i), g2 = dist(i, R);
    ll w12 = wcst(t, g1) + wcst(t, g2);
    if (st == 2)
        return bestSplit(t, N) - w12;
    ll a1 = bestSplit(t, g1 + g2) - w12;
    ll a2 = hzIns[t] < HZBIG ? wcst(t, g1 + g2) - w12 + hzIns[t] : a1;
    return a1 < a2 ? a1 : a2;
}
ll hzGap0[MAXN], hzNear[MAXN], hzRem[MAXN];
int hzVac[MAXN], hzGapA[MAXN];
bool hzVacOK = false;
void hzTypeLb(int t) {
    int st = typeSize[t];
    if (st <= 0)
        return;
    bool act = st >= 2 && F[t] != 0;
    if (t != 0) {
        int h = typeHead[t];
        if (h < 0)
            return;
        ll mn = HZBIG;
        int c = h;
        if (act)
            for (int k = 0; k < st; k++) {
                int nx = nextSame[c];
                int g = dist(c, nx);
                if (g >= 2) {
                    ll v = bestSplit(t, g) - wcst(t, g);
                    if (v < mn)
                        mn = v;
                }
                c = nx;
            }
        hzIns[t] = mn;
        c = h;
        for (int k = 0; k < st; k++) {
            hzLb[c] = act ? lbCell(c, t, st) : 0;
            c = nextSame[c];
        }
        return;
    }
    int k = 0;
    for (int w = 0; w < NW; w++) {
        ull m = vb[w];
        while (m) {
            hzVac[k++] = (w << 6) + __builtin_ctzll(m);
            m &= m - 1;
        }
    }
    hzVacOK = act && k >= 3;
    if (!act) {
        hzIns[0] = HZBIG;
        for (int q = 0; q < k; q++)
            hzLb[hzVac[q]] = 0;
        return;
    }
    ll mn = HZBIG;
    for (int q = 0; q < k; q++) {
        int v = hzVac[q], nv = hzVac[q + 1 < k ? q + 1 : 0];
        int g = dist(v, nv);
        hzGapA[q] = g;
        if (g >= 2) {
            ll val = bestSplit(0, g) - wcst(0, g);
            if (val < mn)
                mn = val;
            int p = v + 1;
            if (p >= N)
                p -= N;
            while (p != nv) {
                hzGap0[p] = val;
                p++;
                if (p >= N)
                    p -= N;
            }
        }
    }
    hzIns[0] = mn;
    for (int q = 0; q < k; q++) {
        int v = hzVac[q];
        int g1 = hzGapA[q > 0 ? q - 1 : k - 1], g2 = hzGapA[q];
        ll w12 = wcst(0, g1) + wcst(0, g2);
        if (k == 2) {
            hzLb[v] = bestSplit(0, N) - w12;
            continue;
        }
        ll nr = bestSplit(0, g1 + g2) - w12, rm = wcst(0, g1 + g2) - w12;
        hzNear[v] = nr;
        hzRem[v] = rm;
        ll fr = rm + mn;
        hzLb[v] = nr < fr ? nr : fr;
    }
}
ll hzS[MAXN];
// 小规模位置对的交换下降；只接受当前代价模型下更优的邻居。
int tinyDescent(int maxSw) {
    if (TSF)
        return tinyDescentFull(maxSw);
    for (int i = 0; i < N; i++)
        hzIns[slotType[i]] = HZBIG;
    for (int i = 0; i < N; i++) {
        int t = slotType[i];
        if (t == 0 || typeSize[t] < 2 || F[t] == 0)
            continue;
        int g = dist(i, nextSame[i]);
        if (g >= 2) {
            ll v = bestSplit(t, g) - wcst(t, g);
            if (v < hzIns[t])
                hzIns[t] = v;
        }
    }
    for (int i = 0; i < N; i++) {
        int t = slotType[i], st = typeSize[t];
        if (t == 0)
            continue;
        hzLb[i] = (st >= 2 && F[t] != 0) ? lbCell(i, t, st) : 0;
    }
    hzVacOK = false;
    if (typeSize[0] > 0)
        hzTypeLb(0);
    int done = 0;
    while (done < maxSw && hzWork < hzLim) {
        ll m1 = HZBIG;
        for (int i = 0; i < N; i++) {
            ll lb = hzLb[i] + (changedNow(i) ? -thrM : thrM);
            hzS[i] = lb;
            if (lb < m1)
                m1 = lb;
        }
        int nc = 0;
        for (int i = 0; i < N; i++)
            if (hzS[i] + m1 < 0)
                hzCand[nc++] = i;
        hzWork += N;
        if (nc < 2)
            break;
        sort(hzCand, hzCand + nc,
             [](int u, int v) { return hzS[u] < hzS[v] || (hzS[u] == hzS[v] && u < v); });
        if (thrM && nc > TSC)
            nc = TSC;
        ll best = 0;
        int bi = -1, bj = -1;
        for (int x = 0; x + 1 < nc; x++) {
            int i = hzCand[x];
            ll li = hzS[i];
            if (li + hzS[hzCand[x + 1]] >= best)
                break;
            int a = slotType[i], sa = typeSize[a];
            bool actA = sa >= 2 && F[a] != 0;
            int Li = 0, Ri = 0, g12 = 0;
            ll w12 = 0, remA = 0;
            if (actA) {
                Li = prvT(i, a);
                Ri = nxtT(i, a);
                int g1 = dist(Li, i), g2 = dist(i, Ri);
                g12 = g1 + g2;
                w12 = wcst(a, g1) + wcst(a, g2);
                remA = (sa == 2 ? wcst(a, N) : wcst(a, g12)) - w12;
            }
            bool vacI = a == 0 && hzVacOK;
            for (int y = x + 1; y < nc; y++) {
                int j = hzCand[y];
                ll lj = hzS[j];
                if (li + lj >= best)
                    break;
                int bt = slotType[j];
                if (bt == a)
                    continue;
                if (vacI) {
                    ll lb = hzRem[i] + hzGap0[j];
                    if (hzNear[i] < lb)
                        lb = hzNear[i];
                    if (li - hzLb[i] + lb + lj >= best)
                        continue;
                } else if (bt == 0 && hzVacOK) {
                    ll lb = hzRem[j] + hzGap0[i];
                    if (hzNear[j] < lb)
                        lb = hzNear[j];
                    if (li + lj - hzLb[j] + lb >= best)
                        continue;
                }
                hzWork++;
                ll da = 0;
                if (actA) {
                    if (sa == 2)
                        da = remA + wcst(a, dist(Li, j)) + wcst(a, dist(j, Li)) - wcst(a, N);
                    else {
                        int gw = dist(Li, j);
                        if (gw < g12)
                            da = wcst(a, gw) + wcst(a, g12 - gw) - w12;
                        else {
                            int L, R;
                            if (!findNbFar(a, i, j, Li, Ri, L, R))
                                continue;
                            da = remA + wcst(a, dist(L, j)) + wcst(a, dist(j, R)) -
                                 wcst(a, dist(L, R));
                        }
                    }
                }
                da += stabD(i, publicGrid[j]);
                if (da + hzS[j] >= best)
                    continue;
                ll db = dMoveWF(bt, j, i);
                if (db == INVALID)
                    continue;
                ll v = da + db + stabD(j, publicGrid[i]);
                if (v < best) {
                    best = v;
                    bi = i < j ? i : j;
                    bj = i < j ? j : i;
                }
            }
        }
        if (bi < 0)
            break;
        int ta = slotType[bi], tb = slotType[bj];
        doSwap(bi, bj);
        hzTypeLb(ta);
        hzTypeLb(tb);
        done++;
    }
    return done;
}
int tinyDescentFull(int maxSw) {
    int done = 0;
    while (done < maxSw) {
        ll best = 0;
        int bi = -1, bj = -1;
        for (int i = 0; i < N; i++) {
            int a = slotType[i];
            for (int j = i + 1; j < N; j++) {
                if (slotType[j] == a)
                    continue;
                ll v = swapVal(i, j);
                if (v < best) {
                    best = v;
                    bi = i;
                    bj = j;
                }
            }
        }
        if (bi < 0)
            break;
        doSwap(bi, bj);
        done++;
    }
    return done;
}
