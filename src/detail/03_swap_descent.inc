// 有预算的交换下降与候选下界。类型计数保持不变，缓存相邻间隔代价并按收益挑选交换。
// Included in fixed order by solution.cpp.

#define MNHI 4999
#define MNHN 800
#define MNK 4
#define SM_MNK 0
#define MNKA0 (SM_MNK > MNK ? SM_MNK : MNK)
#define MNKA (MQ_MNK > MNKA0 ? MQ_MNK : MNKA0)
#define SM_MNCH 0
#define SM_MNGT 0
#define SM_MNGW 24
#define SM_MNGR 1
#define MNR 2
#define MNCHF 1
#define MNWL2 4
#define MNPUSH 10
#define MNEV 1000000
#define MNALL 0
#define MNAP 4
#define MNPX 16
#define MNPOS 1
#define MNGT 0
#define MNGW 24
#define MNGR 1
#define MD_DIR 0
#define MD_DIRB 2
#define MD_FAIL 0
#define MD_RVHI 0
#define MD_HVK 0
int mdRbOp = 0;
#define MD_STV -1
#define MD_STT -1
#define MD_LT 0
int mdSeenL[MAXT], mdSeenR[MAXT], mdSeenSt = 0;
#define MD_MEDK 1
#define MD_MEDH 1
int mdWeak = 0;
int mdZero = 0;
int md2NoMH = 0;
#define MD2S_MNW 0
#define MD2S_H4 0
#define MD2S_H4R 0
#define MD2M_H4 0
#define MD2_CUTLO 1000
#define MD2_STT -1
#define MD2_MEDH 1
#define MD2_MEDK 1
pair<ll, int> mdSortA[MAXN];
#define MD_IQCAP 0
#define MD_IQSR 0
#define MD_V0MN 0
#define MD_LSH 0
int mnStamp = 1;
int mnInsSt[MAXT], mnHoleN[MAXT];
int mnHoleL[MAXT][MNKA], mnHoleG[MAXT][MNKA];
ll mnHoleV[MAXT][MNKA];
int mnCSt[MAXN], mnCL[MAXN], mnCR[MAXN], mnCG[MAXN];
ll mnCW[MAXN], mnCRem[MAXN];
int mnInQ[MAXN];
int mnQ[(MAXN << 1) + 64];
ll mnQv[MAXN];
int mnChg[MAXN], mnNChg = 0;
int mnLight = 0;
ll mnEv = 0;
#define MNBC 1
int mnTISt[MAXT], mnSrcSt = 0;
ll mnTIV[MAXT];
void mnHoleIns(int t, int L, int g, ll v) {
    int nh = mnHoleN[t];
    for (int k = 0; k < nh; k++)
        if (mnHoleL[t][k] == L) {
            for (int q = k; q + 1 < nh; q++) {
                mnHoleL[t][q] = mnHoleL[t][q + 1];
                mnHoleG[t][q] = mnHoleG[t][q + 1];
                mnHoleV[t][q] = mnHoleV[t][q + 1];
            }
            nh--;
            break;
        }
    const int mk_ = (SM_MNK > 0 && smT) ? SM_MNK : ((MQ_MNK > 0 && mqT) ? MQ_MNK : MNK);
    if (v < 0 && (nh < mk_ || v < mnHoleV[t][nh - 1])) {
        int q = nh < mk_ ? nh++ : mk_ - 1;
        while (q > 0 && mnHoleV[t][q - 1] > v) {
            mnHoleV[t][q] = mnHoleV[t][q - 1];
            mnHoleL[t][q] = mnHoleL[t][q - 1];
            mnHoleG[t][q] = mnHoleG[t][q - 1];
            q--;
        }
        mnHoleV[t][q] = v;
        mnHoleL[t][q] = L;
        mnHoleG[t][q] = g;
    }
    mnHoleN[t] = nh;
}
#define SX_MNV 8
void mnEnsureInsB(int t);
SP2_I void mnEnsureIns(int t) {
    if (mnInsSt[t] != mnStamp)
        mnEnsureInsB(t);
}
__attribute__((noinline)) void mnEnsureInsB(int t) {
    mnInsSt[t] = mnStamp;
    int st = typeSize[t];
    ll mn = HZBIG;
    mnHoleN[t] = 0;
    hzIns[t] = HZBIG;
    if (st < 2 || F[t] == 0)
        return;
    if (t != 0) {
        int c = typeHead[t];
        if (c < 0)
            return;
        const int qt_ = qv[t], rb_ = (t << 6) + 32 - qt_;
        for (int k = 0; k < st; k++) {
            int nx = nextSame[c];
            int g = dist(c, nx);
            if (g >= 2) {
                const int h_ = g >> 1;
                const unsigned kg_ = (unsigned)(g - qt_ + 32), kh_ = (unsigned)(h_ - qt_ + 32),
                               kr_ = (unsigned)(g - h_ - qt_ + 32);
                ll v = ((kg_ | kh_ | kr_) < 64u) ? wdt[rb_ + h_] + wdt[rb_ + g - h_] - wdt[rb_ + g]
                                                 : bestSplit(t, g) - wcst(t, g);
                if (v < mn)
                    mn = v;
                if (v < 0 &&
                    (mnHoleN[t] <
                         ((SM_MNK > 0 && smT) ? SM_MNK : ((MQ_MNK > 0 && mqT) ? MQ_MNK : MNK)) ||
                     v < mnHoleV[t][mnHoleN[t] - 1]))
                    mnHoleIns(t, c, g, v);
            }
            c = nx;
        }
    } else if (SX_MNV && qv[0] >= 1 && qv[0] <= SX_MNV) {
        const int q0 = qv[0];
        int first = -1, last = -1;
        bool hasShort = false;
        ll xVt[64];
        const int xVL = TBe < 64 ? TBe : 64;
        for (int g = 2; g < xVL; g++) {
            const int h = g >> 1;
            xVt[g] = wctab0[h] + wctab0[g - h] - wctab0[g];
        }
        for (int w = 0; w < NW; w++) {
            const ull v = vb[w];
            if (!v)
                continue;
            if (first < 0)
                first = (w << 6) + __builtin_ctzll(v);
            last = (w << 6) + 63 - __builtin_clzll(v);
            const ull nx = vb[w + 1];
            ull z = v;
            for (int k = 1; k <= q0; k++) {
                const ull e = (v >> k) | (nx << (64 - k));
                if (k >= 2 && (z & e))
                    hasShort = true;
                z &= ~e;
            }
            while (z) {
                const int p = (w << 6) + __builtin_ctzll(z);
                z &= z - 1;
                int ww = w;
                ull m = (p & 63) == 63 ? 0 : (vb[ww] & (~0ULL << ((p & 63) + 1)));
                while (!m) {
                    ww++;
                    if (ww >= NW)
                        break;
                    m = vb[ww];
                }
                if (!m)
                    break;
                const int g = (ww << 6) + __builtin_ctzll(m) - p;
                ll val = g < xVL ? xVt[g] : bestSplit(0, g) - wcst(0, g);
                if (val < mn)
                    mn = val;
                if (val < 0 &&
                    (mnHoleN[0] <
                         ((SM_MNK > 0 && smT) ? SM_MNK : ((MQ_MNK > 0 && mqT) ? MQ_MNK : MNK)) ||
                     val < mnHoleV[0][mnHoleN[0] - 1]))
                    mnHoleIns(0, p, g, val);
            }
        }
        if (hasShort) {
            ll val = bestSplit(0, 2) - wcst(0, 2);
            if (val < mn)
                mn = val;
        }
        if (last >= 0 && first >= 0) {
            int g = dist(last, first);
            if (g >= 2) {
                ll v = bestSplit(0, g) - wcst(0, g);
                if (v < mn)
                    mn = v;
                if (v < 0 &&
                    (mnHoleN[0] <
                         ((SM_MNK > 0 && smT) ? SM_MNK : ((MQ_MNK > 0 && mqT) ? MQ_MNK : MNK)) ||
                     v < mnHoleV[0][mnHoleN[0] - 1]))
                    mnHoleIns(0, last, g, v);
            }
        }
    } else {
        int first = -1, prev = -1;
        for (int w = 0; w < NW; w++) {
            ull m = vb[w];
            while (m) {
                int v2 = (w << 6) + __builtin_ctzll(m);
                m &= m - 1;
                if (prev >= 0) {
                    int g = v2 - prev;
                    if (g >= 2) {
                        ll v = bestSplit(0, g) - wcst(0, g);
                        if (v < mn)
                            mn = v;
                        if (v < 0 && (mnHoleN[0] < ((SM_MNK > 0 && smT)
                                                        ? SM_MNK
                                                        : ((MQ_MNK > 0 && mqT) ? MQ_MNK : MNK)) ||
                                      v < mnHoleV[0][mnHoleN[0] - 1]))
                            mnHoleIns(0, prev, g, v);
                    }
                } else
                    first = v2;
                prev = v2;
            }
        }
        if (prev >= 0 && first >= 0) {
            int g = dist(prev, first);
            if (g >= 2) {
                ll v = bestSplit(0, g) - wcst(0, g);
                if (v < mn)
                    mn = v;
                if (v < 0 &&
                    (mnHoleN[0] <
                         ((SM_MNK > 0 && smT) ? SM_MNK : ((MQ_MNK > 0 && mqT) ? MQ_MNK : MNK)) ||
                     v < mnHoleV[0][mnHoleN[0] - 1]))
                    mnHoleIns(0, prev, g, v);
            }
        }
    }
    hzIns[t] = mn;
}
void mnNoteGap(int t, int L, int g) {
    if (mnInsSt[t] != mnStamp || g < 2)
        return;
    ll v = bestSplit(t, g) - wcst(t, g);
    if (v < hzIns[t])
        hzIns[t] = v;
    mnHoleIns(t, L, g, v);
}
void mnNoteAround(int t, int p) {
    if (mnInsSt[t] != mnStamp || typeSize[t] < 2)
        return;
    if (slotType[p] == t) {
        int L = prvT(p, t), R = nxtT(p, t);
        mnNoteGap(t, L, dist(L, p));
        mnNoteGap(t, p, dist(p, R));
    } else {
        int L = t ? prevCellT(t, p) : prevVac(p);
        if (L < 0)
            return;
        mnNoteGap(t, L, dist(L, nxtT(L, t)));
    }
}
SP2_I void mnCell(int j, int t) {
    if (mnCSt[j] == mnStamp)
        return;
    mnCSt[j] = mnStamp;
    int L = prvT(j, t), R = nxtT(j, t);
    int g1 = dist(L, j), g2 = dist(j, R);
    ll w = wcst(t, g1) + wcst(t, g2);
    mnCL[j] = L;
    mnCR[j] = R;
    mnCG[j] = g1 + g2;
    mnCW[j] = w;
    mnCRem[j] = wcst(t, g1 + g2) - w;
}
SP2_I ll mnLb(int i) {
    int t = slotType[i], st = typeSize[t];
    ll lb = 0;
    if (st >= 2 && F[t] != 0) {
        mnEnsureIns(t);
        if (st == 2)
            lb = lbCell(i, t, st);
        else {
            mnCell(i, t);
            ll a1 = bestSplit(t, mnCG[i]) - mnCW[i];
            ll a2 = hzIns[t] < HZBIG ? mnCRem[i] + hzIns[t] : a1;
            lb = a1 < a2 ? a1 : a2;
        }
    }
    return lb + (changedNow(i) ? -thrM : thrM);
}
int sqWl = 0;
ll mnBest(int i, int &bjOut) {
    mnSrcSt++;
    const int a = slotType[i], sa = typeSize[a];
    const bool actA = sa >= 2 && F[a] != 0;
    int Li = 0, Ri = 0, g12 = 0;
    ll w12 = 0, remA = 0;
    if (actA) {
        mnEnsureIns(a);
        if (sa >= 3) {
            mnCell(i, a);
            Li = mnCL[i];
            Ri = mnCR[i];
            g12 = mnCG[i];
            w12 = mnCW[i];
            remA = mnCRem[i];
        } else {
            Li = prvT(i, a);
            Ri = Li;
            int g1 = dist(Li, i), g2 = dist(i, Li);
            w12 = wcst(a, g1) + wcst(a, g2);
            remA = wcst(a, N) - w12;
        }
    }
    ll best = 0;
    int bj = -1;
    int aGL = -1, aGG = 0;
    ll aGW = 0;
    ll lbA = 0;
    if (actA) {
        if (sa == 2)
            lbA = bestSplit(a, N) - w12;
        else {
            ll a1 = bestSplit(a, g12) - w12;
            ll a2 = hzIns[a] < HZBIG ? remA + hzIns[a] : a1;
            lbA = a1 < a2 ? a1 : a2;
        }
    }
    auto ev = [&](int j) {
        const int bt = slotType[j];
        if (bt == a)
            return;
        mnEv++;
        ll db = 0;
        const int sb = typeSize[bt];
        if (sb >= 2 && F[bt] != 0) {
            if (sb == 2) {
                db = dMoveWF(bt, j, i);
                if (db == INVALID)
                    return;
            } else {
                mnCell(j, bt);
                int Lj = mnCL[j], gj = mnCG[j];
                int gw = dist(Lj, i);
                if (gw < gj)
                    db = wcst(bt, gw) + wcst(bt, gj - gw) - mnCW[j];
                else if (MNBC) {
                    if (mnTISt[bt] != mnSrcSt) {
                        mnTISt[bt] = mnSrcSt;
                        int L = bt ? prevCellT(bt, i) : prevVac(i);
                        int R = nxtT(L, bt);
                        mnTIV[bt] =
                            wcst(bt, dist(L, i)) + wcst(bt, dist(i, R)) - wcst(bt, dist(L, R));
                    }
                    db = mnCRem[j] + mnTIV[bt];
                } else {
                    int L, R;
                    if (!findNbFar(bt, j, i, Lj, mnCR[j], L, R))
                        return;
                    db = mnCRem[j] + wcst(bt, dist(L, i)) + wcst(bt, dist(i, R)) -
                         wcst(bt, dist(L, R));
                }
            }
        }
        const ll st = stabD(i, publicGrid[j]) + stabD(j, publicGrid[i]);
        if (lbA + db + st >= best)
            return;
        ll da = 0;
        if (actA) {
            if (sa == 2)
                da = remA + wcst(a, dist(Li, j)) + wcst(a, dist(j, Li)) - wcst(a, N);
            else {
                int gw = dist(Li, j);
                if (gw < g12)
                    da = wcst(a, gw) + wcst(a, g12 - gw) - w12;
                else {
                    if (aGL < 0 || dist(aGL, j) >= aGG) {
                        int L, R;
                        if (!findNbFar(a, i, j, Li, Ri, L, R))
                            return;
                        aGL = L;
                        aGG = dist(L, R);
                        aGW = wcst(a, aGG);
                    }
                    int gl = dist(aGL, j);
                    da = remA + wcst(a, gl) + wcst(a, aGG - gl) - aGW;
                }
            }
        }
        ll v = da + db + st;
        if (v < best) {
            best = v;
            bj = j;
        }
    };
    const int wl = mnLight                   ? ((SM_WL2 >= 0 && smT) ? SM_WL2 : MNWL2)
                   : (MD_ZW > 0 && mdZero)   ? MD_ZW
                   : (MD_MEDW > 0 && mdWeak) ? MD_MEDW
                                             : ((SM_MNW > 0 && smT) ? SM_MNW : MNW);
    int dlo = -wl, dhi = wl;
    if (MD_DIR && actA && sa >= 3 && !mnLight) {
        int g1 = dist(Li, i), h = g12 >> 1;
        if (g1 < h) {
            if (dlo < -MD_DIRB)
                dlo = -MD_DIRB;
        } else if (g1 > g12 - h) {
            if (dhi > MD_DIRB)
                dhi = MD_DIRB;
        } else {
            if (dlo < -MD_DIRB)
                dlo = -MD_DIRB;
            if (dhi > MD_DIRB)
                dhi = MD_DIRB;
        }
    }
    if (MD_FIRST && !mnLight) {
        mdSeenSt++;
        const int gA = (actA && sa >= 3) ? g12 : 0;
        for (int d = 1; d <= dhi; d++) {
            int j = i + d;
            if (j >= N)
                j -= N;
            int bt = slotType[j];
            if (mdSeenR[bt] == mdSeenSt) {
                if (MD_FIRST < 2 || dist(Li, j) >= gA)
                    continue;
            } else
                mdSeenR[bt] = mdSeenSt;
            ev(j);
        }
        for (int d = 1; d <= -dlo; d++) {
            int j = i - d;
            if (j < 0)
                j += N;
            int bt = slotType[j];
            if (mdSeenL[bt] == mdSeenSt) {
                if (MD_FIRST < 2 || dist(Li, j) >= gA)
                    continue;
            } else
                mdSeenL[bt] = mdSeenSt;
            ev(j);
        }
    } else
        for (int d = dlo; d <= dhi; d++) {
            if (d == 0)
                continue;
            int j = i + d;
            if (j < 0)
                j += N;
            else if (j >= N)
                j -= N;
            ev(j);
        }
    if ((MNGT || (SM_MNGT && smT)) && actA && sa >= 3 && !mnLight) {
        for (int side = 0; side < 2; side++) {
            int c = side ? Ri : Li;
            for (int k = 0; k < 64; k++) {
                int nc = side ? nxtT(c, a) : prvT(c, a);
                if (nc == i || nc < 0)
                    break;
                int lo = side ? c : nc, g = dist(lo, side ? nc : c);
                int dd0 = side ? dist(i, c) : dist(c, i);
                if (dd0 > ((SM_MNGT && smT) ? SM_MNGW : MNGW))
                    break;
                if (g >= 2) {
                    int mid = lo + (g >> 1);
                    if (mid >= N)
                        mid -= N;
                    const int mgr_ = (SM_MNGT && smT) ? SM_MNGR : MNGR;
                    for (int d = -mgr_; d <= mgr_; d++) {
                        int j = mid + d;
                        if (j < 0)
                            j += N;
                        else if (j >= N)
                            j -= N;
                        if (j == i)
                            continue;
                        int dd = j - i;
                        if (dd < 0)
                            dd = -dd;
                        if (dd > (N >> 1))
                            dd = N - dd;
                        if (dd <= wl)
                            continue;
                        ev(j);
                    }
                }
                c = nc;
            }
        }
    }
    if (MNM >= 0 && actA && sa >= 3 && !mnLight && !(MD_MEDH == 0 && mdWeak) &&
        !(MD_ZH == 0 && mdZero)) {
        int mid = Li + (g12 >> 1);
        if (mid >= N)
            mid -= N;
        const int mnm_ = (SM_MNM >= 0 && smT) ? SM_MNM : ((MQ_MNM >= 0 && mqT) ? MQ_MNM : MNM);
        for (int d = -mnm_; d <= mnm_; d++) {
            int j = mid + d;
            if (j < 0)
                j += N;
            else if (j >= N)
                j -= N;
            if (j == i)
                continue;
            int dd = j - i;
            if (dd < 0)
                dd = -dd;
            if (dd > (N >> 1))
                dd = N - dd;
            if (dd <= wl)
                continue;
            ev(j);
        }
    }
    if (MNCHL > 0) {
        const int lim = mnNChg < MNCHL ? mnNChg : MNCHL;
        const int gi = publicGrid[i], oi = changeStamp[i] == operationStamp ? originalValue[i] : gi;
        for (int k = 0; k < lim; k++) {
            int j = mnChg[k];
            if (j == i)
                continue;
            if (MNCHF && originalValue[j] != gi && publicGrid[j] != oi)
                continue;
            int dd = j - i;
            if (dd < 0)
                dd = -dd;
            if (dd > (N >> 1))
                dd = N - dd;
            if (dd <= wl)
                continue;
            ev(j);
        }
    }
    if (actA && !mnLight && !(MD_MEDH == 0 && mdWeak) && !(MD_ZH == 0 && mdZero)) {
        for (int k = 0; k < mnHoleN[a]; k++) {
            int L = mnHoleL[a][k], g = mnHoleG[a][k];
            int mid = L + (g >> 1);
            if (mid >= N)
                mid -= N;
            const int mnr_ = (SM_MNR >= 0 && smT) ? SM_MNR : ((MQ_MNR >= 0 && mqT) ? MQ_MNR : MNR);
            for (int d = -mnr_; d <= mnr_; d++) {
                int j = mid + d;
                if (j < 0)
                    j += N;
                else if (j >= N)
                    j -= N;
                if (j == i)
                    continue;
                int dd = j - i;
                if (dd < 0)
                    dd = -dd;
                if (dd > (N >> 1))
                    dd = N - dd;
                if (dd <= wl)
                    continue;
                ev(j);
            }
        }
    }
    bjOut = bj;
    return best;
}
struct MnCX {
    int st, L, R, g;
    ll w, rem;
};
MnCX mnCX[MAXN];
ll mnStT[5];
#define MNCHA (SM_MNCH > MNCH ? SM_MNCH : MNCH)
int mnChgO[MNCHA > 0 ? MNCHA : 1];
int mnChgG[MNCHA > 0 ? MNCHA : 1];
int mnChgK[MAXN], mnChgS[MAXN];
#if MNCHA > 64
#error "SX_MN needs MNCH <= 64"
#endif
ull mnHO[256], mnHG[256];
ll mnLbOwn = 0;
#if SP_OMC == 1 || (SP_OMC == 2 && !defined(__clang__))
#define SP_OMC_ON 1
#else
#define SP_OMC_ON 0
#endif
__attribute__((always_inline)) inline void mnCellXFill(int j, int t) {
    MnCX &e = mnCX[j];
    e.st = mnStamp;
    int L = prvT(j, t), R = nxtT(j, t);
    int g1 = dist(L, j), g2 = dist(j, R);
    ll w = SP_WC2 ? wcst2(t, g1, g2) : wcst(t, g1) + wcst(t, g2);
    e.L = L;
    e.R = R;
    e.g = g1 + g2;
    e.w = w;
    e.rem = wcst(t, g1 + g2) - w;
}
__attribute__((always_inline)) inline void mnCellX(int j, int t) {
    if (mnCX[j].st != mnStamp)
        mnCellXFill(j, t);
}
SP2_I ll mnLbX(int i) {
    int t = slotType[i], st = typeSize[t];
    ll lb = 0;
    if (st >= 2 && F[t] != 0) {
        mnEnsureIns(t);
        if (st == 2)
            lb = lbCell(i, t, st);
        else {
            mnCellX(i, t);
            const MnCX &e = mnCX[i];
            ll a1 = bestSplit(t, e.g) - e.w;
            ll a2 = hzIns[t] < HZBIG ? e.rem + hzIns[t] : a1;
            lb = a1 < a2 ? a1 : a2;
        }
    }
    mnLbOwn = lb;
    return lb + (changedNow(i) ? -thrM : thrM);
}
int xlsXSweep(int x, int nq) {
    const int st = typeSize[x];
    int c = typeHead[x];
    if (st < 3 || F[x] == 0 || !SP4_EIT) {
        for (int k = 0; k < st; k++) {
            if (mnInQ[c] != mnStamp) {
                mnInQ[c] = mnStamp;
                mnQ[nq++] = c;
            }
            c = nextSame[c];
        }
        return nq;
    }
    const int stamp = mnStamp, nn = N;
    const bool doIns = mnInsSt[x] != stamp;
    const int mk_ = (SM_MNK > 0 && smT) ? SM_MNK : ((MQ_MNK > 0 && mqT) ? MQ_MNK : MNK);
    if (doIns) {
        mnInsSt[x] = stamp;
        mnHoleN[x] = 0;
        hzIns[x] = HZBIG;
    }
    ll mn = HZBIG;
    const int qt_ = qv[x], rb_ = (x << 6) + 32 - qt_;
    const int c0 = c;
    int g0 = 0, cPrev = -1, gPrev = 0;
    ll wg0 = 0, wgPrev = 0;
    for (int k = 0; k < st; k++) {
        const int nx = nextSame[c];
        int g = nx - c;
        if (g <= 0)
            g += nn;
        const unsigned kg_ = (unsigned)(g - qt_ + 32);
        const ll wg = kg_ < 64u ? wdt[rb_ + g] : wcst(x, g);
        if (doIns && g >= 2) {
            const int h_ = g >> 1;
            const unsigned kh_ = (unsigned)(h_ - qt_ + 32), kr_ = (unsigned)(g - h_ - qt_ + 32);
            const ll v = ((kg_ | kh_ | kr_) < 64u)
                             ? wdt[rb_ + h_] + wdt[rb_ + g - h_] - wdt[rb_ + g]
                             : bestSplit(x, g) - wcst(x, g);
            if (v < mn)
                mn = v;
            if (v < 0 && (mnHoleN[x] < mk_ || v < mnHoleV[x][mnHoleN[x] - 1]))
                mnHoleIns(x, c, g, v);
        }
        if (mnInQ[c] != stamp) {
            mnInQ[c] = stamp;
            mnQ[nq++] = c;
        }
        if (k == 0) {
            g0 = g;
            wg0 = wg;
        } else if (mnCX[c].st != stamp) {
            MnCX &e = mnCX[c];
            const int gg = gPrev + g;
            const ll w = wgPrev + wg;
            e.st = stamp;
            e.L = cPrev;
            e.R = nx;
            e.g = gg;
            e.w = w;
            e.rem = wcst(x, gg) - w;
        }
        cPrev = c;
        gPrev = g;
        wgPrev = wg;
        c = nx;
    }
    if (mnCX[c0].st != stamp) {
        MnCX &e = mnCX[c0];
        const int gg = gPrev + g0;
        const ll w = wgPrev + wg0;
        e.st = stamp;
        e.L = cPrev;
        e.R = nextSame[c0];
        e.g = gg;
        e.w = w;
        e.rem = wcst(x, gg) - w;
    }
    if (doIns)
        hzIns[x] = mn;
    return nq;
}
__attribute__((noinline)) void sp4TI(int bt, int i) {
    mnTISt[bt] = mnSrcSt;
    int L = bt ? prevCellT(bt, i) : prevVac(i);
    int R = nxtT(L, bt);
    mnTIV[bt] = wcst(bt, dist(L, i)) + wcst(bt, dist(i, R)) - wcst(bt, dist(L, R));
}
#define XLS_WIA __attribute__((always_inline)) inline
int sp4CJ[264];
ll sp4CD[264];
int sp4NEv = 0;
#define SP4_APP(j_, v_)                                                                            \
    {                                                                                              \
        sp4CJ[nc] = (j_);                                                                          \
        sp4CD[nc] = (v_);                                                                          \
        nc += (v_) < lim;                                                                          \
    }
#define SP4_OJ(jj_, gj)                                                                            \
    const int sm_ = -(int)(changeStamp[jj_] == op);                                                \
    const int oj = (gj) ^ ((originalValue[jj_] ^ (gj)) & sm_);
#define SP4_NF(jj_)                                                                                \
    {                                                                                              \
        if (gw < g) {                                                                              \
            const int g2 = g - gw;                                                                 \
            ll c;                                                                                  \
            if (bt == 0)                                                                           \
                c = g < TBe ? wctab0[gw] + wctab0[g2] : wcst2(0, gw, g2);                          \
            else {                                                                                 \
                const int q = qv[bt];                                                              \
                const unsigned k1 = (unsigned)(gw - q + 32), k2 = (unsigned)(g2 - q + 32);         \
                c = (k1 | k2) < 64u ? wdt[(bt << 6) + (int)k1] + wdt[(bt << 6) + (int)k2]          \
                                    : wcst2(bt, gw, g2);                                           \
            }                                                                                      \
            db = c - ce.w;                                                                         \
        } else {                                                                                   \
            if (mnTISt[bt] != src)                                                                 \
                sp4TI(bt, i);                                                                      \
            db = ce.rem + mnTIV[bt];                                                               \
        }                                                                                          \
    }
#define SP4_EVB(j_)                                                                                \
    {                                                                                              \
        const int jj_ = (j_);                                                                      \
        const int bt = slotType[jj_];                                                              \
        if (bt == a)                                                                               \
            continue;                                                                              \
        nev++;                                                                                     \
        ll db = 0;                                                                                 \
        const int sb = typeSize[bt];                                                               \
        if (sb >= 3) {                                                                             \
            if (F[bt] != 0) {                                                                      \
                if (mnCX[jj_].st != stamp)                                                         \
                    mnCellXFill(jj_, bt);                                                          \
                const MnCX &ce = mnCX[jj_];                                                        \
                int gw = i - ce.L;                                                                 \
                if (gw <= 0)                                                                       \
                    gw += N;                                                                       \
                const int g = ce.g;                                                                \
                SP4_NF(jj_)                                                                        \
            }                                                                                      \
        } else if (sb == 2 && F[bt] != 0) {                                                        \
            db = dMoveWF(bt, jj_, i);                                                              \
            if (db == INVALID)                                                                     \
                continue;                                                                          \
        }                                                                                          \
        const int gj = publicGrid[jj_];                                                            \
        SP4_OJ(jj_, gj)                                                                            \
        const ll dbs = db + mnStT[sI + (gj != oI) + (gi != oj) - (gj != oj)];                      \
        SP4_APP(jj_, dbs)                                                                          \
    }
XLS_WIA int sp4WinB(int i, int a, int s, int e, ll lim, int sI, int gi, int oI, int nc) {
    const int stamp = mnStamp, op = operationStamp, src = mnSrcSt;
    int nev = 0;
    for (int j = s; j < e; j++)
        SP4_EVB(j)
    sp4NEv += nev;
    return nc;
}
XLS_WIA int sp4RunX(int i, int a, int c, int r, int wl, ll lim, int sI, int gi, int oI, int nc) {
    {
        const int s0 = sdisp(i, c - r < 0 ? c - r + N : c - r);
        if (s0 >= -wl && s0 + (r << 1) <= wl)
            return nc;
    }
    const int stamp = mnStamp, op = operationStamp, src = mnSrcSt;
    const unsigned span = (unsigned)(N - (wl << 1) - 1);
    int nev = 0;
    int j = c - r;
    if (j < 0)
        j += N;
    for (int d = -r; d <= r; d++, j = j + 1 == N ? 0 : j + 1) {
        int o = j - i;
        if (o < 0)
            o += N;
        if ((unsigned)(o - wl - 1) >= span)
            continue;
        SP4_EVB(j)
    }
    sp4NEv += nev;
    return nc;
}
ll mnBestX(int i, int &bjOut, ll lbA0) {
    mnSrcSt++;
    const int a = slotType[i], sa = typeSize[a];
    const bool actA = sa >= 2 && F[a] != 0;
    int Li = 0, Ri = 0, g12 = 0;
    ll w12 = 0, remA = 0;
    if (actA) {
        mnEnsureIns(a);
        if (sa >= 3) {
            mnCellX(i, a);
            const MnCX &e = mnCX[i];
            Li = e.L;
            Ri = e.R;
            g12 = e.g;
            w12 = e.w;
            remA = e.rem;
        } else {
            Li = prvT(i, a);
            Ri = Li;
            int g1 = dist(Li, i), g2 = dist(i, Li);
            w12 = wcst(a, g1) + wcst(a, g2);
            remA = wcst(a, N) - w12;
        }
    }
    const ll lbA = lbA0;
    const int gi = publicGrid[i];
    const int oI = changeStamp[i] == operationStamp ? originalValue[i] : gi;
    const int sI = 2 - (gi != oI);
    ll best = 0;
    int bj = -1;
    ll nev = 0;
    int aGL = -1, aGG = 0;
    ll aGW = 0;
    auto ev = [&](int j) __attribute__((always_inline)) {
        const int bt = slotType[j];
        if (bt == a)
            return;
        nev++;
        ll db = 0;
        const int sb = typeSize[bt];
        if (sb >= 2 && F[bt] != 0) {
            if (sb == 2) {
                db = dMoveWF(bt, j, i);
                if (db == INVALID)
                    return;
            } else {
                mnCellX(j, bt);
                const MnCX &e = mnCX[j];
                int gw = dist(e.L, i);
                if (gw < e.g)
                    db = (SP_WC2 ? wcst2(bt, gw, e.g - gw) : wcst(bt, gw) + wcst(bt, e.g - gw)) -
                         e.w;
                else if (MNBC) {
                    if (mnTISt[bt] != mnSrcSt) {
                        mnTISt[bt] = mnSrcSt;
                        int L = bt ? prevCellT(bt, i) : prevVac(i);
                        int R = nxtT(L, bt);
                        mnTIV[bt] =
                            wcst(bt, dist(L, i)) + wcst(bt, dist(i, R)) - wcst(bt, dist(L, R));
                    }
                    db = e.rem + mnTIV[bt];
                } else {
                    int L, R;
                    if (!findNbFar(bt, j, i, e.L, e.R, L, R))
                        return;
                    db = e.rem + wcst(bt, dist(L, i)) + wcst(bt, dist(i, R)) - wcst(bt, dist(L, R));
                }
            }
        }
        const int gj = publicGrid[j];
        const int oj = changeStamp[j] == operationStamp ? originalValue[j] : gj;
        const ll st = mnStT[sI + (gj != oI) + (gi != oj) - (gj != oj)];
        const ll dbs = db + st;
        if (lbA + dbs >= best)
            return;
        ll da = 0;
        if (actA) {
            if (sa == 2)
                da = remA + wcst(a, dist(Li, j)) + wcst(a, dist(j, Li)) - wcst(a, N);
            else {
                int gw = dist(Li, j);
                if (gw < g12)
                    da = (SP_WC2 ? wcst2(a, gw, g12 - gw) : wcst(a, gw) + wcst(a, g12 - gw)) - w12;
                else {
                    if (aGL < 0 || dist(aGL, j) >= aGG) {
                        int L, R;
                        if (!findNbFar(a, i, j, Li, Ri, L, R))
                            return;
                        aGL = L;
                        aGG = dist(L, R);
                        aGW = wcst(a, aGG);
                    }
                    int gl = dist(aGL, j);
                    da = remA + wcst(a, gl) + wcst(a, aGG - gl) - aGW;
                }
            }
        }
        const ll v = da + dbs;
        if (v < best) {
            best = v;
            bj = j;
        }
    };
    auto evA = [&](int j, ll dbs) __attribute__((always_inline)) {
        if (lbA + dbs >= best)
            return;
        ll da = 0;
        if (actA) {
            if (sa == 2)
                da = remA + wcst(a, dist(Li, j)) + wcst(a, dist(j, Li)) - wcst(a, N);
            else {
                int gw = dist(Li, j);
                if (gw < g12)
                    da = (SP_WC2 ? wcst2(a, gw, g12 - gw) : wcst(a, gw) + wcst(a, g12 - gw)) - w12;
                else {
                    if (aGL < 0 || dist(aGL, j) >= aGG) {
                        int L, R;
                        if (!findNbFar(a, i, j, Li, Ri, L, R))
                            return;
                        aGL = L;
                        aGG = dist(L, R);
                        aGW = wcst(a, aGG);
                    }
                    int gl = dist(aGL, j);
                    da = remA + wcst(a, gl) + wcst(a, aGG - gl) - aGW;
                }
            }
        }
        const ll v = da + dbs;
        if (v < best) {
            best = v;
            bj = j;
        }
    };
    const int wl0_ = mnLight
                         ? ((SM_WL2 >= 0 && smT) ? SM_WL2 : ((MQ_WL2 >= 0 && mqT) ? MQ_WL2 : MNWL2))
                     : (MD_ZW > 0 && mdZero) ? MD_ZW
                     : (MD_MEDW > 0 && mdWeak)
                         ? MD_MEDW
                         : ((SM_MNW > 0 && smT)
                                ? SM_MNW
                                : ((LGM_RBW > 0 && lgmL && mdRbOp) ? LGM_RBW
                                   : (LGM_MNW > 0 && lgmL)
                                       ? LGM_MNW
                                       : ((MQ_MNW > 0 && mqT)
                                              ? MQ_MNW
                                              : ((MD2S_MNW > 0 && N <= MD2_SN) ? MD2S_MNW : MNW))));
    const int wl = (sqWl > 0 && !mnLight) ? (sqWl < ((N - 1) >> 1) ? sqWl : ((N - 1) >> 1)) : wl0_;
    int dlo = -wl, dhi = wl;
    if (MD_DIR && actA && sa >= 3 && !mnLight) {
        int g1 = dist(Li, i), h = g12 >> 1;
        if (g1 < h) {
            if (dlo < -MD_DIRB)
                dlo = -MD_DIRB;
        } else if (g1 > g12 - h) {
            if (dhi > MD_DIRB)
                dhi = MD_DIRB;
        } else {
            if (dlo < -MD_DIRB)
                dlo = -MD_DIRB;
            if (dhi > MD_DIRB)
                dhi = MD_DIRB;
        }
    }
    if (MD_FIRST && !mnLight) {
        mdSeenSt++;
        const int gA = (actA && sa >= 3) ? g12 : 0;
        for (int d = 1; d <= dhi; d++) {
            int j = i + d;
            if (j >= N)
                j -= N;
            int bt = slotType[j];
            if (mdSeenR[bt] == mdSeenSt) {
                if (MD_FIRST < 2 || dist(Li, j) >= gA)
                    continue;
            } else
                mdSeenR[bt] = mdSeenSt;
            ev(j);
        }
        for (int d = 1; d <= -dlo; d++) {
            int j = i - d;
            if (j < 0)
                j += N;
            int bt = slotType[j];
            if (mdSeenL[bt] == mdSeenSt) {
                if (MD_FIRST < 2 || dist(Li, j) >= gA)
                    continue;
            } else
                mdSeenL[bt] = mdSeenSt;
            ev(j);
        }
    } else if (RM_FI >= 2) {
        const int dm = dhi > -dlo ? dhi : -dlo;
        for (int d = 1; d <= dm && best >= 0; d++) {
            if (d <= dhi) {
                int j = i + d;
                if (j >= N)
                    j -= N;
                ev(j);
            }
            if (d <= -dlo && best >= 0) {
                int j = i - d;
                if (j < 0)
                    j += N;
                ev(j);
            }
        }
    } else if (SP4_MNW >= 3 && dhi - dlo <= 256) {
        const ll lim = best - lbA;
        int nc = 0;
        int s = i + dlo;
        if (s < 0) {
            nc = sp4WinB(i, a, s + N, N, lim, sI, gi, oI, nc);
            s = 0;
        }
        nc = sp4WinB(i, a, s, i, lim, sI, gi, oI, nc);
        int e = i + dhi;
        if (e >= N) {
            nc = sp4WinB(i, a, i + 1, N, lim, sI, gi, oI, nc);
            nc = sp4WinB(i, a, 0, e - N + 1, lim, sI, gi, oI, nc);
        } else
            nc = sp4WinB(i, a, i + 1, e + 1, lim, sI, gi, oI, nc);
        nev += sp4NEv;
        sp4NEv = 0;
        for (int k = 0; k < nc; k++)
            evA(sp4CJ[k], sp4CD[k]);
    } else
        for (int d = dlo; d <= dhi; d++) {
            if (d == 0)
                continue;
            int j = i + d;
            if (j < 0)
                j += N;
            else if (j >= N)
                j -= N;
            ev(j);
        }
    if (RM_FI >= 1 && best < 0) {
        mnEv += nev;
        bjOut = bj;
        return best;
    }
    if ((MNGT || (SM_MNGT && smT)) && actA && sa >= 3 && !mnLight) {
        for (int side = 0; side < 2; side++) {
            int c = side ? Ri : Li;
            for (int k = 0; k < 64; k++) {
                int nc = side ? nxtT(c, a) : prvT(c, a);
                if (nc == i || nc < 0)
                    break;
                int lo = side ? c : nc, g = dist(lo, side ? nc : c);
                int dd0 = side ? dist(i, c) : dist(c, i);
                if (dd0 > ((SM_MNGT && smT) ? SM_MNGW : MNGW))
                    break;
                if (g >= 2) {
                    int mid = lo + (g >> 1);
                    if (mid >= N)
                        mid -= N;
                    const int mgr_ = (SM_MNGT && smT) ? SM_MNGR : MNGR;
                    for (int d = -mgr_; d <= mgr_; d++) {
                        int j = mid + d;
                        if (j < 0)
                            j += N;
                        else if (j >= N)
                            j -= N;
                        if (j == i)
                            continue;
                        int dd = j - i;
                        if (dd < 0)
                            dd = -dd;
                        if (dd > (N >> 1))
                            dd = N - dd;
                        if (dd <= wl)
                            continue;
                        ev(j);
                    }
                }
                c = nc;
            }
        }
    }
    if (MNM >= 0 && actA && sa >= 3 && !mnLight && !(MD_MEDH == 0 && mdWeak) &&
        !(MD_ZH == 0 && mdZero) && !(MD2_MEDH == 0 && md2NoMH)) {
        int mid = Li + (g12 >> 1);
        if (mid >= N)
            mid -= N;
        const int mnm_ = (SM_MNM >= 0 && smT) ? SM_MNM : ((MQ_MNM >= 0 && mqT) ? MQ_MNM : MNM);
        if (mnm_ <= 128 && N > (wl << 1) + 1) {
            const int nc = sp4RunX(i, a, mid, mnm_, wl, best - lbA, sI, gi, oI, 0);
            nev += sp4NEv;
            sp4NEv = 0;
            for (int k = 0; k < nc; k++)
                evA(sp4CJ[k], sp4CD[k]);
        } else
            for (int d = -mnm_; d <= mnm_; d++) {
                int j = mid + d;
                if (j < 0)
                    j += N;
                else if (j >= N)
                    j -= N;
                if (j == i)
                    continue;
                int dd = j - i;
                if (dd < 0)
                    dd = -dd;
                if (dd > (N >> 1))
                    dd = N - dd;
                if (dd <= wl)
                    continue;
                ev(j);
            }
    }
    if (MNCHL > 0) {
        const int hN = N >> 1;
        if (MNCHF) {
            ull m = mnHO[gi & 255] | mnHG[oI & 255];
            while (m) {
                const int k = __builtin_ctzll(m);
                m &= m - 1;
                if (mnChgO[k] != gi && mnChgG[k] != oI)
                    continue;
                int j = mnChg[k];
                if (j == i)
                    continue;
                int dd = j - i;
                if (dd < 0)
                    dd = -dd;
                if (dd > hN)
                    dd = N - dd;
                if (dd <= wl)
                    continue;
                ev(j);
            }
        } else {
            const int lim = mnNChg < MNCHL ? mnNChg : MNCHL;
            for (int k = 0; k < lim; k++) {
                int j = mnChg[k];
                if (j == i)
                    continue;
                int dd = j - i;
                if (dd < 0)
                    dd = -dd;
                if (dd > hN)
                    dd = N - dd;
                if (dd <= wl)
                    continue;
                ev(j);
            }
        }
    }
    if (actA && !mnLight && !(MD_MEDH == 0 && mdWeak) && !(MD_ZH == 0 && mdZero) &&
        !(MD2_MEDH == 0 && md2NoMH)) {
        for (int k = 0; k < mnHoleN[a]; k++) {
            int L = mnHoleL[a][k], g = mnHoleG[a][k];
            int mid = L + (g >> 1);
            if (mid >= N)
                mid -= N;
            const int mnr_ = (SM_MNR >= 0 && smT) ? SM_MNR : ((MQ_MNR >= 0 && mqT) ? MQ_MNR : MNR);
            if (mnr_ <= 128 && N > (wl << 1) + 1) {
                const int nc = sp4RunX(i, a, mid, mnr_, wl, best - lbA, sI, gi, oI, 0);
                nev += sp4NEv;
                sp4NEv = 0;
                for (int q = 0; q < nc; q++)
                    evA(sp4CJ[q], sp4CD[q]);
                continue;
            }
            for (int d = -mnr_; d <= mnr_; d++) {
                int j = mid + d;
                if (j < 0)
                    j += N;
                else if (j >= N)
                    j -= N;
                if (j == i)
                    continue;
                int dd = j - i;
                if (dd < 0)
                    dd = -dd;
                if (dd > (N >> 1))
                    dd = N - dd;
                if (dd <= wl)
                    continue;
                ev(j);
            }
        }
    }
    mnEv += nev;
    bjOut = bj;
    return best;
}
#define EH_MNC0 1000000
#define EH_MNCAP 2000000
#define EH_MNHK 0
ll mnEvLim = MNEV;
ll ehMnCredit = EH_MNC0;
#define RM_GP 0
#define RM_GH 80
#define RM_GSW 64
#define RM_GSRC 1024
#define RM_GEV 20000
int rmAll = 0;
int sqSrcOv = 0;
#define RM_TK 16
#define RM_HK 0
#define RM_HMAX 40
#define RM_VSC 0
#define RM_PN 0
#define RM_MNP 256
#define RM_SRC 1024
int rmNox = 0;
extern unsigned char hcT[MAXT];
ll totalLayoutPenalty();
#define MD2_DS 0
#define MD2_DSLO 1000
#define MD2_DSX 0
#define MD2_DSSH 0
#define MD2_DSPC 0
#define MD2_GPN 100000
#define MD2_TKL 16
#define MD2_TKS 16
#define MD2_TKSH 4
#define MD2_TKH 16
#define MD2_TKX 16
ll tsCbar16 = 0;
#if SP2_SORT == 1 || (SP2_SORT == 2 && SP2_O0CMD)
#define SP2_SORT_ON 1
#else
#define SP2_SORT_ON 0
#endif
#if SP2_SORT_ON
struct SP2KV {
    ll k;
    int v;
};
SP2KV sp2A[MAXN + 64], sp2B[MAXN + 64];
SP2_I bool sp2Lt(const SP2KV &x, const SP2KV &y) {
    return x.k < y.k || (x.k == y.k && x.v < y.v);
}
void sp2SortKV(int n) {
    for (int s = 0; s < n; s += 16) {
        const int e = s + 16 < n ? s + 16 : n;
        for (int i = s + 1; i < e; i++) {
            const SP2KV x = sp2A[i];
            int j = i;
            while (j > s && sp2Lt(x, sp2A[j - 1])) {
                sp2A[j] = sp2A[j - 1];
                j--;
            }
            sp2A[j] = x;
        }
    }
    bool inA = true;
    for (int w = 16; w < n; w <<= 1) {
        auto src = inA ? sp2A : sp2B;
        auto dst = inA ? sp2B : sp2A;
        for (int s = 0; s < n; s += w << 1) {
            const int m = s + w < n ? s + w : n, e = s + (w << 1) < n ? s + (w << 1) : n;
            int i = s, j = m, k = s;
            while (i < m && j < e) {
                if (sp2Lt(src[j], src[i]))
                    dst[k++] = src[j++];
                else
                    dst[k++] = src[i++];
            }
            while (i < m)
                dst[k++] = src[i++];
            while (j < e)
                dst[k++] = src[j++];
        }
        inA = !inA;
    }
    if (!inA)
        for (int i = 0; i < n; i++)
            sp2A[i] = sp2B[i];
}
void sp2Select(int n, int k) {
    int lo = 0, hi = n;
    while (hi - lo > 16) {
        const int mid = lo + ((hi - lo) >> 1);
        const SP2KV a = sp2A[lo], b = sp2A[mid], c = sp2A[hi - 1];
        const SP2KV pv = sp2Lt(a, b) ? (sp2Lt(b, c) ? b : (sp2Lt(a, c) ? c : a))
                                     : (sp2Lt(a, c) ? a : (sp2Lt(b, c) ? c : b));
        int i = lo - 1, j = hi;
        for (;;) {
            do
                i++;
            while (sp2Lt(sp2A[i], pv));
            do
                j--;
            while (sp2Lt(pv, sp2A[j]));
            if (i >= j)
                break;
            const SP2KV t = sp2A[i];
            sp2A[i] = sp2A[j];
            sp2A[j] = t;
        }
        if (k <= j)
            hi = j + 1;
        else
            lo = j + 1;
    }
    for (int i = lo + 1; i < hi; i++) {
        const SP2KV x = sp2A[i];
        int j = i;
        while (j > lo && sp2Lt(x, sp2A[j - 1])) {
            sp2A[j] = sp2A[j - 1];
            j--;
        }
        sp2A[j] = x;
    }
}
#endif
ull sp4Key[MAXN + 64];
#define HVB_MNFL 0
#define HVB_MNF 0
// 利用候选下界和局部缓存选择交换，限制实际搜索工作量。
int mnDescent(int maxSw, int x, bool sweep) {
    mnStamp++;
    int nq = 0;
    mnNChg = 0;
    {
        const int o = operationStamp;
        int i0 = 0;
        if (xlsSBon) {
            const int nw_ = NW;
            for (int w = 0; w < nw_; w++) {
                ull m = xlsSB[w];
                while (m) {
                    const int i = (w << 6) + __builtin_ctzll(m);
                    m &= m - 1;
                    mnQ[nq++] = i;
                    mnInQ[i] = mnStamp;
                    if (publicGrid[i] != originalValue[i])
                        mnChg[mnNChg++] = i;
                }
            }
            i0 = N;
        } else
#define LGM_SCN 0
            if (LGM_SCN) {
            const int stp = mnStamp;
            for (; i0 + 16 <= N; i0 += 16) {
                int any = 0;
                for (int k = 0; k < 16; k++)
                    any |= changeStamp[i0 + k] == o;
                if (!any)
                    continue;
                unsigned m = 0;
                for (int k = 0; k < 16; k++)
                    m |= (unsigned)(changeStamp[i0 + k] == o) << k;
                while (m) {
                    const int i = i0 + __builtin_ctz(m);
                    m &= m - 1;
                    mnQ[nq++] = i;
                    mnInQ[i] = stp;
                    mnChg[mnNChg] = i;
                    mnNChg += publicGrid[i] != originalValue[i];
                }
            }
        } else
            for (; i0 + 16 <= N; i0 += 16) {
                int any = 0;
                for (int k = 0; k < 16; k++)
                    any |= changeStamp[i0 + k] == o;
                if (!any)
                    continue;
                for (int i = i0; i < i0 + 16; i++)
                    if (changeStamp[i] == o) {
                        mnQ[nq++] = i;
                        mnInQ[i] = mnStamp;
                        if (publicGrid[i] != originalValue[i])
                            mnChg[mnNChg++] = i;
                    }
            }
        for (int i = i0; i < N; i++)
            if (changeStamp[i] == o) {
                mnQ[nq++] = i;
                mnInQ[i] = mnStamp;
                if (publicGrid[i] != originalValue[i])
                    mnChg[mnNChg++] = i;
            }
    }
    {
        const int lim = mnNChg < MNCHL ? mnNChg : MNCHL;
        for (int k = 0; k < lim; k++) {
            int j = mnChg[k];
            mnChgO[k] = originalValue[j];
            mnChgG[k] = publicGrid[j];
            mnChgK[j] = k;
            mnChgS[j] = mnStamp;
            mnHO[originalValue[j] & 255] |= 1ULL << k;
            mnHG[publicGrid[j] & 255] |= 1ULL << k;
        }
    }
#define MNLBF mnLbX
    if ((!MD_NOX || rmNox) && x > 0 && typeHead[x] >= 0) {
        nq = xlsXSweep(x, nq);
    }
    if (MD2_DS > 0 && !rmAll && N > MD2_DSLO) {
        totalLayoutPenalty();
        int sel[4];
        ll sv[4];
        int ns2 = 0;
        const int kmax = MD2_DS < 1 ? 1 : (MD2_DS < 4 ? MD2_DS : 4);
        for (int t = 1; t < typeSlotCount; t++) {
            int sc = typeSize[t];
            if (sc < 3 || F[t] == 0 || (!MD2_DSX && t == x))
                continue;
            if (MD2_DSSH > 0 && ((ll)sc << MD2_DSSH) < N)
                continue;
            ll r = rv[t];
            ll ex = PtC[t] - multiplyNonnegative(multiplyNonnegative(r, sc - r) << 1, F[t]);
            if (MD2_DSPC)
                ex = divideNonnegative(ex, sc);
            if (ex <= 0)
                continue;
            int k2 = ns2 < kmax ? ns2++ : kmax;
            if (k2 == kmax) {
                if (ex <= sv[kmax - 1])
                    continue;
                k2 = kmax - 1;
            }
            while (k2 > 0 && sv[k2 - 1] < ex) {
                sv[k2] = sv[k2 - 1];
                sel[k2] = sel[k2 - 1];
                k2--;
            }
            sv[k2] = ex;
            sel[k2] = t;
        }
        for (int u = 0; u < ns2; u++) {
            int t = sel[u], c = typeHead[t], st = typeSize[t];
            for (int k = 0; k < st; k++) {
                if (mnInQ[c] != mnStamp) {
                    mnInQ[c] = mnStamp;
                    mnQ[nq++] = c;
                }
                c = nextSame[c];
            }
        }
    }
    if (MQ_NBS > 0 && mqT && !rmAll && MQG(1)) {
        const int nq0 = nq;
        for (int k = 0; k < nq0; k++) {
            const int i = mnQ[k];
            if (changeStamp[i] != operationStamp)
                continue;
            for (int d = -MQ_NBS; d <= MQ_NBS; d++) {
                int j = i + d;
                if (j < 0)
                    j += N;
                else if (j >= N)
                    j -= N;
                if (MQ_NBV == 1 && slotType[j] != 0)
                    continue;
                if (MQ_NBV == 2 && slotType[j] == 0)
                    continue;
                if (mnInQ[j] != mnStamp) {
                    mnInQ[j] = mnStamp;
                    mnQ[nq++] = j;
                    if (MQ_NBK > 0)
                        smNbSt[j] = mnStamp;
                }
            }
        }
    }
    if (MQ_TNB && mqT && !rmAll && MQG(1)) {
        const int nq0 = nq;
        auto addQ = [&](int j) {
            if (j >= 0 && mnInQ[j] != mnStamp) {
                mnInQ[j] = mnStamp;
                mnQ[nq++] = j;
                if (MQ_NBK > 0)
                    smNbSt[j] = mnStamp;
            }
        };
        for (int k = 0; k < nq0; k++) {
            const int i = mnQ[k];
            if (changeStamp[i] != operationStamp)
                continue;
            const int t = slotType[i];
            if ((MQ_TNB & 1) && typeSize[t] >= 2) {
                addQ(prvT(i, t));
                addQ(nxtT(i, t));
            }
            if ((MQ_TNB & 2) && originalValue[i] != publicGrid[i]) {
                auto it = typeIndex.find(originalValue[i]);
                if (it != typeIndex.end()) {
                    const int y = it->second;
                    if (y != t && typeSize[y] >= 1) {
                        if (y == 0) {
                            addQ(prevVac(i));
                            addQ(nextVac(i));
                        } else {
                            addQ(prevCellT(y, i));
                            addQ(nextCellT(y, i));
                        }
                    }
                }
            }
        }
    }
    if (SM_NBS > 0 && smT && !rmAll) {
        const int nq0 = nq;
        for (int k = 0; k < nq0; k++) {
            const int i = mnQ[k];
            if (changeStamp[i] != operationStamp)
                continue;
            for (int d = -SM_NBS; d <= SM_NBS; d++) {
                int j = i + d;
                if (j < 0)
                    j += N;
                else if (j >= N)
                    j -= N;
                if (SM_NBV == 1 && slotType[j] != 0)
                    continue;
                if (SM_NBV == 2 && slotType[j] == 0)
                    continue;
                if (mnInQ[j] != mnStamp) {
                    mnInQ[j] = mnStamp;
                    mnQ[nq++] = j;
                    if (SM_NBK > 0)
                        smNbSt[j] = mnStamp;
                }
            }
        }
    }
    if (SM_TNB && smT && !rmAll) {
        const int nq0 = nq;
        auto addQ = [&](int j) {
            if (j >= 0 && mnInQ[j] != mnStamp) {
                mnInQ[j] = mnStamp;
                mnQ[nq++] = j;
            }
        };
        for (int k = 0; k < nq0; k++) {
            const int i = mnQ[k];
            if (changeStamp[i] != operationStamp)
                continue;
            const int t = slotType[i];
            if ((SM_TNB & 1) && typeSize[t] >= 2) {
                addQ(prvT(i, t));
                addQ(nxtT(i, t));
            }
            if ((SM_TNB & 2) && originalValue[i] != publicGrid[i]) {
                auto it = typeIndex.find(originalValue[i]);
                if (it != typeIndex.end()) {
                    const int y = it->second;
                    if (y != t && typeSize[y] >= 1) {
                        if (y == 0) {
                            addQ(prevVac(i));
                            addQ(nextVac(i));
                        } else {
                            addQ(prevCellT(y, i));
                            addQ(nextCellT(y, i));
                        }
                    }
                }
            }
        }
    }
    if (SM_HCTS && smT && !rmAll) {
        for (int i = 0; i < N; i++) {
            int t = slotType[i];
            if (t > 0 && hcT[t] && mnInQ[i] != mnStamp) {
                mnInQ[i] = mnStamp;
                mnQ[nq++] = i;
            }
        }
    }
    if (rmAll) {
        for (int i = 0; i < N; i++)
            if (mnInQ[i] != mnStamp) {
                mnInQ[i] = mnStamp;
                mnQ[nq++] = i;
            }
    }
    if (sweep && typeSize[0] >= 3 && F[0] != 0) {
        mnEnsureIns(0);
        int p0 = -1, p1 = -1;
        const ll mn0 = hzIns[0];
        for (int w = 0; w < NW; w++) {
            ull m = vb[w];
            while (m) {
                int v = (w << 6) + __builtin_ctzll(m);
                m &= m - 1;
                if (p0 >= 0 && mnInQ[p1] != mnStamp) {
                    int g1 = p1 - p0, g2 = v - p1;
                    ll w12 = wcst(0, g1) + wcst(0, g2);
                    ll a1 = bestSplit(0, g1 + g2) - w12;
                    ll a2 = mn0 < HZBIG ? wcst(0, g1 + g2) - w12 + mn0 : a1;
                    if ((a1 < a2 ? a1 : a2) + thrM < 0) {
                        mnInQ[p1] = mnStamp;
                        mnQ[nq++] = p1;
                    }
                }
                p0 = p1;
                p1 = v;
            }
        }
    }
    if (HVB_MNF && N > MNHI && !rmAll) {
        int k2 = 0;
        for (int k = 0; k < nq; k++) {
            const int i = mnQ[k], t = slotType[i];
            if (t == x || t == 0)
                mnQ[k2++] = i;
            else
                mnInQ[i] = 0;
        }
        nq = k2;
    }
    int ns = 0;
    if (MQ_NBK > 0 && (MQ_NBS > 0 || MQ_TNB) && mqT && !rmAll) {
        const ll nbt = multiplyNonnegative(thrM, MQ_NBK) >> 4;
        for (int k = 0; k < nq; k++) {
            int i = mnQ[k];
            ll lb = MNLBF(i);
            if (lb < 0 && (smNbSt[i] != mnStamp || lb + nbt < 0)) {
                mnQv[i] = lb;
                mnQ[ns++] = i;
            } else
                mnInQ[i] = 0;
        }
    } else if (SM_NBK > 0 && SM_NBS > 0 && smT && !rmAll) {
        const ll nbt = multiplyNonnegative(thrM, SM_NBK) >> 4;
        for (int k = 0; k < nq; k++) {
            int i = mnQ[k];
            ll lb = MNLBF(i);
            if (lb < 0 && (smNbSt[i] != mnStamp || lb + nbt < 0)) {
                mnQv[i] = lb;
                mnQ[ns++] = i;
            } else
                mnInQ[i] = 0;
        }
    } else {
        const int stp = mnStamp;
        for (int k = 0; k < nq; k++) {
            const int i = mnQ[k];
            const ll lb = MNLBF(i);
            const int ok = lb < 0;
            mnQv[i] = lb;
            mnQ[ns] = i;
            ns += ok;
            mnInQ[i] = ok ? stp : 0;
        }
    }
    const int srcCap =
        sqSrcOv > 0 ? sqSrcOv
        : rmAll     ? (smT && SM_GP > 0 ? SM_GSRC : RM_GSRC)
                    : ((SM_MNSRC > 0 && smT)
                           ? SM_MNSRC
                           : ((RM_PN > 0 && N > RM_PN)           ? (mdRbOp ? (RM_SRC << 1) : RM_SRC)
                              : (LGM_SRC > 0 && lgmL && !mdRbOp) ? LGM_SRC
                              : (LGM_RBS > 0 && lgmL && mdRbOp)
                                  ? LGM_RBS
                                  : ((MQ_MNSRCR > 0 && mqT && mdRbOp && MQG(2))
                                         ? MQ_MNSRCR
                                         : ((MQ_MNSRC > 0 && mqT && !mdRbOp && MQG(2))
                                                ? MQ_MNSRC
                                                : ((MD_RBS > 0 && mdRbOp) ? MD_RBS : EH_MNSRC)))));
#if SP2_SORT_ON
    {
        for (int k = 0; k < ns; k++) {
            const int i = mnQ[k];
            sp2A[k].k = mnQv[i];
            sp2A[k].v = i;
        }
        if (srcCap > 0 && ns > srcCap) {
            sp2Select(ns, srcCap);
            for (int k = srcCap; k < ns; k++)
                mnInQ[sp2A[k].v] = 0;
            ns = srcCap;
        }
        sp2SortKV(ns);
        for (int k = 0; k < ns; k++)
            mnQ[k] = sp2A[k].v;
    }
#else
    bool sp4Done = false;
    if (ns > 1 && N <= 16384) {
        ull kmn = (ull)mnQv[mnQ[0]], kmx = kmn;
        for (int k = 1; k < ns; k++) {
            const ll v = mnQv[mnQ[k]];
            if (v < (ll)kmn)
                kmn = (ull)v;
            if (v > (ll)kmx)
                kmx = (ull)v;
        }
        if (kmx - kmn < (1ULL << 49)) {
            for (int k = 0; k < ns; k++) {
                const int c = mnQ[k];
                sp4Key[k] = (((ull)mnQv[c] - kmn) << 14) | (ull)c;
            }
            if (srcCap > 0 && ns > srcCap) {
                nth_element(sp4Key, sp4Key + srcCap, sp4Key + ns);
                for (int k = srcCap; k < ns; k++)
                    mnInQ[(int)(sp4Key[k] & 16383)] = 0;
                ns = srcCap;
            }
            sort(sp4Key, sp4Key + ns);
            for (int k = 0; k < ns; k++)
                mnQ[k] = (int)(sp4Key[k] & 16383);
            sp4Done = true;
        }
    }
    if (!sp4Done) {
        if (srcCap > 0 && ns > srcCap) {
            nth_element(mnQ, mnQ + srcCap, mnQ + ns, [](int u, int v) {
                return mnQv[u] < mnQv[v] || (mnQv[u] == mnQv[v] && u < v);
            });
            for (int k = srcCap; k < ns; k++)
                mnInQ[mnQ[k]] = 0;
            ns = srcCap;
        }
        if (MD_FAST) {
            for (int k = 0; k < ns; k++)
                mdSortA[k] = make_pair(mnQv[mnQ[k]], mnQ[k]);
            sort(mdSortA, mdSortA + ns);
            for (int k = 0; k < ns; k++)
                mnQ[k] = mdSortA[k].second;
        } else
            sort(mnQ, mnQ + ns,
                 [](int u, int v) { return mnQv[u] < mnQv[v] || (mnQv[u] == mnQv[v] && u < v); });
    }
#endif
    const int QC = (MAXN << 1) + 64;
    int head = 0, tail = ns, done = 0;
    mnEv = 0;
    int mdFails = 0;
    const int mdFl =
        (HVB_MNFL > 0 && N > MNHI) ? HVB_MNFL : ((LGM_FAIL > 0 && lgmL) ? LGM_FAIL : MD_FAIL);
    while (head < tail && done < maxSw && mnEv < mnEvLim && (mdFl == 0 || mdFails < mdFl)) {
        int i = mnQ[head];
        head++;
        mnInQ[i] = 0;
        ll lbi = MNLBF(i);
        if (lbi >= 0)
            continue;
        mnLight = MNSF == 2 && changeStamp[i] == operationStamp && changedNow(i) && lbi + thrM >= 0;
        mdWeak = MD_MEDW > 0 && !(SM_MEDW == 0 && smT) && !(MQ_MEDW == 0 && mqT) && !mnLight &&
                 lbi + (thrM << MD_MEDK) > 0;
        mdZero = MD_ZW > 0 && !(SM_ZW == 0 && smT) && !(MQ_ZW == 0 && mqT) && !mnLight &&
                 lbi + thrM == 0 && changeStamp[i] == operationStamp && changedNow(i);
        if (MQ_STS >= -1 && mqT && MQG(4)) {
            if (MQ_STS >= 0 && !mnLight && lbi + (thrM >> MQ_STS) > 0)
                continue;
        } else if (MNSTS >= 0 && !mnLight && lbi + (thrM >> MNSTS) > 0)
            continue;
        if (MD_STV >= 0 && !mnLight && slotType[i] == 0 && lbi + (thrM << MD_STV) > 0)
            continue;
        if (MQ_STV >= -1 && mqT && MQG(4)) {
            if (MQ_STV >= 0 && !mnLight && slotType[i] == 0 && lbi + (thrM << MQ_STV) > 0)
                continue;
        } else if (MD2_STV >= 0 && N > MD2_CUTLO && !mnLight && slotType[i] == 0 &&
                   lbi + (thrM << MD2_STV) > 0)
            continue;
        if (MD2_STT >= 0 && N > MD2_CUTLO && !mnLight && slotType[i] != 0 &&
            lbi + (thrM << MD2_STT) > 0)
            continue;
        if (MD2_MEDH == 0)
            md2NoMH = N > MD2_CUTLO && !mnLight && lbi + (thrM << MD2_MEDK) > 0;
        if (LGM_STV >= 0 && lgmL && !mnLight && slotType[i] == 0 && lbi + (thrM << LGM_STV) > 0)
            continue;
        if (LGM_STT >= 0 && lgmL && !mnLight && slotType[i] != 0 && lbi + (thrM << LGM_STT) > 0)
            continue;
        if (MD_STT >= 0 && !mnLight && slotType[i] != 0 && lbi + (thrM << MD_STT) > 0)
            continue;
        if (MD_LT && mnLight && (MD_LT >= 2 || slotType[i] == 0))
            continue;
        int j;
        ll v = mnBestX(i, j, mnLbOwn);
        if (j < 0 || v >= 0) {
            mdFails++;
            continue;
        }
        mdFails = 0;
        int a = slotType[i], b = slotType[j];
        int La = prvT(i, a), Ra = nxtT(i, a);
        int Lb = prvT(j, b), Rb = nxtT(j, b);
        doSwap(i, j);
        done++;
        int cand[10] = {i, j, La, Ra, Lb, Rb, prvT(j, a), nxtT(j, a), prvT(i, b), nxtT(i, b)};
        for (int k = 0; k < 10; k++)
            if (cand[k] >= 0)
                mnCX[cand[k]].st = 0;
        if (mnChgS[i] == mnStamp) {
            int k = mnChgK[i];
            mnHG[mnChgG[k] & 255] &= ~(1ULL << k);
            mnChgG[k] = publicGrid[i];
            mnHG[publicGrid[i] & 255] |= 1ULL << k;
        }
        if (mnChgS[j] == mnStamp) {
            int k = mnChgK[j];
            mnHG[mnChgG[k] & 255] &= ~(1ULL << k);
            mnChgG[k] = publicGrid[j];
            mnHG[publicGrid[j] & 255] |= 1ULL << k;
        }
        mnNoteAround(a, j);
        mnNoteAround(a, i);
        mnNoteAround(b, i);
        mnNoteAround(b, j);
        for (int k = 0; k < MNPUSH; k++) {
            int p = cand[k];
            if (p < 0 || mnInQ[p] == mnStamp || tail >= QC)
                continue;
            mnInQ[p] = mnStamp;
            mnQ[tail++] = p;
        }
    }
    mnLight = 0;
    {
        const int lim = mnNChg < MNCHL ? mnNChg : MNCHL;
        for (int k = 0; k < lim; k++) {
            mnHO[mnChgO[k] & 255] = 0;
            mnHG[mnChgG[k] & 255] = 0;
        }
    }
    return done;
}
int smNoCredit = 0;
int hugeStk = 0, hugeRun = 0;
#define HVB_MNC 0
#define HVB_CR0 0
#define HVB_CRA 0
#define HVB_MNP 0
#define HVB_MNS 0
// 为当前操作配置交换修复的候选范围、轮数与预算。
void mnRun(int x, int c) {
    if (lgmL && !mdRbOp) {
        bool off_ = LGM_MNOFF > 0 && (LGM_MNOFF == 1 || (LGM_MNOFF == 2) == (lgmAdd != 0));
        if (LGM_MNCS > 0 && ((ll)c << LGM_MNCS) >= N)
            off_ = false;
        if (LGM_MNCX > 0 && ((ll)c << LGM_MNCX) < N)
            off_ = true;
        if (off_)
            return;
    }
    if (EH_MNC > 0) {
        const ll mnc_ = (LGM_MNC > 0 && lgmL)       ? LGM_MNC
                        : (HVB_CR0 > 0 && N > MNHI) ? 0
                        : (HVB_MNC > 0 && N > MNHI) ? HVB_MNC
                        : (SM_MNC > 0 && smT)       ? SM_MNC
                                                    : ((MQ_MNC > 0 && mqT) ? MQ_MNC : EH_MNC),
                 mncap_ = (LGM_MNCAP > 0 && lgmL)     ? LGM_MNCAP
                          : (HVB_CR0 > 0 && N > MNHI) ? multiplyNonnegative(N, HVB_CR0)
                          : (HVB_MNC > 0 && N > MNHI) ? ((ll)HVB_MNC << 2)
                          : (SM_MNCAP > 0 && smT) ? SM_MNCAP
                                                  : ((MQ_MNCAP > 0 && mqT) ? MQ_MNCAP : EH_MNCAP);
        if (!smNoCredit)
            ehMnCredit += mnc_;
        if (ehMnCredit > mncap_)
            ehMnCredit = mncap_;
        mnEvLim = ehMnCredit < MNEV ? ehMnCredit : MNEV;
        if (mnEvLim <= 0)
            return;
    }
    if (MD_RBP < 0 && mdRbOp)
        return;
    if (LGM_RBP < 0 && lgmL && mdRbOp)
        return;
    int h4 = N > MNHN ? MNH4B : MNH4;
    if (MD_RBH > 0 && mdRbOp)
        h4 = MD_RBH;
    if (EH_MNHK > 0) {
        ll hk = divideNonnegative(multiplyNonnegative(N, EH_MNHK),
                                  TS_TAUE > 0 ? ((tsCbar16 >> 2) > 0 ? (tsCbar16 >> 2) : 1)
                                              : ((ll)c << 2));
        if (hk < 1)
            hk = 1;
        if (h4 > hk)
            h4 = (int)hk;
    }
    {
        int hh = rmPick(rmCls, RM_H40, RM_H41, RM_H42, RM_H43);
        if (hh > 0 && !mdRbOp)
            h4 = hh;
    }
    if (MD2S_H4 > 0 && N <= MD2_SN)
        h4 = mdRbOp ? (MD2S_H4R > 0 ? MD2S_H4R : h4) : MD2S_H4;
    if (MD2M_H4 > 0 && N > MD2_SN && !mdRbOp)
        h4 = MD2M_H4;
    if (RM_HK > 0 && !mdRbOp) {
        ll cb = tsCbar16 > 16 ? tsCbar16 : 16;
        ll hk = divideNonnegative(multiplyNonnegative(N, RM_HK), cb);
        if (hk > RM_HMAX)
            hk = RM_HMAX;
        if (hk > h4)
            h4 = (int)hk;
    }
    if (smT) {
        if (SM_H4 > 0 && !mdRbOp)
            h4 = SM_H4;
        if (SM_H4R > 0 && mdRbOp)
            h4 = SM_H4R;
    }
    if (SQ_MHQ > 0 && smT) {
        const int hq = (int)(multiplyNonnegative(operationCount, SQ_MHQ) >> 2) + SQ_MHQB;
        if (h4 > hq)
            h4 = hq;
    }
    if (mqT) {
        if (MQ_H4 > 0 && !mdRbOp)
            h4 = MQ_H4;
        if (MQ_H4R > 0 && mdRbOp)
            h4 = MQ_H4R;
    }
    if (LGM_RBH > 0 && lgmL && mdRbOp)
        h4 = LGM_RBH;
    h4 = sdyH(h4);
    if (HVB_MNH > 0 && N > MNHI)
        h4 = HVB_MNH;
    if (hugeStk && h4 > 4)
        h4 = 4;
    const int h4op_ = h4;
    thrM = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 11,
                             multiplyNonnegative(multiplyNonnegative(11, h4), N - c));
    mnStT[0] = -(thrM << 1);
    mnStT[1] = -thrM;
    mnStT[2] = 0;
    mnStT[3] = thrM;
    mnStT[4] = thrM << 1;
    bool sweep = MNALL == 2 && (operationStamp & (MNAP - 1)) == 0;
    if (RM_VSC > 0)
        sweep = (operationStamp & (MNAP - 1)) == 0 &&
                multiplyNonnegative(tsCbar16 > 16 ? tsCbar16 : 16, RM_VSC) <= ((ll)N << 4);
    rmNox = RM_NOXS > 0 && c <= (N >> RM_NOXS) && typeSize[x] <= (N >> RM_NOXT);
    if (rmPick(rmCls, RM_NOX0, RM_NOX1, RM_NOX2, RM_NOX3) > 0)
        rmNox = 1;
    if (rmPick(rmCls, RM_VSW0, RM_VSW1, RM_VSW2, RM_VSW3) > 0 && (operationStamp & (MNAP - 1)) == 0)
        sweep = true;
    if (LGM_NOX > 0 && lgmL &&
        (LGM_NOX == 1 || ((ll)c << 4) < multiplyNonnegative(typeSize[x], LGM_NOXR)))
        rmNox = 0;
    if (smT) {
        if (SM_NOX == 1)
            rmNox = 1;
        else if (SM_NOX == 2)
            rmNox = 0;
        if (SM_VSW > 0 && (operationStamp & (SM_VSW - 1)) == 0)
            sweep = true;
    }
    int mp = (MD_RBP > 0 && mdRbOp) ? MD_RBP : MNP;
    if (RM_PN > 0 && N > RM_PN)
        mp = mdRbOp ? (RM_MNP << 1) : RM_MNP;
    if (smT) {
        if (SM_MNP > 0 && !mdRbOp)
            mp = SM_MNP;
        if (SM_MNPR > 0 && mdRbOp)
            mp = SM_MNPR;
    }
    if (mqT) {
        if (MQ_MNP > 0 && !mdRbOp)
            mp = MQ_MNP;
        if (MQ_MNPR > 0 && mdRbOp)
            mp = MQ_MNPR;
        if (MQ_MN2P > 0 && smNoCredit)
            mp = MQ_MN2P;
    }
    if (LGM_RBP > 0 && lgmL && mdRbOp)
        mp = LGM_RBP;
    if (HVB_MNP > 0 && N > MNHI)
        mp = HVB_MNP;
    const bool rmKs =
        RM_TK != 16 || MD2_TKL != 16 || MD2_TKS != 16 || MD2_TKH != 16 || MD2_TKX != 16;
    if (rmKs) {
        rmKOn = 1;
        for (int t = 1; t < typeSlotCount; t++) {
            if (typeSize[t] < 2)
                continue;
            int k = RM_TK;
            if (MD2_TKL != 16 || MD2_TKS != 16)
                k = ((ll)typeSize[t] << MD2_TKSH) >= N ? MD2_TKL : MD2_TKS;
            if (MD2_TKH != 16 && hcT[t])
                k = multiplyNonnegative(k, MD2_TKH) >> 4;
            if (MD2_TKX != 16 && t == x)
                k = multiplyNonnegative(k, MD2_TKX) >> 4;
            rmK[t] = k;
            if (k != 16)
                setType(t);
        }
    }
    if (HVB_MNS > 0 && N > MNHI) {
        sqSrcOv = HVB_MNS;
        mnDescent(sweep ? mp + MNPX : mp, x, sweep);
        sqSrcOv = 0;
    } else
        mnDescent(sweep ? mp + MNPX : mp, x, sweep);
    if (rmKs) {
        rmKOn = 0;
        for (int t = 1; t < typeSlotCount; t++)
            if (typeSize[t] >= 2 && rmK[t] != 16) {
                setType(t);
                typePenaltyDirty[t] = 1;
                rmK[t] = 16;
            }
    }
    if (EH_MNC > 0)
        ehMnCredit -= mnEv;
    if (RM_GP > 0 && (operationStamp & (RM_GP - 1)) == 0 && N <= MD2_GPN) {
        thrM = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 11,
                                 multiplyNonnegative(multiplyNonnegative(11, RM_GH), N - c));
        mnStT[0] = -(thrM << 1);
        mnStT[1] = -thrM;
        mnStT[2] = 0;
        mnStT[3] = thrM;
        mnStT[4] = thrM << 1;
        ll ev0 = mnEvLim;
        mnEvLim = RM_GEV;
        rmAll = 1;
        mnDescent(RM_GSW, -1, false);
        rmAll = 0;
        mnEvLim = ev0;
    }
    if (SM_GP > 0 && smT && (operationStamp & (SM_GP - 1)) == 0) {
        const int gh = SM_GH > 0 ? SM_GH : h4op_;
        thrM = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 11,
                                 multiplyNonnegative(multiplyNonnegative(11, gh), N - c));
        mnStT[0] = -(thrM << 1);
        mnStT[1] = -thrM;
        mnStT[2] = 0;
        mnStT[3] = thrM;
        mnStT[4] = thrM << 1;
        ll ev0 = mnEvLim;
        mnEvLim = SM_GEV;
        rmAll = 1;
        mnDescent(SM_GSW, -1, false);
        rmAll = 0;
        mnEvLim = ev0;
    }
}
#define SQ_PREHI 1000
#define SQ_PREA 1
#define SQ_PREP 64
#define SQ_PREV 100000
#define SQ_PRESRC 4096
#define SQ_PRECAP 65536
#define SQ_PRECM 0
ll sqPreCred = 0;
void sqPre(int x, int c) {
    const int v0 = ehV0k;
    if (SQ_PREV0 && v0 != 16) {
        ehV0k = 16;
        setType(0);
        typePenaltyDirty[0] = 1;
    }
    ll ev = SQ_PREV;
    bool run = true;
    if (SQ_PREC > 0) {
        sqPreCred += (SQ_PRECM > 0 && N > 1000) ? SQ_PRECM : SQ_PREC;
        if (sqPreCred > SQ_PRECAP)
            sqPreCred = SQ_PRECAP;
        if (ev > sqPreCred)
            ev = sqPreCred;
        if (ev <= 0)
            run = false;
    }
    if (run) {
        {
            int ph_ = sdyH((SQ_PREH4T > 0 && N <= 100) ? SQ_PREH4T : SQ_PREH4);
            if (hugeStk && ph_ > 4)
                ph_ = 4;
            thrM = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 11,
                                     multiplyNonnegative(multiplyNonnegative(11, ph_), N - c));
        }
        mnStT[0] = -(thrM << 1);
        mnStT[1] = -thrM;
        mnStT[2] = 0;
        mnStT[3] = thrM;
        mnStT[4] = thrM << 1;
        const ll ev0 = mnEvLim;
        mnEvLim = ev;
        rmAll = SQ_PREA;
        sqSrcOv = SQ_PRESRC;
        sqWl = SQ_PREW;
        mnDescent(SQ_PREP, SQ_PREA ? -1 : x, false);
        if (SQ_PREC > 0)
            sqPreCred -= mnEv;
        rmAll = 0;
        sqSrcOv = 0;
        sqWl = 0;
        mnEvLim = ev0;
    }
    if (SQ_PREV0 && v0 != 16) {
        ehV0k = v0;
        setType(0);
        typePenaltyDirty[0] = 1;
    }
}
ll totalLayoutPenalty();
void tinyInit(int restarts) {
    thrM = 0;
    hzWork = 0;
    hzLim = TIW;
    tinyDescent(N << 4);
    ll bestP = totalLayoutPenalty();
    vector<int> bestT(slotType, slotType + N);
    for (int r = 0; r < restarts && bestP > 0 && hzWork < TIW; r++) {
        int kicks = 2 + (int)(hzRand() & 3);
        for (int k = 0; k < kicks; k++) {
            int i = (int)(hzRand() & 16383), j = (int)(hzRand() & 16383);
            while (i >= N)
                i -= N;
            while (j >= N)
                j -= N;
            if (slotType[i] != slotType[j])
                doSwap(i, j);
        }
        tinyDescent(N << 4);
        ll P = totalLayoutPenalty();
        if (P < bestP) {
            bestP = P;
            for (int i = 0; i < N; i++)
                bestT[i] = slotType[i];
        } else {
            for (int i = 0; i < N; i++) {
                if (slotType[i] == bestT[i])
                    continue;
                for (int j = i + 1; j < N; j++)
                    if (slotType[j] == bestT[i] && slotType[j] != bestT[j]) {
                        doSwap(i, j);
                        break;
                    }
            }
        }
    }
}
