// 布局惩罚汇总、重构触发与后续修复。为稳定性引入价格，使用受限搜索改善必要改动后的布局。
// Included in fixed order by solution.cpp.

ll wCredit = 0, wRb = 0, wCap = 0;
ll rbExcess = 0, rbM = 0, accEx = 0, lastEx = 0;
int sinceRb = 0, lastChk = 0;
// 汇总所有类型的当前加权 gap 惩罚，并复用未失效的类型缓存。
ll totalLayoutPenalty() {
    ll P = 0;
    for (int t = 1; t < typeSlotCount; t++) {
        int sc = typeSize[t];
        if (sc < 2 || F[t] == 0)
            continue;
        if (!typePenaltyDirty[t]) {
            P += PtC[t];
            continue;
        }
        int q = qv[t], h = typeHead[t], cur = h;
        int A = 0, Gc = 0;
        for (int k = 0; k < sc; k++) {
            int nx = nextSame[cur];
            int g = nx - cur;
            g += g <= 0 ? N : 0;
            int dg = g - q;
            A += dg < 0 ? -dg : dg;
            Gc += dg > 0;
            cur = nx;
        }
        int nd = sc - (Gc << 1);
        ll sd = multiplyNonnegative(A, sc) +
                (nd >= 0 ? multiplyNonnegative(rv[t], nd) : -multiplyNonnegative(rv[t], -nd));
        ll pt = multiplyNonnegative(sd, F[t]);
        PtC[t] = pt;
        typePenaltyDirty[t] = 0;
        P += pt;
    }
    int sc0 = typeSize[0];
    if (sc0 >= 2 && F[0] != 0) {
        int first = -1, last = -1, q = qv[0];
        int A0 = 0, G0 = 0;
        if (SX_VQ > 0 && q >= 1 && q <= SX_VQ && multiplyNonnegative(q, NW) <= sc0) {
            int nle, e;
            ll sle;
            vacShort(q, nle, sle, first, last, e);
            const int ngt = e - 1 - nle;
            const ll sgt = (ll)(last - first) - sle;
            A0 = (int)((multiplyNonnegative(q, nle) - sle) + (sgt - multiplyNonnegative(q, ngt)));
            G0 = ngt;
        } else
            for (int w = 0; w < NW; w++) {
                ull m = vb[w];
                while (m) {
                    int i = (w << 6) + __builtin_ctzll(m);
                    m &= m - 1;
                    if (last >= 0) {
                        int dg = i - last - q;
                        A0 += dg < 0 ? -dg : dg;
                        G0 += dg > 0;
                    } else
                        first = i;
                    last = i;
                }
            }
        if (first >= 0) {
            int dg = first + N - last - q;
            A0 += dg < 0 ? -dg : dg;
            G0 += dg > 0;
        }
        int nd = sc0 - (G0 << 1);
        ll sd = multiplyNonnegative(A0, sc0) +
                (nd >= 0 ? multiplyNonnegative(rv[0], nd) : -multiplyNonnegative(rv[0], -nd));
        P0c = multiplyNonnegative(sd, F[0]);
        P += P0c;
    } else
        P0c = 0;
    return P;
}
// 计算整数间隔条件下的理论惩罚下界，用于衡量布局仍可改善的空间。
ll minimumPossiblePenalty() {
    ll P = 0;
    for (int t = 0; t < typeSlotCount; t++) {
        int sc = typeSize[t];
        if (sc < 2 || F[t] == 0)
            continue;
        ll r = rv[t];
        P += multiplyNonnegative(multiplyNonnegative(r, sc - r) << 1, F[t]);
    }
    return P;
}
#define RQ_PART 0
#define RQ_VAC 1
#define RQ_KMAX 1000
#define RQ_FULL 1
#define RQ_PIN 0
#define RQ_PK 16
#define RQ_PIN0 0
#define RQ_PK0 16
#define RQ_RANK 0
int rqBestNT[MAXN];
RVEC(int) rqOrd;
ll rqEx[MAXT];
int rqLastK = -1;
// 根据当前惩罚与必要改动规模，选择值得尝试的重构修复。
void rqSelect(ll Pc, int c) {
    const ll priceM = multiplyNonnegative(multiplyNonnegative(N, N) << 9, 7);
    const ll gmul = multiplyNonnegative(multiplyNonnegative(11, pTAUA), N - c);
    ll bestNet = OMNEG;
    int bestM = 0;
    ll bestP = Pc;
    bool have = false;
    int bestK = -2;
    if (RQ_FULL) {
        omPart = false;
        buildOverlapReconstruction();
        bestNet = multiplyNonnegative(Pc - omP > 0 ? Pc - omP : 0, gmul) -
                  (Pc - omP > 0 ? 0 : (ll)1 << 50) - multiplyNonnegative(omM > 0 ? omM : 0, priceM);
        bestM = omM;
        bestP = omP;
        have = true;
        bestK = -1;
        for (int i = 0; i < N; i++)
            rqBestNT[i] = rbNTa[i];
    }
    if (RQ_PIN0) {
        ll lamP = multiplyNonnegative(lamFor(c), RQ_PK0) >> 4;
        ll pOld = 0;
        int nIn = 0, nAll = 0;
        for (int t = 0; t < typeSlotCount; t++) {
            int sc = typeSize[t];
            if (sc <= 0)
                continue;
            nAll++;
            ll po = 0, pm = 0;
            if (sc >= 2 && F[t] != 0) {
                po = t ? PtC[t] : P0c;
                ll r = rv[t];
                pm = multiplyNonnegative(multiplyNonnegative(r, sc - r) << 1, F[t]);
            }
            bool pin = (t != 0 || !RQ_VAC) && po - pm < multiplyNonnegative(lamP, sc);
            omIn[t] = pin ? 0 : 1;
            if (!pin) {
                pOld += po;
                nIn++;
            }
        }
        if (!RQ_FULL && !(nIn > 0 && nIn < nAll)) {
            omPart = false;
            buildOverlapReconstruction();
            bestNet = multiplyNonnegative(Pc - omP > 0 ? Pc - omP : 0, gmul) -
                      multiplyNonnegative(omM > 0 ? omM : 0, priceM);
            bestM = omM;
            bestP = omP;
            have = true;
            bestK = -1;
            for (int i = 0; i < N; i++)
                rqBestNT[i] = rbNTa[i];
        }
        if (nIn > 0 && nIn < nAll) {
            omPart = true;
            buildOverlapReconstruction();
            omPart = false;
            ll Pn = Pc - pOld + omP;
            ll gain = Pc - Pn;
            if (gain > 0 || !have) {
                ll net = multiplyNonnegative(gain > 0 ? gain : 0, gmul) -
                         multiplyNonnegative(omM > 0 ? omM : 0, priceM);
                if (net > bestNet || !have) {
                    bestNet = net;
                    bestM = omM;
                    bestP = Pn;
                    have = true;
                    bestK = 99;
                    for (int i = 0; i < N; i++)
                        rqBestNT[i] = rbNTa[i];
                }
            }
        }
    }
    if (RQ_PIN) {
        ll lamP = multiplyNonnegative(lamFor(c), RQ_PK) >> 4;
        for (int it = 0; it < RQ_PIN; it++) {
            ll pOld = 0;
            int nIn = 0, nAll = 0;
            for (int t = 0; t < typeSlotCount; t++) {
                if (typeSize[t] <= 0)
                    continue;
                nAll++;
                if (it > 0 && !omIn[t])
                    continue;
                ll po = (typeSize[t] >= 2 && F[t] != 0) ? (t ? PtC[t] : P0c) : 0;
                int dm = rqDm[t];
                bool pin = po - rqPn[t] < multiplyNonnegative(lamP, dm > 0 ? dm : 0);
                omIn[t] = pin ? 0 : 1;
                if (!pin) {
                    pOld += po;
                    nIn++;
                }
            }
            if (nIn == 0 || nIn == nAll)
                break;
            omPart = true;
            buildOverlapReconstruction();
            ll Pn = Pc - pOld + omP;
            ll gain = Pc - Pn;
            if (gain <= 0)
                break;
            ll net =
                multiplyNonnegative(gain, gmul) - multiplyNonnegative(omM > 0 ? omM : 0, priceM);
            if (net > bestNet) {
                bestNet = net;
                bestM = omM;
                bestP = Pn;
                have = true;
                bestK = 100 + it;
                for (int i = 0; i < N; i++)
                    rqBestNT[i] = rbNTa[i];
            }
        }
        omPart = false;
    }
    rqOrd.clear();
    for (int t = 0; t < typeSlotCount; t++) {
        int sc = typeSize[t];
        if (sc <= 0)
            continue;
        ll pt = 0, pm = 0;
        if (sc >= 2 && F[t] != 0) {
            pt = t ? PtC[t] : P0c;
            ll r = rv[t];
            pm = multiplyNonnegative(multiplyNonnegative(r, sc - r) << 1, F[t]);
        }
        rqEx[t] = pt - pm;
        if (t == 0 && RQ_VAC)
            continue;
        if (pt - pm <= 0)
            continue;
        rqOrd.push_back(t);
    }
    if (RQ_RANK == 1)
        sort(rqOrd.begin(), rqOrd.end(), [](int a, int b) {
            ll x = divideNonnegative(rqEx[a], typeSize[a]),
               y = divideNonnegative(rqEx[b], typeSize[b]);
            return x > y || (x == y && a < b);
        });
    else
        sort(rqOrd.begin(), rqOrd.end(),
             [](int a, int b) { return rqEx[a] > rqEx[b] || (rqEx[a] == rqEx[b] && a < b); });
    int nk = (int)rqOrd.size();
    for (int t = 0; t < typeSlotCount; t++)
        omIn[t] = 0;
    if (RQ_VAC)
        omIn[0] = 1;
    ll pOld = RQ_VAC ? (typeSize[0] >= 2 && F[0] != 0 ? P0c : 0) : 0;
    int k = 0, nextK = 1;
    while (k < nk && k < RQ_KMAX) {
        int t = rqOrd[k];
        omIn[t] = 1;
        pOld += t ? PtC[t] : P0c;
        k++;
        if (k != nextK && k != nk)
            continue;
        nextK = nextK + (nextK >> 1) + 1;
        if (k >= nk && RQ_FULL && (!RQ_VAC || true)) {
        }
        omPart = true;
        buildOverlapReconstruction();
        ll Pn = Pc - pOld + omP;
        ll gain = Pc - Pn;
        if (gain <= 0)
            continue;
        ll net = multiplyNonnegative(gain, gmul) - multiplyNonnegative(omM > 0 ? omM : 0, priceM);
        if (net > bestNet) {
            bestNet = net;
            bestM = omM;
            bestP = Pn;
            have = true;
            bestK = k;
            for (int i = 0; i < N; i++)
                rqBestNT[i] = rbNTa[i];
        }
    }
    omPart = false;
    rqLastK = bestK;
    if (!have) {
        omM = 0;
        omP = Pc;
        for (int i = 0; i < N; i++)
            rbNTa[i] = slotType[i];
        return;
    }
    for (int i = 0; i < N; i++)
        rbNTa[i] = rqBestNT[i];
    omM = bestM;
    omP = bestP;
}
void om2PartSelect(ll Pc, int c, int tauAE, int mode) {
    int nIn = 0, nAll = 0;
    ll pOld = 0;
    for (int t = 0; t < typeSlotCount; t++) {
        omIn[t] = 0;
        if (typeSize[t] <= 0)
            continue;
        nAll++;
        if ((t == 0 && OM2_PARTV) || (t != 0 && hcT[t])) {
            omIn[t] = 1;
            nIn++;
            if (typeSize[t] >= 2 && F[t] != 0)
                pOld += t ? PtC[t] : P0c;
        }
    }
    if (nIn == 0 || nIn == nAll) {
        omPart = false;
        buildOverlapReconstruction();
        return;
    }
    omPart = true;
    buildOverlapReconstruction();
    omPart = false;
    ll Pn = Pc - pOld + omP;
    int Mn = omM;
    if (mode < 2) {
        omP = Pn;
        return;
    }
    const ll priceM = multiplyNonnegative(multiplyNonnegative(N, N) << 9, 7),
             gmul = multiplyNonnegative(multiplyNonnegative(11, tauAE), N - c);
    ll netA = multiplyNonnegative(Pc - Pn > 0 ? Pc - Pn : 0, gmul) -
              (Pc - Pn > 0 ? 0 : (ll)1 << 50) - multiplyNonnegative(Mn > 0 ? Mn : 0, priceM);
    for (int i = 0; i < N; i++)
        rqBestNT[i] = rbNTa[i];
    buildOverlapReconstruction();
    ll netB = multiplyNonnegative(Pc - omP > 0 ? Pc - omP : 0, gmul) -
              (Pc - omP > 0 ? 0 : (ll)1 << 50) - multiplyNonnegative(omM > 0 ? omM : 0, priceM);
    if (netA > netB) {
        for (int i = 0; i < N; i++)
            rbNTa[i] = rqBestNT[i];
        omP = Pn;
        omM = Mn;
    }
}
void om2BestOf(ll Pc, int c, int tauAE) {
    const ll priceM = multiplyNonnegative(multiplyNonnegative(N, N) << 9, 7),
             gmul = multiplyNonnegative(multiplyNonnegative(11, tauAE), N - c);
    const ll hv0 = omHV;
    const int ks[4] = {16, OM2_TK(OM2_BKA), OM2_TK(OM2_BKB), OM2_TK(OM2_BKC)};
    ll bestNet = 0;
    int have = 0;
    ll bP = 0;
    int bM = 0;
    for (int v = 0; v < 4; v++) {
        if (ks[v] <= 0)
            continue;
        omHV = multiplyNonnegative(hv0, ks[v]) >> 4;
        buildOverlapReconstruction();
        ll net = multiplyNonnegative(Pc - omP > 0 ? Pc - omP : 0, gmul) -
                 (Pc - omP > 0 ? 0 : (ll)1 << 50) - multiplyNonnegative(omM > 0 ? omM : 0, priceM);
        if (!have || net > bestNet) {
            bestNet = net;
            bP = omP;
            bM = omM;
            for (int i = 0; i < N; i++)
                rqBestNT[i] = rbNTa[i];
            have = 1;
        }
    }
    omHV = hv0;
    for (int i = 0; i < N; i++)
        rbNTa[i] = rqBestNT[i];
    omP = bP;
    omM = bM;
}
#define HZ 1
#define HZA 2
#define HZB 2
#define HZLO 1
#define HZR 1
#define HZOM 1
#define HSN 256
#define HSC 8
#define HZP 0
int sdyHcur = 1;
// 估算局部修复使用的有限收益视野，作为搜索启发式而非未来输入知识。
int currentHorizon() {
    if (hugeStk)
        return 1;
    if (HZ) {
        int h = (int)(multiplyNonnegative(operationCount, HZA) >> 2) + HZB;
        if (h < HZLO)
            h = HZLO;
        if (h > HORLS)
            h = HORLS;
        if (N <= HSN && h > HSC)
            h = HSC;
        if (SM_HC > 0 && smT && h > SM_HC)
            h = SM_HC;
        return sdyHcur ? sdyH(h) : sdyR(h);
    }
    int h = operationStamp;
    if (h < HMIN)
        h = HMIN;
    if (h > HORLS)
        h = HORLS;
    return h;
}
#define HC_HVKH 0
#define HC_HVKS 2
#define HC_RVH 20
#define HC_RVHC 1
RVEC(int) hcFQ, hcTq;
RVEC(char) hcFIn;
SP2_I void hcRPush(int i) {
    if (i >= 0 && !hcFIn[i] && changeStamp[i] == operationStamp &&
        publicGrid[i] != originalValue[i] &&
        (HC_RV >= 2 || (omPre[i] >= 0 && omPre[i] != slotType[i]))) {
        hcFIn[i] = 1;
        hcFQ.push_back(i);
    }
}
#define MD2_HCSTR 0
#define MD2_HCLO 1000
vector<int> bg1Qb;
void hcRevertLS(ll budget, ll thr) {
    if ((int)hcFIn.size() != N)
        hcFIn.assign(N, 0);
    hcFQ.clear();
    const bool bg1h = BG1_RVOF == 1 && RB_HCORD == 4 && RB_HCSTR == 2 && OM2_RVO_B == 2 && N > NM;
    size_t bg1A = (size_t)-1;
    if (BF_RVX && HC_RV >= 2 && N > NM) {
        hcFQ.resize(N);
        int n = 0;
        const int op = operationStamp;
        for (int i = 0; i < N; i++) {
            int f = (changeStamp[i] == op) & (publicGrid[i] != originalValue[i]);
            hcFQ[n] = i;
            hcFIn[i] = (char)f;
            n += f;
        }
        hcFQ.resize(n);
        if (RB_HCORD == 1)
            std::reverse(hcFQ.begin(), hcFQ.end());
        else if (RB_HCORD == 2) {
            vector<int> tq;
            tq.reserve(n);
            for (int k = 0; k < n; k += 2)
                tq.push_back(hcFQ[k]);
            for (int k = 1; k < n; k += 2)
                tq.push_back(hcFQ[k]);
            hcFQ.swap(tq);
        } else if (RB_HCORD == 4) {
            hcTq.resize(n);
            int m = 0;
            if (bg1h) {
                bg1Qb.resize((size_t)n + 2);
                auto FQ = hcFQ.data();
                auto PR = omPre.data();
                auto TQ = hcTq.data();
                auto C1 = bg1Qb.data();
                int m1 = 0;
                for (int g = 0; g < 2; g++)
                    for (int k = g; k < n; k += 2) {
                        const int i = FQ[k], y = PR[i];
                        const int yy = y & ~(y >> 31);
                        const int c0 = (y > 0) & (hcT[yy] == 0), c1 = (y != 0) & (c0 ^ 1);
                        TQ[m] = i;
                        m += c0;
                        C1[m1] = i;
                        m1 += c1;
                    }
                for (int k = 0; k < m1; k++)
                    TQ[m + k] = C1[k];
                m += m1;
                hcTq.resize(m);
                bg1A = (size_t)m;
            } else
                for (int r = 0; r < RB_HCSTR; r++)
                    for (int k = r; k < n; k += RB_HCSTR)
                        hcTq[m++] = hcFQ[k];
            hcFQ.swap(hcTq);
        } else if (RB_HCORD == 3) {
            int WW = RB_HCRW;
            if (WW > (N >> 1) - 1)
                WW = (N >> 1) - 1;
            vector<int> qa, qb;
            qa.reserve(n);
            qb.reserve(n);
            for (int k = 0; k < n; k++) {
                int i = hcFQ[k], a0 = omPre[i], gi = publicGrid[i];
                bool pr = false;
                if (a0 >= 0 && a0 != slotType[i])
                    for (int d = -WW; d <= WW && !pr; d++) {
                        int j = i + d;
                        if (j >= N)
                            j -= N;
                        else if (j < 0)
                            j += N;
                        pr = j != i && slotType[j] == a0 && changeStamp[j] == op &&
                             originalValue[j] == gi;
                    }
                if (pr)
                    qa.push_back(i);
                else
                    qb.push_back(i);
            }
            for (int x : qb)
                qa.push_back(x);
            hcFQ.swap(qa);
        }
    } else {
        for (int i = 0; i < N; i++)
            hcRPush(i);
        if (MD2_HCSTR > 1 && N <= NM && N > MD2_HCLO) {
            const int n = (int)hcFQ.size();
            hcTq.resize(n);
            int m = 0;
            for (int r = 0; r < MD2_HCSTR; r++)
                for (int k = r; k < n; k += MD2_HCSTR)
                    hcTq[m++] = hcFQ[k];
            hcFQ.swap(hcTq);
        }
    }
    if ((OM2_RVO_S || OM2_RVO_M || OM2_RVO_B) && OM2_TK(OM2_RVO) &&
        !(bg1h && BF_RVX && HC_RV >= 2)) {
        const int md = OM2_TK(OM2_RVO);
        const int n0 = (int)hcFQ.size();
        hcTq.resize(n0);
        int m = 0;
        auto FQ = hcFQ.data();
        auto TQ = hcTq.data();
        auto PR = omPre.data();
        auto FI = hcFIn.data();
        if (md == 1) {
            for (int k = 0; k < n0; k++) {
                int i = FQ[k];
                if (PR[i] != 0)
                    TQ[m++] = i;
                else
                    FI[i] = 0;
            }
        } else {
            for (int pass = 0; pass < 2; pass++)
                for (int k = 0; k < n0; k++) {
                    int i = FQ[k], y = PR[i];
                    int cl = (y > 0 && !hcT[y]) ? 0 : 1;
                    if (y != 0 && cl == pass)
                        TQ[m++] = i;
                }
            for (int k = 0; k < n0; k++) {
                int i = FQ[k];
                if (PR[i] == 0) {
                    if (md == 3)
                        FI[i] = 0;
                    else
                        TQ[m++] = i;
                }
            }
        }
        hcTq.resize(m);
        hcFQ.swap(hcTq);
    }
    size_t h = 0;
    int W = N > NM ? RB_HCRW : ((SM_HCRW > 0 && smT) ? SM_HCRW : HC_RW);
    if (W > (N >> 1) - 1)
        W = (N >> 1) - 1;
    const int fm_ = N > NM ? RB_HCFM : ((SM_HCFM >= 0 && smT) ? SM_HCFM : HC_FM);
    while (budget > 0) {
        if (BG1_RVOF == 1 && h == bg1A) {
            bg1A = (size_t)-1;
            const int n0 = (int)hcTq.size();
            bg1Qb.resize((size_t)n0 + 2);
            auto IL = hcTq.data();
            auto C2 = bg1Qb.data();
            auto PR = omPre.data();
            int m2 = 0;
            for (int g = 0; g < 2; g++)
                for (int k = g; k < n0; k += 2) {
                    const int i = IL[k];
                    C2[m2] = i;
                    m2 += PR[i] == 0;
                }
            if (m2 > 0) {
                const size_t old = hcFQ.size();
                hcFQ.resize(old + (size_t)m2);
                auto Q = hcFQ.data();
                for (size_t k = old; k > h; k--)
                    Q[k - 1 + (size_t)m2] = Q[k - 1];
                for (int k = 0; k < m2; k++)
                    Q[h + (size_t)k] = C2[k];
            }
        }
        if (h >= hcFQ.size())
            break;
        int i = hcFQ[h++];
        hcFIn[i] = 0;
        int a = slotType[i], a0 = omPre[i];
        const int gi = publicGrid[i], oi = originalValue[i];
        ll best = 0;
        int bj = -1;
        if (HC_RV >= 2) {
            int sa = typeSize[a];
            if (sa >= 3 && F[a] != 0) {
                int L = prvT(i, a), R = nxtT(i, a);
                int g1 = dist(L, i), g2 = dist(i, R), gl = g1 + g2;
                int q = qv[a], lo = g1 < g2 ? g1 : g2, hi = gl - lo;
                if (gl >= 4 && hi - lo >= 2 && lo <= q && hi > q) {
                    int h1 = gl >> 1;
                    int m = L + h1;
                    if (m >= N)
                        m -= N;
                    for (int d = -fm_; d <= fm_; d++) {
                        int j = m + d;
                        if (j >= N)
                            j -= N;
                        else if (j < 0)
                            j += N;
                        if (j == i || j == L || j == R || slotType[j] == a)
                            continue;
                        int gj0 = h1 + d;
                        if (gj0 <= 0 || gj0 >= gl)
                            continue;
                        const int gj = publicGrid[j],
                                  oj = changeStamp[j] == operationStamp ? originalValue[j] : gj;
                        if (oj == gj)
                            continue;
                        int dm = (gj != oi) - 1 + (gi != oj) - (gj != oj);
                        ll v0 = dm > 0 ? multiplyNonnegative(thr, dm)
                                       : (dm < 0 ? -multiplyNonnegative(thr, -dm) : 0);
                        budget--;
                        ll da = SP3_W4(a, gj0, gl - gj0, g1, g2);
                        if (da + v0 >= best + (thr << 2))
                            continue;
                        ll db = dMoveWI(slotType[j], j, i);
                        if (db == INVALID)
                            continue;
                        ll v = da + db + v0;
                        if (v < best) {
                            best = v;
                            bj = j;
                        }
                    }
                }
            }
        }
        int hsA = 0, hLu = 0, hRu = 0, hg1 = 0, hg2 = 0;
        if (a0 >= 0 && a0 != a && typeSize[a0] > 0) {
            hsA = (F[a] == 0 || typeSize[a] <= 1) ? 0 : typeSize[a];
            if (hsA >= 3) {
                hLu = prvT(i, a);
                hRu = nxtT(i, a);
                hg1 = dist(hLu, i);
                hg2 = dist(i, hRu);
            }
        }
        if (a0 >= 0 && a0 != a && typeSize[a0] > 0)
            for (int d = -W; d <= W; d++) {
                int j = i + d;
                if (j >= N)
                    j -= N;
                else if (j < 0)
                    j += N;
                if (slotType[j] != a0 || j == i)
                    continue;
                const int gj = publicGrid[j],
                          oj = changeStamp[j] == operationStamp ? originalValue[j] : gj;
                int dm = (gj != oi) - 1 + (gi != oj) - (gj != oj);
                ll v0 = dm > 0 ? multiplyNonnegative(thr, dm)
                               : (dm < 0 ? -multiplyNonnegative(thr, -dm) : 0);
                budget--;
                ll da;
                if (hsA >= 3 && SP_DMI) {
                    const int gw = dist(hLu, j);
                    if (gw < hg1 + hg2)
                        da = SP3_W4(a, gw, hg1 + hg2 - gw, hg1, hg2);
                    else if (TBITS) {
                        int L, R;
                        if (!findNbFar(a, i, j, hLu, hRu, L, R))
                            da = INVALID;
                        else
                            da = (wcst(a, hg1 + hg2) - wcst(a, hg1) - wcst(a, hg2)) +
                                 (wcst(a, dist(L, j)) + wcst(a, dist(j, R)) - wcst(a, dist(L, R)));
                    } else
                        da = dMoveW(a, i, j);
                } else
                    da = hsA == 0 ? 0 : dMoveWI(a, i, j);
                if (da == INVALID)
                    continue;
                ll db = dMoveWI(a0, j, i);
                if (db == INVALID)
                    continue;
                ll v = da + db + v0;
                if (v < best) {
                    best = v;
                    bj = j;
                }
            }
        if (bj >= 0) {
            int b = slotType[bj];
            int La = prvT(i, a), Ra = nxtT(i, a), Lb = prvT(bj, b), Rb = nxtT(bj, b);
            doSwap(i, bj);
            hcRPush(La);
            hcRPush(Ra);
            hcRPush(Lb);
            hcRPush(Rb);
            hcRPush(prvT(i, b));
            hcRPush(nxtT(i, b));
            hcRPush(prvT(bj, a));
            hcRPush(nxtT(bj, a));
            hcRPush(i);
            hcRPush(bj);
        }
    }
    for (size_t k = h; k < hcFQ.size(); k++)
        hcFIn[hcFQ[k]] = 0;
    if (BG1_RVOF == 1 && bg1A != (size_t)-1)
        for (size_t k = 0; k < hcTq.size(); k++)
            hcFIn[hcTq[k]] = 0;
    hcFQ.clear();
}
#define HC_V0 0
#define HC_V0W 4
#define HC_V0H 4
#define HC_V0R 1
#define HC_VSH 2
#define HC_VACTM 1
#define SH_BOP 3
#define SH_VRL 0
#define SH_VRW 8
#define SH_VRA 0
#define SH_VRAR 0
#define SH_VRWB 0
#define HVB_VRH 0
#define HVB_VCH 0
#define HVB_RXR 0
#define SH_VRG 0
#define EH_RBDN 0
#define EH_V0S 1
#define EH_V0R 20
#define EH_V0E 2
#define EH_V0MIN 1
ll ehCbar16 = 0;
ll shCbar16 = 0;
#define BF_RVH -1
#define BF_V0R 0
#define BF_V0S -1
int smBestNT[MAXN];
ull smRng = 0x2545F4914F6CDD1DULL;
inline ull smRand() {
    smRng ^= smRng << 13;
    smRng ^= smRng >> 7;
    smRng ^= smRng << 17;
    return smRng;
}
const int SMLOG = SM_SA > 0 ? (1 << 18) : 2;
int smLogI[SMLOG], smLogJ[SMLOG];
int smCand[MAXN];
void smAnneal(int c) {
    const ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 11,
                                     multiplyNonnegative(multiplyNonnegative(11, SM_SAH), N - c));
    ll iters = multiplyNonnegative(N, SM_SA) >> 4;
    if (iters > SMLOG - 1)
        iters = SMLOG - 1;
    if (iters < 1)
        return;
    int nc = 0;
    if (SM_SAL > 0) {
        for (int i = 0; i < N; i++)
            smCand[i] = 0;
        const int op = operationStamp;
        for (int i = 0; i < N; i++)
            if (changeStamp[i] == op) {
                for (int d = -SM_SAL; d <= SM_SAL; d++) {
                    int j = i + d;
                    if (j < 0)
                        j += N;
                    else if (j >= N)
                        j -= N;
                    smCand[j] = 1;
                }
            }
        for (int i = 0; i < N; i++)
            if (smCand[i])
                smCand[nc++] = i;
        if (nc == 0)
            return;
    } else
        nc = N;
    int msk = 1;
    while (msk < nc)
        msk = (msk << 1) | 1;
    const ll T0 = multiplyNonnegative(thr, SM_SAT) >> 4;
    const ll tstep = divideNonnegative(T0, iters) + 1;
    ll Tc = T0;
    ll cum = 0, best = 0;
    int bestK = 0, nlog = 0;
    const int W = SM_SAW < (N >> 1) - 1 ? SM_SAW : (N >> 1) - 1;
    int wm = 1;
    while (wm < (W << 1) + 1)
        wm = (wm << 1) | 1;
    for (ll it = 0; it < iters; it++) {
        Tc -= tstep;
        if (Tc < 0)
            Tc = 0;
        ull r = smRand();
        int k = (int)(r & (ull)msk);
        if (k >= nc)
            continue;
        int dd = (int)((r >> 32) & (ull)wm);
        if (dd > (W << 1))
            continue;
        int d = dd - W;
        if (d == 0)
            continue;
        int i = SM_SAL > 0 ? smCand[k] : k;
        int j = i + d;
        if (j < 0)
            j += N;
        else if (j >= N)
            j -= N;
        const int a = slotType[i], b = slotType[j];
        if (a == b)
            continue;
        ll da = dMoveWI(a, i, j);
        if (da == INVALID)
            continue;
        ll db = dMoveWI(b, j, i);
        if (db == INVALID)
            continue;
        int dm = changedIf(i, publicGrid[j]) - changedNow(i) + changedIf(j, publicGrid[i]) -
                 changedNow(j);
        ll v =
            da + db +
            (dm > 0 ? multiplyNonnegative(thr, dm) : (dm < 0 ? -multiplyNonnegative(thr, -dm) : 0));
        if (v <= Tc && (v < 0 || Tc > 0)) {
            doSwap(i, j);
            smLogI[nlog] = i;
            smLogJ[nlog] = j;
            nlog++;
            cum += v;
            if (cum < best) {
                best = cum;
                bestK = nlog;
            }
        }
    }
    for (int q = nlog - 1; q >= bestK; q--)
        doSwap(smLogI[q], smLogJ[q]);
}
#define SDY_RSA 0
#define SDY_RSW 16
#define SDY_RST 16
#define SDY_RSH 0
const int SDYLOG = SDY_RSA > 0 ? (1 << 20) : 2;
int sdyLogI[SDYLOG], sdyLogJ[SDYLOG];
ull sdyRng = 0x9E3779B97F4A7C15ULL;
void sdyAnneal(ll iters, ll thr, int Wq, int Tk) {
    if (iters > SDYLOG - 1)
        iters = SDYLOG - 1;
    if (iters < 1)
        return;
    int msk = 1;
    while (msk < N)
        msk = (msk << 1) | 1;
    const ll T0 = multiplyNonnegative(thr, Tk) >> 4;
    const ll tstep = divideNonnegative(T0, iters) + 1;
    ll Tc = T0, cum = 0, best = 0;
    int bestK = 0, nlog = 0;
    const int W = Wq < (N >> 1) - 1 ? Wq : (N >> 1) - 1;
    if (W < 1)
        return;
    int wm = 1;
    while (wm < (W << 1) + 1)
        wm = (wm << 1) | 1;
    for (ll it = 0; it < iters; it++) {
        Tc -= tstep;
        if (Tc < 0)
            Tc = 0;
        sdyRng ^= sdyRng << 13;
        sdyRng ^= sdyRng >> 7;
        sdyRng ^= sdyRng << 17;
        ull r = sdyRng;
        int i = (int)(r & (ull)msk);
        if (i >= N)
            continue;
        int dd = (int)((r >> 32) & (ull)wm);
        if (dd > (W << 1))
            continue;
        int d = dd - W;
        if (d == 0)
            continue;
        int j = i + d;
        if (j < 0)
            j += N;
        else if (j >= N)
            j -= N;
        const int a = slotType[i], b = slotType[j];
        if (a == b)
            continue;
        ll da = dMoveWI(a, i, j);
        if (da == INVALID)
            continue;
        ll db = dMoveWI(b, j, i);
        if (db == INVALID)
            continue;
        int dm = changedIf(i, publicGrid[j]) - changedNow(i) + changedIf(j, publicGrid[i]) -
                 changedNow(j);
        ll v =
            da + db +
            (dm > 0 ? multiplyNonnegative(thr, dm) : (dm < 0 ? -multiplyNonnegative(thr, -dm) : 0));
        if (v <= Tc && (v < 0 || Tc > 0)) {
            doSwap(i, j);
            sdyLogI[nlog] = i;
            sdyLogJ[nlog] = j;
            nlog++;
            cum += v;
            if (cum < best) {
                best = cum;
                bestK = nlog;
            }
            if (nlog >= SDYLOG - 1)
                break;
        }
    }
    for (int q = nlog - 1; q >= bestK; q--)
        doSwap(sdyLogI[q], sdyLogJ[q]);
}
const int SMRCM[8] = {4, 6, 12, 16, 24, 32, 2, 48};
void smRepairCands(ll Pc, int c, int tauAE) {
    const ll hv0 = omHV;
    const ll pr = multiplyNonnegative(multiplyNonnegative(N, N) << 9, 7);
    const ll gk = multiplyNonnegative(11, multiplyNonnegative(tauAE, N - c));
    ll bestV = 0, bP = 0;
    int bM = 0;
    auto val = [&]() {
        ll g = Pc - omP;
        return (g > 0 ? multiplyNonnegative(g, gk) : -1) - multiplyNonnegative(omM, pr);
    };
    buildOverlapReconstruction();
    bestV = val();
    bP = omP;
    bM = omM;
    for (int i = 0; i < N; i++)
        smBestNT[i] = rbNTa[i];
    auto tryOne = [&]() {
        buildOverlapReconstruction();
        ll v = val();
        if (v > bestV) {
            bestV = v;
            bP = omP;
            bM = omM;
            for (int i = 0; i < N; i++)
                smBestNT[i] = rbNTa[i];
        }
    };
    for (int k = 0; k < 8; k++)
        if ((SM_RCH >> k) & 1) {
            omHV = multiplyNonnegative(hv0, SMRCM[k]) >> 3;
            tryOne();
        }
    omHV = hv0;
    if (SM_RCT > 1) {
        for (int a = 0; a < SM_RCT; a++)
            for (int b = a + 1; b < SM_RCT; b++) {
                iqSA = a;
                iqSB = b;
                tryOne();
            }
        iqSA = -1;
        iqSB = -1;
    }
    for (int i = 0; i < N; i++)
        rbNTa[i] = smBestNT[i];
    omP = bP;
    omM = bM;
}
#define BG2_PH 0
#define BG2_PULLO 0
unsigned char bgOk[MAXT];
SP2_I ll bgSl(int u, int q, ll fs, ll w2) {
    return u > q ? fs : (u < q ? -fs : fs - w2);
}
__attribute__((noinline)) void bg2Pull(ll thr) {
    const int D = BG2_PULL >= 2 ? 2 : 1;
    if (BG2_PULLF) {
        const ll fs0 = multiplyNonnegative(typeSize[0], F[0]);
        for (int y = 1; y < typeSlotCount; y++) {
            int sy = typeSize[y];
            bgOk[y] =
                (unsigned char)(sy >= 2 && F[y] > 0 &&
                                ((multiplyNonnegative(sy, F[y]) + fs0) << (D == 1 ? 1 : 2)) > thr);
        }
        bgOk[0] = 0;
    }
    for (int w = 0; w < NW; w++) {
        ull m = vb[w] & ~vcVb0[w];
        while (m) {
            const int p = (w << 6) + __builtin_ctzll(m);
            m &= m - 1;
            if (slotType[p] != 0)
                continue;
            if (BG2_PULLF) {
                const int o = changeStamp[p] == operationStamp ? originalValue[p] : publicGrid[p];
                int j1 = p - 1;
                if (j1 < 0)
                    j1 += N;
                int j2 = p + 1;
                if (j2 >= N)
                    j2 -= N;
                bool any = (slotType[j1] != 0 && (bgOk[slotType[j1]] || publicGrid[j1] == o)) ||
                           (slotType[j2] != 0 && (bgOk[slotType[j2]] || publicGrid[j2] == o));
                if (D == 2 && !any) {
                    int j3 = j1 - 1;
                    if (j3 < 0)
                        j3 += N;
                    int j4 = j2 + 1;
                    if (j4 >= N)
                        j4 -= N;
                    any = (slotType[j1] != 0 && slotType[j3] != 0 &&
                           (bgOk[slotType[j3]] || publicGrid[j3] == o)) ||
                          (slotType[j2] != 0 && slotType[j4] != 0 &&
                           (bgOk[slotType[j4]] || publicGrid[j4] == o));
                }
                if (!any)
                    continue;
            }
            const int L = prevVac(p), R = nextVac(p);
            const int g1 = dist(L, p), g2 = dist(p, R);
            const int gp = publicGrid[p],
                      op = changeStamp[p] == operationStamp ? originalValue[p] : gp, cp = op != gp;
            ll bv = 0;
            int bj = -1;
            if (BG2_PULLO >= 2) {
                const ll fs0 = wdt[31] - wdt[32], w20 = wrv[0] << 1;
                const int q0 = qv[0];
                for (int d = -D; d <= D; d++) {
                    if (d == 0 || d <= -g1 || d >= g2)
                        continue;
                    int j = p + d;
                    if (j >= N)
                        j -= N;
                    else if (j < 0)
                        j += N;
                    const int y = slotType[j];
                    if (y == 0)
                        continue;
                    const int ad = d > 0 ? d : -d;
                    ll v = 0;
                    {
                        const int vg = d > 0 ? g1 : g2, vs = d > 0 ? g2 : g1;
                        v += bgSl(vg, q0, fs0, w20) - bgSl(vs - 1, q0, fs0, w20);
                        if (ad == 2)
                            v += bgSl(vg + 1, q0, fs0, w20) - bgSl(vs - 2, q0, fs0, w20);
                    }
                    if (typeSize[y] >= 3 && F[y] != 0 &&
                        (ad == 1 || slotType[d > 0 ? (p + 1 >= N ? p + 1 - N : p + 1)
                                                   : (p - 1 < 0 ? p - 1 + N : p - 1)] != y)) {
                        const int yb = y << 6;
                        const ll fs = wdt[yb + 31] - wdt[yb + 32], w2 = wrv[y] << 1;
                        const int qy = qv[y];
                        const int a = dist(prevSame[j], j), b = dist(j, nextSame[j]);
                        const int sh = d > 0 ? a : b, gr = d > 0 ? b : a;
                        v += bgSl(gr, qy, fs, w2) - bgSl(sh - 1, qy, fs, w2);
                        if (ad == 2)
                            v += bgSl(gr + 1, qy, fs, w2) - bgSl(sh - 2, qy, fs, w2);
                    } else {
                        ll db = dMoveW(y, j, p);
                        if (db == INVALID)
                            continue;
                        v += db;
                    }
                    const int gj = publicGrid[j],
                              oj = changeStamp[j] == operationStamp ? originalValue[j] : gj;
                    const int dm = (gj != op) - cp + (0 != oj) - (gj != oj);
                    v += dm == 1    ? thr
                         : dm == 0  ? 0
                         : dm == 2  ? (thr << 1)
                         : dm == -1 ? -thr
                                    : -(thr << 1);
                    if (v < bv) {
                        bv = v;
                        bj = j;
                    }
                }
                if (bj >= 0)
                    doSwap(p, bj);
                continue;
            }
            const ll base = wcst(0, g1) + wcst(0, g2);
            for (int d = -D; d <= D; d++) {
                if (d == 0 || d <= -g1 || d >= g2)
                    continue;
                int j = p + d;
                if (j >= N)
                    j -= N;
                else if (j < 0)
                    j += N;
                const int y = slotType[j];
                if (y == 0)
                    continue;
                if (BG2_PULLF && !bgOk[y] && publicGrid[j] != op)
                    continue;
                ll db;
                if (BG2_PULLO && typeSize[y] >= 3 && F[y] != 0 &&
                    (d == 1 || d == -1 ||
                     slotType[d > 0 ? (p + 1 >= N ? p + 1 - N : p + 1)
                                    : (p - 1 < 0 ? p - 1 + N : p - 1)] != y)) {
                    const int yb = y << 6;
                    const ll fs = wdt[yb + 31] - wdt[yb + 32], wr = wrv[y];
                    const int qy = qv[y];
                    const int a = dist(prevSame[j], j), b = dist(j, nextSame[j]);
                    int sh = d > 0 ? a : b, gr = d > 0 ? b : a;
                    const int ad = d > 0 ? d : -d;
                    db = 0;
                    for (int t2 = 0; t2 < ad; t2++) {
                        int u1 = sh - 1 - t2;
                        db -= u1 >= qy + 1 ? fs : (u1 <= qy - 1 ? -fs : fs - (wr << 1));
                        int u2 = gr + t2;
                        db += u2 >= qy + 1 ? fs : (u2 <= qy - 1 ? -fs : fs - (wr << 1));
                    }
                } else
                    db = dMoveW(y, j, p);
                if (db == INVALID)
                    continue;
                const int gj = publicGrid[j],
                          oj = changeStamp[j] == operationStamp ? originalValue[j] : gj;
                const int dm = (gj != op) - cp + (0 != oj) - (gj != oj);
                ll v = db + wcst(0, g1 + d) + wcst(0, g2 - d) - base +
                       (dm > 0 ? multiplyNonnegative(thr, dm) : -multiplyNonnegative(thr, -dm));
                if (v < bv) {
                    bv = v;
                    bj = j;
                }
            }
            if (bj >= 0)
                doSwap(p, bj);
        }
    }
}
#define VPM_MW 1
void vpmLmp(int c) {
    int hh = VPM_PH;
    {
        const int hc = currentHorizon();
        if (hh > hc)
            hh = hc;
    }
    if (hh < 1 || typeSize[0] < 3 || F[0] == 0)
        return;
    const ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                     multiplyNonnegative(multiplyNonnegative(11, hh), N - c));
    ll tv[5];
    tv[0] = -(thr << 1);
    tv[1] = -thr;
    tv[2] = 0;
    tv[3] = thr;
    tv[4] = thr << 1;
    const int op_ = operationStamp;
    for (int k = 0; k < vpmMvN; k++) {
        const int p = vpmMv[k];
        const int tp = slotType[p];
        const int gp = publicGrid[p], op0 = changeStamp[p] == op_ ? originalValue[p] : gp;
        ll best = 0;
        int bq = -1;
        for (int d = -VPM_MW; d <= VPM_MW; d++) {
            if (d == 0)
                continue;
            int q = p + d;
            if (q >= N)
                q -= N;
            else if (q < 0)
                q += N;
            const int tq = slotType[q];
            if ((tp == 0) == (tq == 0))
                continue;
            const int gq = publicGrid[q], oq = changeStamp[q] == op_ ? originalValue[q] : gq;
            const int dm = (gq != op0) - (gp != op0) + (gp != oq) - (gq != oq);
            if (dm >= 0)
                continue;
            ll dv, dy;
            if (tp == 0) {
                dv = dMoveW(0, p, q);
                if (dv == INVALID)
                    continue;
                dy = dMoveWI(tq, q, p);
            } else {
                dv = dMoveW(0, q, p);
                if (dv == INVALID)
                    continue;
                dy = dMoveWI(tp, p, q);
            }
            if (dy == INVALID)
                continue;
            const ll v = tv[dm + 2] + dv + dy;
            if (v < best) {
                best = v;
                bq = q;
            }
        }
        if (bq >= 0)
            doSwap(p, bq);
    }
}
#define RBX_FHV 1
#define RBX_FA 0
#define RBX_FAH 0
#define HVB_NW 0
#define HVB_NH 5
int rbxSrc[MAXN + 8], rbxNS = 0;
void rbxFar(int add) {
    const int W = RBX_FW, span = (W << 1) + 1;
    const ll thr = thrM;
    if (typeSize[0] < 3 || F[0] == 0)
        return;
    for (int k = 0; k < rbxNS; k++) {
        const int i = rbxSrc[k];
        if (slotType[i] != 0 || (!add && !changedNow(i)))
            continue;
        const int L = prvT(i, 0), R = nxtT(i, 0);
        if (L < 0 || L == i || R == L)
            continue;
        const int gL = dist(L, i), gR = dist(i, R);
        const ll rem0 = wcst(0, gL + gR) - wcst(0, gL) - wcst(0, gR);
        if (RBX_FR >= 0 && rem0 + (thr << RBX_FR) > 0)
            continue;
        int ws = i - W;
        if (ws < 0)
            ws += N;
        const ull m = bitsAt(ws) & lowMask(span) & ~(1ULL << W);
        int offs[72];
        int no = 0;
        {
            int pv = prevVac(ws);
            if (pv == i)
                pv = prevVac(pv);
            offs[no++] = pv < 0 ? -100000 : -dist(pv, ws);
            ull mm = m;
            while (mm) {
                offs[no++] = __builtin_ctzll(mm);
                mm &= mm - 1;
            }
            int we = ws + span - 1;
            if (we >= N)
                we -= N;
            int nv = nextVac(we);
            if (nv == i)
                nv = nextVac(nv);
            offs[no++] = nv < 0 ? 100000 : (span - 1) + dist(we, nv);
        }
        const int oL = W - gL, oR = W + gR;
        int bestG[4], bestO[4];
        int nb = 0;
        for (int e = 0; e + 1 < no; e++) {
            const int a0 = offs[e], a1 = offs[e + 1];
            if (a0 < -W || a1 > span - 1 + W)
                continue;
            const int g = a1 - a0;
            if (g < 2)
                continue;
            int kk = nb < RBX_FK ? nb++ : RBX_FK;
            if (kk == RBX_FK) {
                if (g <= bestG[RBX_FK - 1])
                    continue;
                kk = RBX_FK - 1;
            }
            while (kk > 0 && bestG[kk - 1] < g) {
                bestG[kk] = bestG[kk - 1];
                bestO[kk] = bestO[kk - 1];
                kk--;
            }
            bestG[kk] = g;
            bestO[kk] = a0;
        }
        if (nb == 0)
            continue;
        {
            const int g = bestG[0], h = g >> 1;
            if (rem0 + wcst(0, h) + wcst(0, g - h) - wcst(0, g) >= 0)
                continue;
        }
        const int gi = publicGrid[i], oI = originalValue[i];
        ll bv = 0;
        int bj = -1;
        for (int u = 0; u < nb; u++) {
            const int g = bestG[u], mid = bestO[u] + (g >> 1);
            const bool own = bestO[u] == oL && g == oR - oL;
            const ll wg = wcst(0, g);
            for (int d = -(RBX_FD - 1); d <= RBX_FD - 1; d++) {
                const int off = mid + d;
                if (off <= bestO[u] || off >= bestO[u] + g)
                    continue;
                int j = ws + off;
                while (j >= N)
                    j -= N;
                while (j < 0)
                    j += N;
                const int b = slotType[j];
                if (b == 0)
                    continue;
                const int da = off - bestO[u];
                const ll d0 = own ? wcst(0, da) + wcst(0, g - da) - wcst(0, gL) - wcst(0, gR)
                                  : rem0 + wcst(0, da) + wcst(0, g - da) - wg;
                const int gj = publicGrid[j],
                          oj = changeStamp[j] == operationStamp ? originalValue[j] : gj;
                const int dm = (gj != oI) - (gi != oI) + (gi != oj) - (gj != oj);
                const ll stv =
                    dm == 0 ? 0
                            : (dm == 1 ? thr
                                       : (dm == 2 ? (thr << 1) : (dm == -1 ? -thr : -(thr << 1))));
                const ll db = dMoveW(b, j, i);
                if (db == INVALID)
                    continue;
                const ll v = d0 + db + stv;
                if (v < bv) {
                    bv = v;
                    bj = j;
                }
            }
        }
        if (bj >= 0) {
            const int b = slotType[bj];
            doSwap(i, bj);
            pushSeed(i);
            pushSeed(bj);
            if (typeSize[b] >= 2) {
                pushSeed(prvT(i, b));
                pushSeed(nxtT(i, b));
            }
            pushSeed(prvT(bj, 0));
            pushSeed(nxtT(bj, 0));
        }
    }
}
#define HVB_MNV0 1
#define HVB_MNCR 5
#define HVB_LSK 0
#define HVB_LSH 0
#define ZCH_H 4
#define ZCH_M 3
#define ZCH_F 0
#define ZCH_SEED 1
#define ZCH_IT 1
ll zchSl[MAXT];
int zchMoves = 0;
__attribute__((noinline)) void zchPass(int x, ll thr, int w) {
    const int nn = zchNN;
    if (nn == 0 || typeSize[x] < 3 || F[x] == 0)
        return;
    for (int t = 0; t < typeSlotCount; t++)
        zchSl[t] = (typeSize[t] >= 2 && F[t] != 0) ? (wmt[(t << 6) + 1] << 1) : 0;
    const int op_ = operationStamp;
    const int xid = serviceId[x];
    for (int it = 0; it < ZCH_IT; it++)
        for (int k = 0; k < nn; k++) {
            const int a = zchNL[k];
            if (slotType[a] != x)
                continue;
            const int L = prevSame[a], R = nextSame[a];
            const int g1 = dist(L, a), g2 = dist(a, R);
            if (ZCH_F == 1) {
                const int df = g1 - g2;
                if (df < 2 && df > -2)
                    continue;
            }
            int lo = 1 - g1, hi = g2 - 1;
            if (lo < -w)
                lo = -w;
            if (hi > w)
                hi = w;
            const ll base = wcst2(x, g1, g2);
            const int oa = changeStamp[a] == op_ ? originalValue[a] : xid, cna = xid != oa;
            ll best = 0;
            int bj = -1;
            for (int d = lo; d <= hi; d++) {
                if (d == 0)
                    continue;
                int b = a + d;
                if (b >= N)
                    b -= N;
                else if (b < 0)
                    b += N;
                const int y = slotType[b];
                if (y == 0 ? !(ZCH_M & 1) : !(ZCH_M & 2))
                    continue;
                const ll dx = wcst2(x, g1 + d, g2 - d) - base;
                const int gb = publicGrid[b], ob = changeStamp[b] == op_ ? originalValue[b] : gb;
                const int dm = (gb != oa) - cna + (xid != ob) - (gb != ob);
                ll v0 = dx;
                if (dm > 0)
                    v0 += dm == 1 ? thr : (thr << 1);
                else if (dm < 0)
                    v0 -= dm == -1 ? thr : (thr << 1);
                const int ad = d < 0 ? -d : d;
                if (v0 - multiplyNonnegative(zchSl[y], ad) >= best)
                    continue;
                const ll dp = dMoveWI(y, b, a);
                if (dp == INVALID)
                    continue;
                const ll v = v0 + dp;
                if (v < best) {
                    best = v;
                    bj = b;
                }
            }
            if (bj >= 0) {
                const int y = slotType[bj];
                const int Lb = y ? prevSame[bj] : -1, Rb = y ? nextSame[bj] : -1;
                doSwap(a, bj);
                zchNL[k] = bj;
                zchMoves++;
                if (ZCH_SEED) {
                    pushSeed(L);
                    pushSeed(R);
                    pushSeed(a);
                    pushSeed(bj);
                    if (y) {
                        pushSeed(Lb);
                        pushSeed(Rb);
                    }
                }
            }
        }
}
#define ZCH_EX 0
#define ZCH_PR 0
#define ZCH_DPW 8
ull zchB[(MAXN >> 6) + 2];
int zchS[MAXN + 8], zchPart[MAXN + 8];
int zchLo[MAXN + 8], zchHi[MAXN + 8];
ll zchNC[(MAXN + 8) + ((MAXN + 8) << 4)];
unsigned char zchCh[MAXN + 8][(ZCH_DPW << 1) + 1];
ll zchExc = 0, zchRunsN = 0, zchRunsDone = 0;
__attribute__((noinline)) void zchRuns(int x, ll thr, int w) {
    const int nn = zchNN;
    if (nn == 0 || typeSize[x] < 3 || F[x] == 0)
        return;
    if (w > ZCH_DPW)
        w = ZCH_DPW;
    const int W = (w << 1) + 1;
    const ll INF = (ll)1 << 60;
    const int op_ = operationStamp, xid = serviceId[x];
#define ZCH_ALL 0
    if (ZCH_ALL) {
        for (int ww = 0; ww < NW; ww++) {
            ull b = TBit[(x << 8) + ww];
            while (b) {
                const int p = (ww << 6) + __builtin_ctzll(b);
                b &= b - 1;
                if (changeStamp[p] == op_ && originalValue[p] != xid)
                    zchB[ww] |= 1ULL << (p & 63);
            }
        }
    } else
        for (int k = 0; k < nn; k++) {
            const int p = zchNL[k];
            if (slotType[p] == x)
                zchB[p >> 6] |= 1ULL << (p & 63);
        }
    int m = 0;
    for (int ww = 0; ww < NW; ww++) {
        ull b = zchB[ww];
        zchB[ww] = 0;
        while (b) {
            zchS[m++] = (ww << 6) + __builtin_ctzll(b);
            b &= b - 1;
        }
    }
    if (m == 0)
        return;
    auto isNew = [&](int p) {
        return changeStamp[p] == op_ && originalValue[p] != xid && slotType[p] == x;
    };
    int st = -1;
    for (int k = 0; k < m; k++)
        if (!isNew(prevSame[zchS[k]])) {
            st = k;
            break;
        }
    if (st < 0)
        return;
    ll tv[5];
    tv[0] = -(thr << 1);
    tv[1] = -thr;
    tv[2] = 0;
    tv[3] = thr;
    tv[4] = thr << 1;
    const ll exT = multiplyNonnegative(thr, ZCH_EX) >> 4;
    ll V[(ZCH_DPW << 1) + 1], Vn[(ZCH_DPW << 1) + 1];
    int i = 0;
    while (i < m) {
        int k0 = st + i;
        if (k0 >= m)
            k0 -= m;
        const int a0 = zchS[k0];
        const int pL = prevSame[a0];
        int len = 0;
        {
            int p = a0;
            for (;;) {
                zchPart[len++] = p;
                const int nx = nextSame[p];
                if (!isNew(nx) || len >= m)
                    break;
                p = nx;
            }
        }
        i += len;
        const int pR = nextSame[zchPart[len - 1]];
        zchRunsN++;
        ll cur = 0;
        {
            int prev = pL;
            for (int k = 0; k < len; k++) {
                cur += wcst(x, dist(prev, zchPart[k]));
                prev = zchPart[k];
            }
            cur += wcst(x, dist(prev, pR));
            const ll publicGrid = dist(pL, pR);
            const ll q0 = divideNonnegative(publicGrid, len + 1),
                     r0 = publicGrid - multiplyNonnegative(q0, len + 1);
            const ll lb = multiplyNonnegative(wcst(x, (int)q0 + 1), r0) +
                          multiplyNonnegative(wcst(x, (int)q0), len + 1 - r0);
            if (ZCH_EX >= 0 && cur - lb <= exT)
                continue;
            zchExc += cur - lb;
        }
        zchRunsDone++;
        int prevP = pL;
        for (int k = 0; k < len; k++) {
            const int a = zchPart[k];
            const int nxP = k + 1 < len ? zchPart[k + 1] : pR;
            const int gl = dist(prevP, a), gr = dist(a, nxP);
            int lo = -w, hi = w;
            if (lo < 1 - gl)
                lo = 1 - gl;
            if (hi > gr - 1)
                hi = gr - 1;
            zchLo[k] = lo + w;
            zchHi[k] = hi + w;
            const int oa = changeStamp[a] == op_ ? originalValue[a] : xid, cna = xid != oa;
            const int ncO = (int)multiplyNonnegative(k, W) + w;
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
                    const int y = slotType[b];
                    const int ad = d < 0 ? -d : d;
                    if (y == 0 ? !(ZCH_M & 1) : !(ZCH_M & 2))
                        v = INF;
                    else if (ZCH_PR && y != 0 && typeSize[y] > 1 && ad > qv[y] + ZCH_PR - 1)
                        v = INF;
                    else {
                        const ll dp = dMoveWI(y, b, a);
                        if (dp == INVALID)
                            v = INF;
                        else {
                            const int gb = publicGrid[b],
                                      ob = changeStamp[b] == op_ ? originalValue[b] : gb;
                            const int dm = (gb != oa) - cna + (xid != ob) - (gb != ob);
                            v = dp + tv[dm + 2];
                        }
                    }
                }
                zchNC[ncO + d] = v;
            }
            prevP = a;
        }
        for (int d = 0; d < W; d++)
            V[d] = INF;
        V[w] = 0;
        int plo = w, phi = w;
        prevP = pL;
        for (int k = 0; k < len; k++) {
            const int a = zchPart[k];
            const int g0 = dist(prevP, a);
            const int dlo = zchLo[k], dhi = zchHi[k];
            const int ncO = (int)multiplyNonnegative(k, W);
            for (int d1 = 0; d1 < W; d1++)
                Vn[d1] = INF;
            for (int d1 = dlo; d1 <= dhi; d1++) {
                const ll ncv = zchNC[ncO + d1];
                if (ncv >= INF) {
                    zchCh[k][d1] = (unsigned char)w;
                    continue;
                }
                ll best = INF;
                int bd = w;
                for (int d0 = plo; d0 <= phi; d0++) {
                    if (V[d0] >= INF)
                        continue;
                    const int g = g0 + d1 - d0;
                    if (g < 1)
                        continue;
                    const ll v = V[d0] + wcst(x, g);
                    if (v < best) {
                        best = v;
                        bd = d0;
                    }
                }
                Vn[d1] = best >= INF ? INF : best + ncv;
                zchCh[k][d1] = (unsigned char)bd;
            }
            for (int d = 0; d < W; d++)
                V[d] = Vn[d];
            plo = dlo;
            phi = dhi;
            prevP = a;
        }
        const int gR = dist(prevP, pR);
        ll best = INF;
        int bd = -1;
        for (int d0 = plo; d0 <= phi; d0++) {
            if (V[d0] >= INF)
                continue;
            const int g = gR - (d0 - w);
            if (g < 1)
                continue;
            const ll v = V[d0] + wcst(x, g);
            if (v < best) {
                best = v;
                bd = d0;
            }
        }
        if (bd < 0 || best >= cur)
            continue;
        int d = bd;
        for (int k = len - 1; k >= 0; k--) {
            const int pd = zchCh[k][d];
            zchLo[k] = d;
            d = pd;
        }
        for (int k = 0; k < len; k++) {
            const int dd = zchLo[k] - w;
            if (dd == 0)
                continue;
            const int a = zchPart[k];
            int b = a + dd;
            if (b >= N)
                b -= N;
            else if (b < 0)
                b += N;
            if (slotType[a] != x || slotType[b] == x)
                continue;
            const int y = slotType[b];
            const int Lb = y ? prevSame[b] : -1, Rb = y ? nextSame[b] : -1;
            doSwap(a, b);
            zchMoves++;
            if (ZCH_SEED) {
                pushSeed(a);
                pushSeed(b);
                if (y) {
                    pushSeed(Lb);
                    pushSeed(Rb);
                }
            }
        }
        if (ZCH_SEED) {
            pushSeed(pL);
            pushSeed(pR);
        }
    }
}
