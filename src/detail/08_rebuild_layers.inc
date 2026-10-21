// 分层重构与重叠保持。为各类型生成均匀候选，利用与当前布局的重叠减少额外改动，再形成完整重构。
// Included in fixed order by solution.cpp.

unsigned char selTab[256][8];
bool selTabReady = false;
void buildSelTab() {
    for (int v = 0; v < 256; v++) {
        int k = 0;
        for (int b = 0; b < 8; b++)
            if ((v >> b) & 1)
                selTab[v][k++] = (unsigned char)b;
    }
    selTabReady = true;
}
SP2_I int select64(ull m, int k) {
    ull b = m - ((m >> 1) & 0x5555555555555555ULL);
    b = (b & 0x3333333333333333ULL) + ((b >> 2) & 0x3333333333333333ULL);
    b = (b + (b >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    ull pre = b + (b << 8);
    pre += pre << 16;
    pre += pre << 32;
    ull kk = (ull)(k + 1);
    kk |= kk << 8;
    kk |= kk << 16;
    kk |= kk << 32;
    ull ge = ((pre | 0x8080808080808080ULL) - kk) & 0x8080808080808080ULL;
    int bi = __builtin_ctzll(ge) >> 3;
    int before = bi ? (int)((pre >> ((bi - 1) << 3)) & 0xff) : 0;
    return (bi << 3) + selTab[(m >> (bi << 3)) & 0xff][k - before];
}
ull rbFB[(MAXN >> 6) + 2], rbCL[(MAXN >> 6) + 2];
int rbPC[(MAXN >> 6) + 2], rbTw[(MAXN >> 6) + 2];
int rbNTa[MAXN + 8];
int iqSA = -1, iqSB = -1;
int iqBestNT[MAXN + 8];
vector<pair<int, int>> rbTy;
int rbFirst[MAXT], rbLast[MAXT];
ll sdA[MAXT];
int sdG[MAXT];
ll rbPafter = 0;
int rbDeltaM = 0;
// 按类型数量分层构造重建布局，作为后续保留重叠的基础。
void rbAssign() {
    rbTy.clear();
    for (int t = 0; t < typeSlotCount; t++)
        if (typeSize[t] > 0)
            rbTy.push_back({typeSize[t], t});
    sort(rbTy.begin(), rbTy.end(), [](const pair<int, int> &a, const pair<int, int> &b) {
        return a.first > b.first || (a.first == b.first && a.second < b.second);
    });
    for (int w = 0; w < NW; w++) {
        rbFB[w] = ~0ULL;
        rbCL[w] = 0;
    }
    if (N & 63)
        rbFB[NW - 1] = (1ULL << (N & 63)) - 1;
    for (int w = 0; w < NW; w++)
        rbPC[w] = __builtin_popcountll(rbFB[w]);
    int freeN = N;
    int nTy = (int)rbTy.size();
    for (int ti = 0; ti < nTy; ti++) {
        int sc = rbTy[ti].first, t = rbTy[ti].second, n = freeN;
        if (sc <= 0 || n <= 0)
            continue;
        if (sc >= n) {
            for (int w = 0; w < NW; w++) {
                ull m = rbFB[w];
                while (m) {
                    int b = __builtin_ctzll(m);
                    m &= m - 1;
                    rbNTa[(w << 6) + b] = t;
                }
                rbFB[w] = 0;
                rbPC[w] = 0;
            }
            freeN = 0;
            break;
        }
        if ((sc << RBDS) >= n) {
            int acc = n >> 1;
            for (int w = 0; w < NW; w++) {
                ull m = rbFB[w], clr = 0;
                while (m) {
                    int b = __builtin_ctzll(m);
                    m &= m - 1;
                    acc += sc;
                    int fire = acc >= n;
                    acc -= fire ? n : 0;
                    clr |= (ull)fire << b;
                }
                if (clr) {
                    rbFB[w] &= ~clr;
                    rbPC[w] = __builtin_popcountll(rbFB[w]);
                    while (clr) {
                        int b = __builtin_ctzll(clr);
                        clr &= clr - 1;
                        rbNTa[(w << 6) + b] = t;
                    }
                }
            }
        } else {
            int q0 = (int)divideNonnegative(n, sc), r0 = n - (int)multiplyNonnegative(q0, sc);
            int u = n - (n >> 1);
            int A = (int)divideNonnegative(u + sc - 1, sc);
            int e = (int)multiplyNonnegative(A, sc) - u;
            int rank = A - 1;
            int w = 0, cnt = 0, nTw = 0;
            for (int j = 0; j < sc; j++) {
                while (cnt + rbPC[w] <= rank) {
                    cnt += rbPC[w];
                    w++;
                }
                int b = select64(rbFB[w], rank - cnt);
                rbNTa[(w << 6) + b] = t;
                rbTw[nTw] = w;
                nTw += rbCL[w] == 0;
                rbCL[w] |= 1ULL << b;
                if (r0 > e) {
                    rank += q0 + 1;
                    e += sc - r0;
                } else {
                    rank += q0;
                    e -= r0;
                }
            }
            for (int k = 0; k < nTw; k++) {
                int ww = rbTw[k];
                rbFB[ww] &= ~rbCL[ww];
                rbCL[ww] = 0;
                rbPC[ww] = __builtin_popcountll(rbFB[ww]);
            }
        }
        freeN -= sc;
    }
}
// 将选定的重构应用到当前状态，并维护各类型索引。
void applyReconstruction() {
    for (int w = 0; w <= NW; w++)
        vb[w] = 0;
    for (int w = 0; w < NS; w++)
        vs[w] = 0;
    for (int t = 0; t < typeSlotCount; t++) {
        rbFirst[t] = -1;
        rbLast[t] = -1;
        sdA[t] = 0;
        sdG[t] = 0;
        if (TBITS && t && typeSize[t] > 0)
            for (int w = 0; w < NW; w++)
                TBit[(t << 8) + w] = 0;
    }
    int dM = 0;
    const int op = operationStamp;
    for (int i = 0; i < N; i++) {
        int nt = rbNTa[i];
        int ng = serviceId[nt], gi = publicGrid[i];
        int o = changeStamp[i] == op ? originalValue[i] : gi;
        dM += (ng != o) - (gi != o);
        changeStamp[i] = op;
        originalValue[i] = o;
        slotType[i] = nt;
        publicGrid[i] = ng;
        if (TBITS)
            TBit[(nt << 8) + (i >> 6)] |= (ull)(nt != 0) << (i & 63);
        vb[i >> 6] |= (ull)(nt == 0) << (i & 63);
        int l = rbLast[nt];
        if (l < 0)
            rbFirst[nt] = i;
        else {
            nextSame[l] = i;
            prevSame[i] = l;
            int dg = i - l - qv[nt];
            sdA[nt] += dg < 0 ? -dg : dg;
            sdG[nt] += dg > 0;
        }
        rbLast[nt] = i;
    }
    if (xlsSBon) {
        for (int w = 0; w < NW; w++)
            xlsSB[w] = ~0ULL;
        if (N & 63)
            xlsSB[NW - 1] = (1ULL << (N & 63)) - 1;
    }
    ll P = 0;
    for (int t = 0; t < typeSlotCount; t++) {
        int f = rbFirst[t];
        typeHead[t] = f;
        if (f < 0)
            continue;
        int l = rbLast[t];
        nextSame[l] = f;
        prevSame[f] = l;
        int dg = f + N - l - qv[t];
        sdA[t] += dg < 0 ? -dg : dg;
        sdG[t] += dg > 0;
        int sc = typeSize[t];
        if (sc < 2 || F[t] == 0)
            continue;
        int nd = sc - (sdG[t] << 1);
        ll sd = multiplyNonnegative(sdA[t], sc) +
                (nd >= 0 ? multiplyNonnegative(rv[t], nd) : -multiplyNonnegative(rv[t], -nd));
        ll pt = multiplyNonnegative(sd, F[t]);
        PtC[t] = pt;
        typePenaltyDirty[t] = 0;
        P += pt;
    }
    for (int w = 0; w < NW; w++)
        if (vb[w])
            vs[w >> 6] |= 1ULL << (w & 63);
    rbPafter = P;
    rbDeltaM = dM;
}
__attribute__((noinline)) void fullRebuild() {
    rbAssign();
    applyReconstruction();
}
#define DDD 2
#define OA 1
#define HVK 2
#define GTOL 3
#define HRB 20
#define QB 4
#define BFR 1
#define DPS3U 1
RVEC(int) omFr, omNf, omPos, omOrd, omIdx, omRec, omPre;
#define PREHIT 1
RVEC(unsigned short) omHitS, omGoodS;
RVEC(unsigned char) omGood;
RVEC(ull) omChP;
ll omHV = 0, omP = 0, omSteps = 0;
int rqC = 0;
int omTk[MAXN], omSer = 0;
int rqDm[MAXT];
ll rqPn[MAXT];
ll omLam = 0;
RVEC(int) omPosB;
ll P0c = 0;
int omM = 0;
ll omTab[129], omTabF[129];
int omTq = 0;
const ll OMNEG = -((ll)1 << 60);
SP2_I ll lamFor(int c) {
    return divideNonnegative(
        multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
        multiplyNonnegative(multiplyNonnegative(11, HRB), N - c > 0 ? N - c : 1));
}
RVEC(int) cgLast, cgFirst, cgLo, cgHi;
#define VC_OMG0 0
#define OM2_HVT 16
#define OM2_HVU 16
#define OM2_GAT -1
#define OM2_GAU -1
#define OM2_GAV -1
#define OM2_GU 0
#define OM2_HVH 0
#define OM2_HVA 0
#define OM2_PARTV 1
#define OM2_PART_T 0
#define OM2_DDS 0
#define OM2_DDS_T 0
#define OM2_DDD 0
#define OM2_DDD_T 0
#define OM2_RVB 0
#define OM2_RVB_T 0
#define OM2_POL -1
#define OM2_POL_T -1
#define OM2_BKA 0
#define OM2_BKA_T 0
#define OM2_BKB 0
#define OM2_BKB_T 0
#define OM2_DDSC 7
#define OM2_DDSN 0
#define OM2_DDSX 0
#define OM2_KEEP 0
#define OM2_KEEP_T 0
#define OM2_KW 0
#define OM2_KW_T 0
#define OM2_KR -1
#define OM2_KR_T -1
#define OM2_RVO_T 0
#define OM2_HVV 16
#define OM2_HVV_T 16
#define OM2_BKC 0
#define OM2_BKC_T 0
#define SQ_OMS 1000
#define SQ_OMLO 100
#define OM2_TK(K) (N <= SQ_OMLO ? K##_T : (N <= SQ_OMS ? K##_S : (N <= NM ? K##_M : K##_B)))
#define OM2_HVT_T 16
#define OM2_HVU_T 16
#define OM2_GAT_T -1
#define OM2_GAU_T -1
#define OM2_GAV_T -1
#define OM2_GU_T 0
#define OM2_GREL_T 0
#define OM2_HVH_T 0
#define OM2_HVA_T 0
#define OM2_CLSON                                                                                  \
    (OM2_HVV_S != 16 || OM2_HVV_M != 16 || OM2_HVV_B != 16 || OM2_HVT_S != 16 ||                   \
     OM2_HVT_M != 16 || OM2_HVT_B != 16 || OM2_HVU_S != 16 || OM2_HVU_M != 16 ||                   \
     OM2_HVU_B != 16 || OM2_GAT_S >= 0 || OM2_GAT_M >= 0 || OM2_GAT_B >= 0 || OM2_GAU_S >= 0 ||    \
     OM2_GAU_M >= 0 || OM2_GAU_B >= 0 || OM2_GAV_S >= 0 || OM2_GAV_M >= 0 || OM2_GAV_B >= 0)
#define OM2_GRELON (OM2_GREL_S || OM2_GREL_M || OM2_GREL_B)
int om2Rep = 0;
int om2WideDDS = 0;
int om2Grel = 0;
unsigned char om2Placed[MAXT];
void om2GoodAdj();
void computeGood() {
    if (blGAMMA == 0) {
        if ((int)omGoodS.size() != N)
            omGoodS.assign(N, 0);
        return;
    }
#define RB_XCG 1
    if (RB_XCG && TBITS && N >= 64) {
        omGoodS.resize(N);
        const int nt = typeSlotCount;
        cgLo.resize(nt);
        cgHi.resize(nt);
        for (int t = 0; t < nt; t++) {
            int q = qv[t];
            int a = q >> GTOL;
            if (a < 1)
                a = 1;
            cgLo[t] = q - a;
            cgHi[t] = q + 1 + a;
        }
        auto gS = omGoodS.data();
        auto lo_ = cgLo.data();
        auto hi_ = cgHi.data();
        const int nn = N;
        for (int w = 0; w < NW; w++) {
            ull m = ~vb[w];
            if (((w + 1) << 6) > nn)
                m &= (1ULL << (nn & 63)) - 1;
            while (m) {
                const int i = (w << 6) + __builtin_ctzll(m);
                m &= m - 1;
                const int t = slotType[i];
                int g1 = i - prevSame[i];
                g1 += g1 <= 0 ? nn : 0;
                int g2 = nextSame[i] - i;
                g2 += g2 <= 0 ? nn : 0;
                const int l = lo_[t], h = hi_[t];
                const int ok = (g1 >= l) & (g1 <= h) & (g2 >= l) & (g2 <= h);
                gS[i] = (unsigned short)(ok << 1);
            }
        }
        for (int t = 1; t < nt; t++)
            if (typeSize[t] == 1)
                gS[typeHead[t]] = 0;
        if (typeSize[0] >= 1) {
            const int l = lo_[0], h = hi_[0];
            int w = 0;
            ull m = 0;
            while (!(m = vb[w]))
                w++;
            const int first = (w << 6) + __builtin_ctzll(m);
            m &= m - 1;
            int last = first, okp = 0, okFirst = 0, nv = 1;
            for (;;) {
                while (m) {
                    const int i = (w << 6) + __builtin_ctzll(m);
                    m &= m - 1;
                    const int g = i - last;
                    const int ok = (g >= l) & (g <= h);
                    if (nv == 1)
                        okFirst = ok;
                    else
                        gS[last] = (unsigned short)((okp & ok) << 1);
                    okp = ok;
                    last = i;
                    nv++;
                }
                if (++w >= NW)
                    break;
                m = vb[w];
            }
            if (nv == 1)
                gS[first] = 0;
            else {
                const int g = first + nn - last;
                const int ok = (g >= l) & (g <= h);
                gS[last] = (unsigned short)((okp & ok) << 1);
                gS[first] = (unsigned short)((ok & okFirst) << 1);
            }
        }
        if (VC_OMG0 && N > NM) {
            for (int w = 0; w < NW; w++) {
                ull m = vb[w];
                while (m) {
                    omGoodS[(w << 6) + __builtin_ctzll(m)] = 0;
                    m &= m - 1;
                }
            }
        }
        if ((OM2_GU_S || OM2_GU_M || OM2_GU_B) && om2Rep && OM2_TK(OM2_GU))
            om2GoodAdj();
        return;
    }
    if (RB_XCG) {
        omGoodS.resize(N);
        int nt = typeSlotCount;
        cgLast.assign(nt, -1);
        cgFirst.resize(nt);
        cgLo.resize(nt);
        cgHi.resize(nt);
        for (int t = 0; t < nt; t++) {
            int q = qv[t];
            int a = q >> GTOL;
            if (a < 1)
                a = 1;
            cgLo[t] = q - a;
            cgHi[t] = q + 1 + a;
        }
        for (int i = 0; i < N; i++) {
            int t = slotType[i];
            int l = cgLast[t];
            if (l >= 0) {
                int g = i - l;
                unsigned short ok =
                    (g >= cgLo[t] && g <= cgHi[t]) ? (unsigned short)2 : (unsigned short)0;
                omGoodS[l] &= ok;
                omGoodS[i] = ok;
            } else {
                cgFirst[t] = i;
                omGoodS[i] = 2;
            }
            cgLast[t] = i;
        }
        for (int t = 0; t < nt; t++) {
            int l = cgLast[t];
            if (l < 0)
                continue;
            if (typeSize[t] < 2) {
                omGoodS[l] = 0;
                continue;
            }
            int f = cgFirst[t];
            int g = f + N - l;
            unsigned short ok =
                (g >= cgLo[t] && g <= cgHi[t]) ? (unsigned short)2 : (unsigned short)0;
            omGoodS[l] &= ok;
            omGoodS[f] &= ok;
        }
        if (VC_OMG0 && N > NM) {
            for (int w = 0; w < NW; w++) {
                ull m = vb[w];
                while (m) {
                    omGoodS[(w << 6) + __builtin_ctzll(m)] = 0;
                    m &= m - 1;
                }
            }
        }
        if ((OM2_GU_S || OM2_GU_M || OM2_GU_B) && om2Rep && OM2_TK(OM2_GU))
            om2GoodAdj();
        return;
    }
    omGood.resize(N);
    omGoodS.resize(N);
    int nt = typeSlotCount;
    cgLast.assign(nt, -1);
    cgFirst.resize(nt);
    cgLo.resize(nt);
    cgHi.resize(nt);
    for (int t = 0; t < nt; t++) {
        int q = qv[t];
        int a = q >> GTOL;
        if (a < 1)
            a = 1;
        cgLo[t] = q - a;
        cgHi[t] = q + 1 + a;
    }
    for (int i = 0; i < N; i++) {
        int t = slotType[i];
        int l = cgLast[t];
        if (l >= 0) {
            int g = i - l;
            unsigned char ok = (g >= cgLo[t] && g <= cgHi[t]) ? 1 : 0;
            omGood[l] &= ok;
            omGood[i] = ok;
        } else {
            cgFirst[t] = i;
            omGood[i] = 1;
        }
        cgLast[t] = i;
    }
    for (int t = 0; t < nt; t++) {
        int l = cgLast[t];
        if (l < 0)
            continue;
        if (typeSize[t] < 2) {
            omGood[l] = 0;
            continue;
        }
        int f = cgFirst[t];
        int g = f + N - l;
        unsigned char ok = (g >= cgLo[t] && g <= cgHi[t]) ? 1 : 0;
        omGood[l] &= ok;
        omGood[f] &= ok;
    }
    for (int i = 0; i < N; i++)
        omGoodS[i] = blGAMMA > 0 ? (unsigned short)(omGood[i] << 1) : (unsigned short)0;
}
int omTabT = -1;
const int SXOFF = 512;
ll omTabX[129 + (SXOFF << 1)];
int omTabSer = 0, omTabXSer = -1;
int omTabXlo = 0, omTabXhi = 128;
void omTabFor(int t) {
    if (omTabT == t)
        return;
    omTabT = t;
    omTabSer++;
    int s_ = typeSize[t];
    int g0 = qv[t] - 64;
    ll v = -(ll)N;
    if (g0 > 0)
        v = multiplyNonnegative(s_, g0) - N;
    const ll fT = F[t];
    ll sF = multiplyNonnegative(s_, fT), NF = multiplyNonnegative(N, fT);
    ll vf = g0 > 0 ? multiplyNonnegative(sF, g0) - NF : -NF;
    for (int k = 0; k < 129; k++) {
        int g = g0 + k;
        if (g < 0) {
            omTab[k] = 0;
            omTabF[k] = 0;
            continue;
        }
        omTab[k] = v < 0 ? -v : v;
        omTabF[k] = vf < 0 ? -vf : vf;
        v += s_;
        vf += sF;
    }
    omTq = g0;
}
SP2_I ll omCst(int t, int g) {
    int k = g - omTq;
    if (k >= 0 && k < 129)
        return omTab[k];
    return cst(t, g);
}
SP2_I ll omCstF(int t, int g) {
    int k = g - omTq;
    if (k >= 0 && k < 129)
        return omTabF[k];
    return multiplyNonnegative(cst(t, g), F[t]);
}
SP2_I ll rcost(int g) {
    int k = g - omTq;
    k = k < 0 ? 0 : (k > 128 ? 128 : k);
    return omTabF[k];
}
template <int D, bool LAZY, bool RDM>
// 对单一类型的重叠候选作动态规划，将间隔质量与保留旧格子的收益合并。
bool omDP(int t, int sc, int n, int i0) {
    int Q = (int)divideNonnegative(n, sc), R = n - (int)multiplyNonnegative(Q, sc);
    ll devU = divideNonnegative(multiplyNonnegative(multiplyNonnegative(F[t], (ll)sc << 1), N), n);
    const ll HV = omHV;
    const ll GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const int W = (D << 1) + 1;
    const int PAD = 3;
    const bool allowM = (LAZY ? OAS : OA) > 0 && Q >= 2;
    const bool allowP = (LAZY ? OAS : OA) > 0;
    const ll pen1 = RDM ? 0 : (R == 0 ? devU : 0);
    const ll BIG = (ll)1 << 61;
    const ll penM = allowM ? (RDM ? 0 : devU) : BIG;
    const ll penP = allowP ? (RDM ? 0 : devU) : BIG;
    const ll fT = F[t];
    ll hval[4];
    hval[0] = 0;
    hval[1] = HV;
    hval[2] = -GV;
    hval[3] = OMNEG;
    ll Vp[(D << 1) + 1 + 6], Vn[(D << 1) + 1 + 6];
    int prvR[(D << 1) + 1 + 6], curR[(D << 1) + 1 + 6];
    for (int w = 0; w < W + PAD + PAD; w++) {
        Vp[w] = OMNEG;
        Vn[w] = OMNEG;
        prvR[w] = omFr[i0];
        curR[w] = omFr[i0];
    }
    if (RDM) {
        omTabFor(t);
    }
    omChP.resize(sc);
    {
        int c0;
        if (LAZY) {
            int r = omRec[i0];
            c0 = (r & 1) ? 3 : (((r >> 2) == t) ? 1 : (r & 2));
        } else
            c0 = omHitS[i0];
        Vp[D + PAD] = hval[c0];
    }
    int baseU = i0, cj = 0, acc = 0;
    for (int j = 1; j < sc; j++) {
        baseU += Q;
        int cn = cj;
        acc += R;
        if (acc >= sc) {
            acc -= sc;
            cn++;
        }
        int x0 = cn - cj + PAD;
        int hu = baseU + cn - D;
        unsigned hc[(D << 1) + 1];
        if (hu >= 0 && hu + W <= n) {
            for (int wn = 0; wn < W; wn++) {
                const int pos = hu + wn;
                if (LAZY) {
                    int r = omRec[pos];
                    hc[wn] = (r & 1) ? 3u : (((r >> 2) == t) ? 1u : (unsigned)(r & 2));
                } else
                    hc[wn] = omHitS[pos];
                if (RDM)
                    curR[wn + PAD] = omFr[pos];
            }
        } else
            for (int wn = 0; wn < W; wn++) {
                int uu = hu + wn, pos = uu, add = 0;
                while (pos >= n) {
                    pos -= n;
                    add += N;
                }
                while (pos < 0) {
                    pos += n;
                    add -= N;
                }
                if (LAZY) {
                    int r = omRec[pos];
                    hc[wn] = (r & 1) ? 3u : (((r >> 2) == t) ? 1u : (unsigned)(r & 2));
                } else
                    hc[wn] = omHitS[pos];
                if (RDM)
                    curR[wn + PAD] = omFr[pos] + add;
            }
        ull pk = 0;
        ll mxv = OMNEG;
        for (int wn = 0; wn < W; wn++) {
            int x = wn + x0;
            ll bv, v1, vm, v2;
            if (RDM) {
                int cr = curR[wn + PAD];
                bv = Vp[x] - rcost(cr - prvR[x]);
                v1 = Vp[x - 1] - rcost(cr - prvR[x - 1]);
                vm = Vp[x + 1] - rcost(cr - prvR[x + 1]) - penM;
                v2 = Vp[x - 2] - rcost(cr - prvR[x - 2]) - penP;
            } else {
                bv = Vp[x];
                v1 = Vp[x - 1] - pen1;
                vm = Vp[x + 1] - penM;
                v2 = Vp[x - 2] - penP;
            }
            unsigned ch = 1;
            ch = v1 > bv ? 2u : ch;
            bv = v1 > bv ? v1 : bv;
            ch = vm > bv ? 0u : ch;
            bv = vm > bv ? vm : bv;
            ch = v2 > bv ? 3u : ch;
            bv = v2 > bv ? v2 : bv;
            ll nv = bv + hval[hc[wn]];
            nv = nv < OMNEG ? OMNEG : nv;
            Vn[wn + PAD] = nv;
            mxv = nv > mxv ? nv : mxv;
            pk |= (ull)ch << (wn << 1);
        }
        if (mxv <= (OMNEG >> 1))
            return false;
        omChP[j] = pk;
        for (int w = 0; w < W; w++)
            Vp[w + PAD] = Vn[w + PAD];
        if (RDM) {
            for (int w = 0; w < W; w++)
                prvR[w + PAD] = curR[w + PAD];
            prvR[PAD - 1] = prvR[PAD - 2] = prvR[PAD - 3] = curR[PAD];
            prvR[PAD + W] = prvR[PAD + W + 1] = prvR[PAD + W + 2] = curR[PAD + W - 1];
        }
        cj = cn;
    }
    int bw = -1;
    ll bv = OMNEG >> 1;
    for (int w = 0; w < W; w++) {
        ll v = Vp[w + PAD];
        if (v <= (OMNEG >> 1))
            continue;
        int u = cj + w - D;
        int bl = R - u;
        if (bl < (allowM ? -1 : 0) || bl > (allowP ? 2 : 1))
            continue;
        if (RDM)
            v -= rcost(omFr[i0] + N - prvR[w + PAD]);
        else if (bl == -1 || bl == 2)
            v -= devU;
        else if (bl == 1)
            v -= pen1;
        if (v > bv) {
            bv = v;
            bw = w;
        }
    }
    if (bw < 0)
        return false;
    omPos.resize(sc);
    int u = cj + bw - D;
    int accb = acc, cc = cj;
    ll p = baseU + u;
    while (p >= n)
        p -= n;
    while (p < 0)
        p += n;
    for (int j = sc - 1; j >= 0; j--) {
        omPos[j] = (int)p;
        if (j == 0)
            break;
        int w = u - cc + D;
        int bb = (int)((omChP[j] >> (w << 1)) & 3ULL) - 1;
        u -= bb;
        p -= Q + bb;
        if (p < 0)
            p += n;
        int prevAcc = accb - R;
        if (prevAcc < 0) {
            prevAcc += sc;
            cc--;
        }
        accb = prevAcc;
    }
    return true;
}
template <int D> bool omDPS(int t, int sc, int n, int i0) {
    int Q = (int)divideNonnegative(n, sc), R = n - (int)multiplyNonnegative(Q, sc);
    const ll HV = omHV;
    const ll GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const int W = (D << 1) + 1;
    const int PAD = 3;
    const int WT = W + PAD + PAD;
    const bool allowM = OAS > 0 && Q >= 2;
    const bool allowP = OAS > 0;
    const ll BIG = (ll)1 << 61;
    const ll penM = allowM ? 0 : BIG;
    const ll penP = allowP ? 0 : BIG;
    const ll fT = F[t];
    omTabFor(t);
    const int tq = omTq;
    const int t4 = t << 2;
    const bool useX = sc >= 32;
    if (useX && omTabXSer != omTabSer) {
        omTabXSer = omTabSer;
        const ll lo = omTabF[0], hi = omTabF[128];
        for (int k = 0; k < SXOFF; k++) {
            omTabX[k] = lo;
            omTabX[SXOFF + 129 + k] = hi;
        }
        for (int k = 0; k <= 128; k++)
            omTabX[SXOFF + k] = omTabF[k];
    }
    ll hval[4];
    hval[0] = 0;
    hval[1] = HV;
    hval[2] = -GV;
    hval[3] = OMNEG;
    ll V[2][WT];
    int PR[2][WT];
    for (int w = 0; w < WT; w++) {
        V[0][w] = OMNEG;
        V[1][w] = OMNEG;
        PR[0][w] = omFr[i0] + tq;
        PR[1][w] = omFr[i0] + tq;
    }
    omChP.resize(sc);
    {
        int r = omRec[i0];
        int c0 = (r & 1) ? 3 : (((r & ~3) == t4) ? 1 : (r & 2));
        V[0][D + PAD] = hval[c0];
    }
    int cur = 0;
    int baseU = i0, cj = 0, acc = 0;
    for (int j = 1; j < sc; j++) {
        baseU += Q;
        int cn = cj;
        acc += R;
        if (acc >= sc) {
            acc -= sc;
            cn++;
        }
        const int x0 = cn - cj + PAD;
        int pos = baseU + cn - D, add = 0;
        while (pos >= n) {
            pos -= n;
            add += N;
        }
        while (pos < 0) {
            pos += n;
            add -= N;
        }
        const int nx = cur ^ 1;
        ll hv[(D << 1) + 1];
        int crq[(D << 1) + 1];
        for (int wn = 0; wn < W; wn++) {
            int r = omRec[pos];
            int code = (r & 1) ? 3 : (((r & ~3) == t4) ? 1 : (r & 2));
            hv[wn] = hval[code];
            int cr = omFr[pos] + add;
            crq[wn] = cr;
            PR[nx][wn + PAD] = cr + tq;
            pos++;
            if (pos >= n) {
                pos -= n;
                add += N;
            }
        }
        ull pk = 0;
        ll mxv = OMNEG;
        if (useX && crq[0] - PR[cur][x0 + W] >= -SXOFF &&
            crq[W - 1] - PR[cur][x0 - 2] <= 128 + SXOFF) {
            for (int wn = 0; wn < W; wn++) {
                const int x = wn + x0;
                const int cr = crq[wn] + SXOFF;
                ll bv = V[cur][x] - omTabX[cr - PR[cur][x]];
                ll v1 = V[cur][x - 1] - omTabX[cr - PR[cur][x - 1]];
                ll vm = V[cur][x + 1] - omTabX[cr - PR[cur][x + 1]] - penM;
                ll v2 = V[cur][x - 2] - omTabX[cr - PR[cur][x - 2]] - penP;
                unsigned ch = 1;
                ch = v1 > bv ? 2u : ch;
                bv = v1 > bv ? v1 : bv;
                ch = vm > bv ? 0u : ch;
                bv = vm > bv ? vm : bv;
                ch = v2 > bv ? 3u : ch;
                bv = v2 > bv ? v2 : bv;
                ll nv = bv + hv[wn];
                nv = nv < OMNEG ? OMNEG : nv;
                V[nx][wn + PAD] = nv;
                mxv = nv > mxv ? nv : mxv;
                pk |= (ull)ch << (wn << 1);
            }
        } else
            for (int wn = 0; wn < W; wn++) {
                const int x = wn + x0;
                const int cr = crq[wn];
                int k0 = cr - PR[cur][x], k1 = cr - PR[cur][x - 1], km = cr - PR[cur][x + 1],
                    k2 = cr - PR[cur][x - 2];
                k0 = k0 < 0 ? 0 : (k0 > 128 ? 128 : k0);
                k1 = k1 < 0 ? 0 : (k1 > 128 ? 128 : k1);
                km = km < 0 ? 0 : (km > 128 ? 128 : km);
                k2 = k2 < 0 ? 0 : (k2 > 128 ? 128 : k2);
                ll bv = V[cur][x] - omTabF[k0];
                ll v1 = V[cur][x - 1] - omTabF[k1];
                ll vm = V[cur][x + 1] - omTabF[km] - penM;
                ll v2 = V[cur][x - 2] - omTabF[k2] - penP;
                unsigned ch = 1;
                ch = v1 > bv ? 2u : ch;
                bv = v1 > bv ? v1 : bv;
                ch = vm > bv ? 0u : ch;
                bv = vm > bv ? vm : bv;
                ch = v2 > bv ? 3u : ch;
                bv = v2 > bv ? v2 : bv;
                ll nv = bv + hv[wn];
                nv = nv < OMNEG ? OMNEG : nv;
                V[nx][wn + PAD] = nv;
                mxv = nv > mxv ? nv : mxv;
                pk |= (ull)ch << (wn << 1);
            }
        if (mxv <= (OMNEG >> 1))
            return false;
        omChP[j] = pk;
        {
            const int a = PR[nx][PAD], b = PR[nx][PAD + W - 1];
            PR[nx][PAD - 1] = a;
            PR[nx][PAD - 2] = a;
            PR[nx][PAD - 3] = a;
            PR[nx][PAD + W] = b;
            PR[nx][PAD + W + 1] = b;
            PR[nx][PAD + W + 2] = b;
        }
        cur = nx;
        cj = cn;
    }
    int bw = -1;
    ll bv = OMNEG >> 1;
    for (int w = 0; w < W; w++) {
        ll v = V[cur][w + PAD];
        if (v <= (OMNEG >> 1))
            continue;
        int u = cj + w - D;
        int bl = R - u;
        if (bl < (allowM ? -1 : 0) || bl > (allowP ? 2 : 1))
            continue;
        int k = omFr[i0] + N - PR[cur][w + PAD];
        k = k < 0 ? 0 : (k > 128 ? 128 : k);
        v -= omTabF[k];
        if (v > bv) {
            bv = v;
            bw = w;
        }
    }
    if (bw < 0)
        return false;
    omPos.resize(sc);
    int u = cj + bw - D;
    int accb = acc, cc = cj;
    ll p = baseU + u;
    while (p >= n)
        p -= n;
    while (p < 0)
        p += n;
    for (int j = sc - 1; j >= 0; j--) {
        omPos[j] = (int)p;
        if (j == 0)
            break;
        int w = u - cc + D;
        int bb = (int)((omChP[j] >> (w << 1)) & 3ULL) - 1;
        u -= bb;
        p -= Q + bb;
        if (p < 0)
            p += n;
        int prevAcc = accb - R;
        if (prevAcc < 0) {
            prevAcc += sc;
            cc--;
        }
        accb = prevAcc;
    }
    return true;
}
static SP2_I int omCk(int k) {
    k = k < 0 ? 0 : k;
    return k > 128 ? 128 : k;
}
#define OMCAND(val, code)                                                                          \
    {                                                                                              \
        ll v_ = (val);                                                                             \
        ch = v_ > bv ? (code) : ch;                                                                \
        bv = v_ > bv ? v_ : bv;                                                                    \
    }
#define OMFIN(w)                                                                                   \
    {                                                                                              \
        ll nv_ = bv + H##w;                                                                        \
        nv_ = nv_ < OMNEG ? OMNEG : nv_;                                                           \
        N##w = nv_;                                                                                \
        pk |= ch << ((w) << 1);                                                                    \
    }
#define OMEC(w, pw) omTabF[omCk(C##w - P##pw)]
bool omDPS2(int t, int sc, int n, int i0) {
    omSteps += sc;
    int Q = (int)divideNonnegative(n, sc), R = n - (int)multiplyNonnegative(Q, sc);
    const ll HV = omHV;
    const ll GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const bool allowM = OAS > 0 && Q >= 2;
    const bool allowP = OAS > 0;
    const ll BIG = (ll)1 << 61;
    const ll penM = allowM ? 0 : BIG;
    const ll fT = F[t];
    omTabFor(t);
    const int tq = omTq;
    const int t4 = t << 2;
    ll hval[4];
    hval[0] = 0;
    hval[1] = HV;
    hval[2] = -GV;
    hval[3] = OMNEG;
    ll V0 = OMNEG, V1 = OMNEG, V2, V3 = OMNEG, V4 = OMNEG;
    int P0 = omFr[i0] + tq, P1 = P0, P2 = P0, P3 = P0, P4 = P0;
    {
        int r = omRec[i0];
        int c0 = (r & 1) ? 3 : (((r & ~3) == t4) ? 1 : (r & 2));
        V2 = hval[c0];
    }
    omChP.resize(sc);
    int baseU = i0, cj = 0, acc = 0;
    for (int j = 1; j < sc; j++) {
        baseU += Q;
        int cn = cj;
        acc += R;
        if (acc >= sc) {
            acc -= sc;
            cn++;
        }
        int pos = baseU + cn - 2, add = 0;
        if (pos >= n) {
            pos -= n;
            add = N;
            if (pos >= n) {
                pos -= n;
                add += N;
            }
        } else if (pos < 0) {
            pos += n;
            add = -N;
        }
        ll H0, H1, H2, H3, H4;
        int C0, C1, C2, C3, C4;
#define OMLD(w)                                                                                    \
    {                                                                                              \
        int r_ = omRec[pos];                                                                       \
        ll h_ = ((r_ & ~3) == t4) ? HV : ((r_ & 2) ? -GV : 0);                                     \
        H##w = (r_ & 1) ? OMNEG : h_;                                                              \
        C##w = omFr[pos] + add;                                                                    \
        pos++;                                                                                     \
        if (pos >= n) {                                                                            \
            pos -= n;                                                                              \
            add += N;                                                                              \
        }                                                                                          \
    }
        OMLD(0)
        OMLD(1) OMLD(2) OMLD(3) OMLD(4)
#undef OMLD
            ll N0,
            N1, N2, N3, N4;
        unsigned pk = 0;
        if (cn == cj) {
            {
                ll bv = V0 - OMEC(0, 0);
                unsigned ch = 1;
                OMCAND(V1 - OMEC(0, 1) - penM, 0u) OMFIN(0)
            }
            {
                ll bv = V1 - OMEC(1, 1);
                unsigned ch = 1;
                OMCAND(V0 - OMEC(1, 0), 2u) OMCAND(V2 - OMEC(1, 2) - penM, 0u) OMFIN(1)
            }
            {
                ll bv = V2 - OMEC(2, 2);
                unsigned ch = 1;
                OMCAND(V1 - OMEC(2, 1), 2u)
                OMCAND(V3 - OMEC(2, 3) - penM, 0u) OMCAND(V0 - OMEC(2, 0), 3u) OMFIN(2)
            }
            {
                ll bv = V3 - OMEC(3, 3);
                unsigned ch = 1;
                OMCAND(V2 - OMEC(3, 2), 2u)
                OMCAND(V4 - OMEC(3, 4) - penM, 0u) OMCAND(V1 - OMEC(3, 1), 3u) OMFIN(3)
            }
            {
                ll bv = V4 - OMEC(4, 4);
                unsigned ch = 1;
                OMCAND(V3 - OMEC(4, 3), 2u) OMCAND(V2 - OMEC(4, 2), 3u) OMFIN(4)
            }
        } else {
            {
                ll bv = V1 - OMEC(0, 1);
                unsigned ch = 1;
                OMCAND(V0 - OMEC(0, 0), 2u) OMCAND(V2 - OMEC(0, 2) - penM, 0u) OMFIN(0)
            }
            {
                ll bv = V2 - OMEC(1, 2);
                unsigned ch = 1;
                OMCAND(V1 - OMEC(1, 1), 2u)
                OMCAND(V3 - OMEC(1, 3) - penM, 0u) OMCAND(V0 - OMEC(1, 0), 3u) OMFIN(1)
            }
            {
                ll bv = V3 - OMEC(2, 3);
                unsigned ch = 1;
                OMCAND(V2 - OMEC(2, 2), 2u)
                OMCAND(V4 - OMEC(2, 4) - penM, 0u) OMCAND(V1 - OMEC(2, 1), 3u) OMFIN(2)
            }
            {
                ll bv = V4 - OMEC(3, 4);
                unsigned ch = 1;
                OMCAND(V3 - OMEC(3, 3), 2u) OMCAND(V2 - OMEC(3, 2), 3u) OMFIN(3)
            }
            {
                ll bv = V4 - OMEC(4, 4);
                unsigned ch = 2;
                OMCAND(V3 - OMEC(4, 3), 3u) OMFIN(4)
            }
        }
        ll mx = N0 > N1 ? N0 : N1;
        mx = N2 > mx ? N2 : mx;
        mx = N3 > mx ? N3 : mx;
        mx = N4 > mx ? N4 : mx;
        if (mx <= (OMNEG >> 1))
            return false;
        omChP[j] = pk;
        V0 = N0;
        V1 = N1;
        V2 = N2;
        V3 = N3;
        V4 = N4;
        P0 = C0 + tq;
        P1 = C1 + tq;
        P2 = C2 + tq;
        P3 = C3 + tq;
        P4 = C4 + tq;
        cj = cn;
    }
    int bw = -1;
    ll bv = OMNEG >> 1;
    for (int w = 0; w < 5; w++) {
        ll v = w == 0 ? V0 : (w == 1 ? V1 : (w == 2 ? V2 : (w == 3 ? V3 : V4)));
        int pw = w == 0 ? P0 : (w == 1 ? P1 : (w == 2 ? P2 : (w == 3 ? P3 : P4)));
        if (v <= (OMNEG >> 1))
            continue;
        int u = cj + w - 2;
        int bl = R - u;
        if (bl < (allowM ? -1 : 0) || bl > (allowP ? 2 : 1))
            continue;
        v -= omTabF[omCk(omFr[i0] + N - pw)];
        if (v > bv) {
            bv = v;
            bw = w;
        }
    }
    if (bw < 0)
        return false;
    omPos.resize(sc);
    int u = cj + bw - 2;
    int accb = acc, cc = cj;
    ll p = baseU + u;
    while (p >= n)
        p -= n;
    while (p < 0)
        p += n;
    for (int j = sc - 1; j >= 0; j--) {
        omPos[j] = (int)p;
        if (j == 0)
            break;
        int w = u - cc + 2;
        int bb = (int)((omChP[j] >> (w << 1)) & 3ULL) - 1;
        u -= bb;
        p -= Q + bb;
        if (p < 0)
            p += n;
        int prevAcc = accb - R;
        if (prevAcc < 0) {
            prevAcc += sc;
            cc--;
        }
        accb = prevAcc;
    }
    return true;
}
#undef OMCAND
#undef OMFIN
#undef OMEC
#define OMCAND(val, code)                                                                          \
    {                                                                                              \
        ll v_ = (val);                                                                             \
        ch = v_ > bv ? (code) : ch;                                                                \
        bv = v_ > bv ? v_ : bv;                                                                    \
    }
#define OMFIN(w)                                                                                   \
    {                                                                                              \
        ll nv_ = bv + H##w;                                                                        \
        nv_ = nv_ < OMNEG ? OMNEG : nv_;                                                           \
        N##w = nv_;                                                                                \
        pk |= ch << ((w) << 1);                                                                    \
    }
#define OMEC(w, pw) omTabF[omCk(C##w - P##pw)]
bool omDPS3(int t, int sc, int n, int i0) {
    omSteps += sc;
    int Q = (int)divideNonnegative(n, sc), R = n - (int)multiplyNonnegative(Q, sc);
    const ll HV = omHV;
    const ll GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const bool allowM = OAS > 0 && Q >= 2;
    const bool allowP = OAS > 0;
    const ll BIG = (ll)1 << 61;
    const ll penM = allowM ? 0 : BIG;
    const ll penP = allowP ? 0 : BIG;
    omTabFor(t);
    const int tq = omTq;
    const int t4 = t << 2;
    ll hval[4];
    hval[0] = 0;
    hval[1] = HV;
    hval[2] = -GV;
    hval[3] = OMNEG;
    ll V0 = OMNEG, V1 = OMNEG, V2 = OMNEG, V3, V4 = OMNEG, V5 = OMNEG, V6 = OMNEG;
    int P0 = omFr[i0] + tq, P1 = P0, P2 = P0, P3 = P0, P4 = P0, P5 = P0, P6 = P0;
    {
        int r = omRec[i0];
        int c0 = (r & 1) ? 3 : (((r & ~3) == t4) ? 1 : (r & 2));
        V3 = hval[c0];
    }
    omChP.resize(sc);
    int baseU = i0, cj = 0, acc = 0;
    for (int j = 1; j < sc; j++) {
        baseU += Q;
        int cn = cj;
        acc += R;
        if (acc >= sc) {
            acc -= sc;
            cn++;
        }
        int pos = baseU + cn - 3, add = 0;
        if (pos >= n) {
            pos -= n;
            add = N;
            if (pos >= n) {
                pos -= n;
                add += N;
            }
        } else if (pos < 0) {
            pos += n;
            add = -N;
        }
        ll H0, H1, H2, H3, H4, H5, H6;
        int C0, C1, C2, C3, C4, C5, C6;
#define OMLD(w)                                                                                    \
    {                                                                                              \
        int r_ = omRec[pos];                                                                       \
        ll h_ = ((r_ & ~3) == t4) ? HV : ((r_ & 2) ? -GV : 0);                                     \
        H##w = (r_ & 1) ? OMNEG : h_;                                                              \
        C##w = omFr[pos] + add;                                                                    \
        pos++;                                                                                     \
        if (pos >= n) {                                                                            \
            pos -= n;                                                                              \
            add += N;                                                                              \
        }                                                                                          \
    }
        OMLD(0)
        OMLD(1) OMLD(2) OMLD(3) OMLD(4) OMLD(5) OMLD(6)
#undef OMLD
            ll N0,
            N1, N2, N3, N4, N5, N6;
        unsigned pk = 0;
        if (cn == cj) {
            {
                ll bv = V0 - OMEC(0, 0);
                unsigned ch = 1u;
                OMCAND(V1 - OMEC(0, 1) - penM, 0u) OMFIN(0)
            }
            {
                ll bv = V1 - OMEC(1, 1);
                unsigned ch = 1u;
                OMCAND(V0 - OMEC(1, 0), 2u) OMCAND(V2 - OMEC(1, 2) - penM, 0u) OMFIN(1)
            }
            {
                ll bv = V2 - OMEC(2, 2);
                unsigned ch = 1u;
                OMCAND(V1 - OMEC(2, 1), 2u)
                OMCAND(V3 - OMEC(2, 3) - penM, 0u) OMCAND(V0 - OMEC(2, 0) - penP, 3u) OMFIN(2)
            }
            {
                ll bv = V3 - OMEC(3, 3);
                unsigned ch = 1u;
                OMCAND(V2 - OMEC(3, 2), 2u)
                OMCAND(V4 - OMEC(3, 4) - penM, 0u) OMCAND(V1 - OMEC(3, 1) - penP, 3u) OMFIN(3)
            }
            {
                ll bv = V4 - OMEC(4, 4);
                unsigned ch = 1u;
                OMCAND(V3 - OMEC(4, 3), 2u)
                OMCAND(V5 - OMEC(4, 5) - penM, 0u) OMCAND(V2 - OMEC(4, 2) - penP, 3u) OMFIN(4)
            }
            {
                ll bv = V5 - OMEC(5, 5);
                unsigned ch = 1u;
                OMCAND(V4 - OMEC(5, 4), 2u)
                OMCAND(V6 - OMEC(5, 6) - penM, 0u) OMCAND(V3 - OMEC(5, 3) - penP, 3u) OMFIN(5)
            }
            {
                ll bv = V6 - OMEC(6, 6);
                unsigned ch = 1u;
                OMCAND(V5 - OMEC(6, 5), 2u) OMCAND(V4 - OMEC(6, 4) - penP, 3u) OMFIN(6)
            }
        } else {
            {
                ll bv = V1 - OMEC(0, 1);
                unsigned ch = 1u;
                OMCAND(V0 - OMEC(0, 0), 2u) OMCAND(V2 - OMEC(0, 2) - penM, 0u) OMFIN(0)
            }
            {
                ll bv = V2 - OMEC(1, 2);
                unsigned ch = 1u;
                OMCAND(V1 - OMEC(1, 1), 2u)
                OMCAND(V3 - OMEC(1, 3) - penM, 0u) OMCAND(V0 - OMEC(1, 0) - penP, 3u) OMFIN(1)
            }
            {
                ll bv = V3 - OMEC(2, 3);
                unsigned ch = 1u;
                OMCAND(V2 - OMEC(2, 2), 2u)
                OMCAND(V4 - OMEC(2, 4) - penM, 0u) OMCAND(V1 - OMEC(2, 1) - penP, 3u) OMFIN(2)
            }
            {
                ll bv = V4 - OMEC(3, 4);
                unsigned ch = 1u;
                OMCAND(V3 - OMEC(3, 3), 2u)
                OMCAND(V5 - OMEC(3, 5) - penM, 0u) OMCAND(V2 - OMEC(3, 2) - penP, 3u) OMFIN(3)
            }
            {
                ll bv = V5 - OMEC(4, 5);
                unsigned ch = 1u;
                OMCAND(V4 - OMEC(4, 4), 2u)
                OMCAND(V6 - OMEC(4, 6) - penM, 0u) OMCAND(V3 - OMEC(4, 3) - penP, 3u) OMFIN(4)
            }
            {
                ll bv = V6 - OMEC(5, 6);
                unsigned ch = 1u;
                OMCAND(V5 - OMEC(5, 5), 2u) OMCAND(V4 - OMEC(5, 4) - penP, 3u) OMFIN(5)
            }
            {
                ll bv = V6 - OMEC(6, 6);
                unsigned ch = 2u;
                OMCAND(V5 - OMEC(6, 5) - penP, 3u) OMFIN(6)
            }
        }
        ll mx = N0 > N1 ? N0 : N1;
        mx = N2 > mx ? N2 : mx;
        mx = N3 > mx ? N3 : mx;
        mx = N4 > mx ? N4 : mx;
        mx = N5 > mx ? N5 : mx;
        mx = N6 > mx ? N6 : mx;
        if (mx <= (OMNEG >> 1))
            return false;
        omChP[j] = pk;
        V0 = N0;
        V1 = N1;
        V2 = N2;
        V3 = N3;
        V4 = N4;
        V5 = N5;
        V6 = N6;
        P0 = C0 + tq;
        P1 = C1 + tq;
        P2 = C2 + tq;
        P3 = C3 + tq;
        P4 = C4 + tq;
        P5 = C5 + tq;
        P6 = C6 + tq;
        cj = cn;
    }
    ll VF[7] = {V0, V1, V2, V3, V4, V5, V6};
    int PF[7] = {P0, P1, P2, P3, P4, P5, P6};
    int bw = -1;
    ll bv = OMNEG >> 1;
    for (int w = 0; w < 7; w++) {
        ll v = VF[w];
        if (v <= (OMNEG >> 1))
            continue;
        int u = cj + w - 3;
        int bl = R - u;
        if (bl < (allowM ? -1 : 0) || bl > (allowP ? 2 : 1))
            continue;
        v -= omTabF[omCk(omFr[i0] + N - PF[w])];
        if (v > bv) {
            bv = v;
            bw = w;
        }
    }
    if (bw < 0)
        return false;
    omPos.resize(sc);
    int u = cj + bw - 3;
    int accb = acc, cc = cj;
    ll p = baseU + u;
    while (p >= n)
        p -= n;
    while (p < 0)
        p += n;
    for (int j = sc - 1; j >= 0; j--) {
        omPos[j] = (int)p;
        if (j == 0)
            break;
        int w = u - cc + 3;
        int bb = (int)((omChP[j] >> (w << 1)) & 3ULL) - 1;
        u -= bb;
        p -= Q + bb;
        if (p < 0)
            p += n;
        int prevAcc = accb - R;
        if (prevAcc < 0) {
            prevAcc += sc;
            cc--;
        }
        accb = prevAcc;
    }
    return true;
}
#undef OMCAND
#undef OMFIN
#undef OMEC
#define OMCAND(val, code)                                                                          \
    {                                                                                              \
        ll v_ = (val);                                                                             \
        ch = v_ > bv ? (code) : ch;                                                                \
        bv = v_ > bv ? v_ : bv;                                                                    \
    }
#define OMFIN(w)                                                                                   \
    {                                                                                              \
        ll nv_ = bv + H##w;                                                                        \
        nv_ = nv_ < OMNEG ? OMNEG : nv_;                                                           \
        N##w = nv_;                                                                                \
        pk |= (ull)ch << ((w) << 1);                                                               \
    }
unsigned char omCode8[MAXN + 16];
#define PRE true
template <bool PZ> bool omDPS4Z(int t, int sc, int n, int i0);
bool omDPS4(int t, int sc, int n, int i0) {
    {
        const int t4_ = t << 2;
        auto recD = omRec.data();
        for (int i = 0; i < n; i++) {
            const int r_ = recD[i];
            omCode8[i] = (unsigned char)((r_ & 1) ? 3 : (((r_ & ~3) == t4_) ? 1 : (r_ & 2)));
        }
    }
    if (OAS > 0 && (int)divideNonnegative(n, sc) >= 2)
        return omDPS4Z<true>(t, sc, n, i0);
    return omDPS4Z<false>(t, sc, n, i0);
}
template <bool PZ> bool omDPS4Z(int t, int sc, int n, int i0) {
    int Q = (int)divideNonnegative(n, sc), R = n - (int)multiplyNonnegative(Q, sc);
    const ll HV = omHV;
    const ll GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const bool allowM = OAS > 0 && Q >= 2;
    const bool allowP = OAS > 0;
    const ll BIG = (ll)1 << 61;
    const ll penM = (PZ || allowM) ? 0 : BIG;
    const ll penP = (PZ || allowP) ? 0 : BIG;
    omTabFor(t);
    const int tq = omTq;
    const int t4 = t << 2;
    ll hval[4];
    hval[0] = 0;
    hval[1] = HV;
    hval[2] = -GV;
    hval[3] = OMNEG;
    ll V0 = OMNEG, V1 = OMNEG, V2 = OMNEG, V3 = OMNEG, V4, V5 = OMNEG, V6 = OMNEG, V7 = OMNEG,
       V8 = OMNEG;
    int P0 = omFr[i0] + tq, P1 = P0, P2 = P0, P3 = P0, P4 = P0, P5 = P0, P6 = P0, P7 = P0, P8 = P0;
    {
        int r = omRec[i0];
        int c0 = (r & 1) ? 3 : (((r & ~3) == t4) ? 1 : (r & 2));
        V4 = hval[c0];
    }
    omChP.resize(sc);
    auto recD = omRec.data();
    auto frD = omFr.data();
    auto chD = omChP.data();
#define SPREC(k) recD[k]
#define SPFR(k) frD[k]
#define SPCH(k) chD[k]
    int baseU = i0, cj = 0, acc = 0;
    for (int j = 1; j < sc; j++) {
        baseU += Q;
        int cn = cj;
        acc += R;
        if (acc >= sc) {
            acc -= sc;
            cn++;
        }
        int pos = baseU + cn - 4, add = 0;
        while (pos >= n) {
            pos -= n;
            add += N;
        }
        while (pos < 0) {
            pos += n;
            add -= N;
        }
#if SP_OMC_ON
        ull cds = 0;
#define SPH(w, code) cds |= (ull)(code) << ((w) << 1)
#undef OMFIN
#define OMFIN(w)                                                                                   \
    {                                                                                              \
        ll nv_ = bv + hval[(cds >> ((w) << 1)) & 3];                                               \
        nv_ = nv_ < OMNEG ? OMNEG : nv_;                                                           \
        N##w = nv_;                                                                                \
        pk |= (ull)ch << ((w) << 1);                                                               \
    }
#else
        ll H0, H1, H2, H3, H4, H5, H6, H7, H8;
#define SPH(w, code) H##w = hval[code]
#endif
        int C0, C1, C2, C3, C4, C5, C6, C7, C8;
        if (pos + 8 < n) {
#define OMLDF(w)                                                                                   \
    {                                                                                              \
        int code_;                                                                                 \
        if (PRE)                                                                                   \
            code_ = omCode8[pos + w];                                                              \
        else {                                                                                     \
            int r_ = SPREC(pos + w);                                                               \
            code_ = (r_ & 1) ? 3 : (((r_ & ~3) == t4) ? 1 : (r_ & 2));                             \
        }                                                                                          \
        SPH(w, code_);                                                                             \
        C##w = SPFR(pos + w) + add;                                                                \
    }
            OMLDF(0) OMLDF(1) OMLDF(2) OMLDF(3) OMLDF(4) OMLDF(5) OMLDF(6) OMLDF(7) OMLDF(8)
#undef OMLDF
        } else {
#define OMLD(w)                                                                                    \
    {                                                                                              \
        int code_;                                                                                 \
        if (PRE)                                                                                   \
            code_ = omCode8[pos];                                                                  \
        else {                                                                                     \
            int r_ = SPREC(pos);                                                                   \
            code_ = (r_ & 1) ? 3 : (((r_ & ~3) == t4) ? 1 : (r_ & 2));                             \
        }                                                                                          \
        SPH(w, code_);                                                                             \
        C##w = SPFR(pos) + add;                                                                    \
        pos++;                                                                                     \
        if (pos >= n) {                                                                            \
            pos -= n;                                                                              \
            add += N;                                                                              \
        }                                                                                          \
    }
            OMLD(0) OMLD(1) OMLD(2) OMLD(3) OMLD(4) OMLD(5) OMLD(6) OMLD(7) OMLD(8)
#undef OMLD
        }
        ll N0, N1, N2, N3, N4, N5, N6, N7, N8;
        ull pk = 0;
        const int kmin = C0 - P8, kmax = C8 - P0;
        if (kmin >= 0 && kmax <= 128) {
            if (cn == cj) {
                {
                    ll bv = V0 - omTabF[C0 - P0];
                    unsigned ch = 1u;
                    OMCAND(V1 - omTabF[C0 - P1] - penM, 0u) OMFIN(0)
                }
                {
                    ll bv = V1 - omTabF[C1 - P1];
                    unsigned ch = 1u;
                    OMCAND(V0 - omTabF[C1 - P0], 2u)
                    OMCAND(V2 - omTabF[C1 - P2] - penM, 0u) OMFIN(1)
                }
                {
                    ll bv = V2 - omTabF[C2 - P2];
                    unsigned ch = 1u;
                    OMCAND(V1 - omTabF[C2 - P1], 2u)
                    OMCAND(V3 - omTabF[C2 - P3] - penM, 0u) OMCAND(V0 - omTabF[C2 - P0] - penP, 3u)
                        OMFIN(2)
                }
                {
                    ll bv = V3 - omTabF[C3 - P3];
                    unsigned ch = 1u;
                    OMCAND(V2 - omTabF[C3 - P2], 2u)
                    OMCAND(V4 - omTabF[C3 - P4] - penM, 0u) OMCAND(V1 - omTabF[C3 - P1] - penP, 3u)
                        OMFIN(3)
                }
                {
                    ll bv = V4 - omTabF[C4 - P4];
                    unsigned ch = 1u;
                    OMCAND(V3 - omTabF[C4 - P3], 2u)
                    OMCAND(V5 - omTabF[C4 - P5] - penM, 0u) OMCAND(V2 - omTabF[C4 - P2] - penP, 3u)
                        OMFIN(4)
                }
                {
                    ll bv = V5 - omTabF[C5 - P5];
                    unsigned ch = 1u;
                    OMCAND(V4 - omTabF[C5 - P4], 2u)
                    OMCAND(V6 - omTabF[C5 - P6] - penM, 0u) OMCAND(V3 - omTabF[C5 - P3] - penP, 3u)
                        OMFIN(5)
                }
                {
                    ll bv = V6 - omTabF[C6 - P6];
                    unsigned ch = 1u;
                    OMCAND(V5 - omTabF[C6 - P5], 2u)
                    OMCAND(V7 - omTabF[C6 - P7] - penM, 0u) OMCAND(V4 - omTabF[C6 - P4] - penP, 3u)
                        OMFIN(6)
                }
                {
                    ll bv = V7 - omTabF[C7 - P7];
                    unsigned ch = 1u;
                    OMCAND(V6 - omTabF[C7 - P6], 2u)
                    OMCAND(V8 - omTabF[C7 - P8] - penM, 0u) OMCAND(V5 - omTabF[C7 - P5] - penP, 3u)
                        OMFIN(7)
                }
                {
                    ll bv = V8 - omTabF[C8 - P8];
                    unsigned ch = 1u;
                    OMCAND(V7 - omTabF[C8 - P7], 2u)
                    OMCAND(V6 - omTabF[C8 - P6] - penP, 3u) OMFIN(8)
                }
            } else {
                {
                    ll bv = V1 - omTabF[C0 - P1];
                    unsigned ch = 1u;
                    OMCAND(V0 - omTabF[C0 - P0], 2u)
                    OMCAND(V2 - omTabF[C0 - P2] - penM, 0u) OMFIN(0)
                }
                {
                    ll bv = V2 - omTabF[C1 - P2];
                    unsigned ch = 1u;
                    OMCAND(V1 - omTabF[C1 - P1], 2u)
                    OMCAND(V3 - omTabF[C1 - P3] - penM, 0u) OMCAND(V0 - omTabF[C1 - P0] - penP, 3u)
                        OMFIN(1)
                }
                {
                    ll bv = V3 - omTabF[C2 - P3];
                    unsigned ch = 1u;
                    OMCAND(V2 - omTabF[C2 - P2], 2u)
                    OMCAND(V4 - omTabF[C2 - P4] - penM, 0u) OMCAND(V1 - omTabF[C2 - P1] - penP, 3u)
                        OMFIN(2)
                }
                {
                    ll bv = V4 - omTabF[C3 - P4];
                    unsigned ch = 1u;
                    OMCAND(V3 - omTabF[C3 - P3], 2u)
                    OMCAND(V5 - omTabF[C3 - P5] - penM, 0u) OMCAND(V2 - omTabF[C3 - P2] - penP, 3u)
                        OMFIN(3)
                }
                {
                    ll bv = V5 - omTabF[C4 - P5];
                    unsigned ch = 1u;
                    OMCAND(V4 - omTabF[C4 - P4], 2u)
                    OMCAND(V6 - omTabF[C4 - P6] - penM, 0u) OMCAND(V3 - omTabF[C4 - P3] - penP, 3u)
                        OMFIN(4)
                }
                {
                    ll bv = V6 - omTabF[C5 - P6];
                    unsigned ch = 1u;
                    OMCAND(V5 - omTabF[C5 - P5], 2u)
                    OMCAND(V7 - omTabF[C5 - P7] - penM, 0u) OMCAND(V4 - omTabF[C5 - P4] - penP, 3u)
                        OMFIN(5)
                }
                {
                    ll bv = V7 - omTabF[C6 - P7];
                    unsigned ch = 1u;
                    OMCAND(V6 - omTabF[C6 - P6], 2u)
                    OMCAND(V8 - omTabF[C6 - P8] - penM, 0u) OMCAND(V5 - omTabF[C6 - P5] - penP, 3u)
                        OMFIN(6)
                }
                {
                    ll bv = V8 - omTabF[C7 - P8];
                    unsigned ch = 1u;
                    OMCAND(V7 - omTabF[C7 - P7], 2u)
                    OMCAND(V6 - omTabF[C7 - P6] - penP, 3u) OMFIN(7)
                }
                {
                    ll bv = V8 - omTabF[C8 - P8];
                    unsigned ch = 2u;
                    OMCAND(V7 - omTabF[C8 - P7] - penP, 3u) OMFIN(8)
                }
            }
        } else if (kmin >= -SXOFF && kmax <= 128 + SXOFF) {
            if (omTabXSer != omTabSer) {
                omTabXSer = omTabSer;
                const ll lo = omTabF[0], hi = omTabF[128];
                for (int k = 0; k < SXOFF; k++) {
                    omTabX[k] = lo;
                    omTabX[SXOFF + 129 + k] = hi;
                }
                for (int k = 0; k <= 128; k++)
                    omTabX[SXOFF + k] = omTabF[k];
            }
            C0 += SXOFF;
            C1 += SXOFF;
            C2 += SXOFF;
            C3 += SXOFF;
            C4 += SXOFF;
            C5 += SXOFF;
            C6 += SXOFF;
            C7 += SXOFF;
            C8 += SXOFF;
            if (cn == cj) {
                {
                    ll bv = V0 - omTabX[C0 - P0];
                    unsigned ch = 1u;
                    OMCAND(V1 - omTabX[C0 - P1] - penM, 0u) OMFIN(0)
                }
                {
                    ll bv = V1 - omTabX[C1 - P1];
                    unsigned ch = 1u;
                    OMCAND(V0 - omTabX[C1 - P0], 2u)
                    OMCAND(V2 - omTabX[C1 - P2] - penM, 0u) OMFIN(1)
                }
                {
                    ll bv = V2 - omTabX[C2 - P2];
                    unsigned ch = 1u;
                    OMCAND(V1 - omTabX[C2 - P1], 2u)
                    OMCAND(V3 - omTabX[C2 - P3] - penM, 0u) OMCAND(V0 - omTabX[C2 - P0] - penP, 3u)
                        OMFIN(2)
                }
                {
                    ll bv = V3 - omTabX[C3 - P3];
                    unsigned ch = 1u;
                    OMCAND(V2 - omTabX[C3 - P2], 2u)
                    OMCAND(V4 - omTabX[C3 - P4] - penM, 0u) OMCAND(V1 - omTabX[C3 - P1] - penP, 3u)
                        OMFIN(3)
                }
                {
                    ll bv = V4 - omTabX[C4 - P4];
                    unsigned ch = 1u;
                    OMCAND(V3 - omTabX[C4 - P3], 2u)
                    OMCAND(V5 - omTabX[C4 - P5] - penM, 0u) OMCAND(V2 - omTabX[C4 - P2] - penP, 3u)
                        OMFIN(4)
                }
                {
                    ll bv = V5 - omTabX[C5 - P5];
                    unsigned ch = 1u;
                    OMCAND(V4 - omTabX[C5 - P4], 2u)
                    OMCAND(V6 - omTabX[C5 - P6] - penM, 0u) OMCAND(V3 - omTabX[C5 - P3] - penP, 3u)
                        OMFIN(5)
                }
                {
                    ll bv = V6 - omTabX[C6 - P6];
                    unsigned ch = 1u;
                    OMCAND(V5 - omTabX[C6 - P5], 2u)
                    OMCAND(V7 - omTabX[C6 - P7] - penM, 0u) OMCAND(V4 - omTabX[C6 - P4] - penP, 3u)
                        OMFIN(6)
                }
                {
                    ll bv = V7 - omTabX[C7 - P7];
                    unsigned ch = 1u;
                    OMCAND(V6 - omTabX[C7 - P6], 2u)
                    OMCAND(V8 - omTabX[C7 - P8] - penM, 0u) OMCAND(V5 - omTabX[C7 - P5] - penP, 3u)
                        OMFIN(7)
                }
                {
                    ll bv = V8 - omTabX[C8 - P8];
                    unsigned ch = 1u;
                    OMCAND(V7 - omTabX[C8 - P7], 2u)
                    OMCAND(V6 - omTabX[C8 - P6] - penP, 3u) OMFIN(8)
                }
            } else {
                {
                    ll bv = V1 - omTabX[C0 - P1];
                    unsigned ch = 1u;
                    OMCAND(V0 - omTabX[C0 - P0], 2u)
                    OMCAND(V2 - omTabX[C0 - P2] - penM, 0u) OMFIN(0)
                }
                {
                    ll bv = V2 - omTabX[C1 - P2];
                    unsigned ch = 1u;
                    OMCAND(V1 - omTabX[C1 - P1], 2u)
                    OMCAND(V3 - omTabX[C1 - P3] - penM, 0u) OMCAND(V0 - omTabX[C1 - P0] - penP, 3u)
                        OMFIN(1)
                }
                {
                    ll bv = V3 - omTabX[C2 - P3];
                    unsigned ch = 1u;
                    OMCAND(V2 - omTabX[C2 - P2], 2u)
                    OMCAND(V4 - omTabX[C2 - P4] - penM, 0u) OMCAND(V1 - omTabX[C2 - P1] - penP, 3u)
                        OMFIN(2)
                }
                {
                    ll bv = V4 - omTabX[C3 - P4];
                    unsigned ch = 1u;
                    OMCAND(V3 - omTabX[C3 - P3], 2u)
                    OMCAND(V5 - omTabX[C3 - P5] - penM, 0u) OMCAND(V2 - omTabX[C3 - P2] - penP, 3u)
                        OMFIN(3)
                }
                {
                    ll bv = V5 - omTabX[C4 - P5];
                    unsigned ch = 1u;
                    OMCAND(V4 - omTabX[C4 - P4], 2u)
                    OMCAND(V6 - omTabX[C4 - P6] - penM, 0u) OMCAND(V3 - omTabX[C4 - P3] - penP, 3u)
                        OMFIN(4)
                }
                {
                    ll bv = V6 - omTabX[C5 - P6];
                    unsigned ch = 1u;
                    OMCAND(V5 - omTabX[C5 - P5], 2u)
                    OMCAND(V7 - omTabX[C5 - P7] - penM, 0u) OMCAND(V4 - omTabX[C5 - P4] - penP, 3u)
                        OMFIN(5)
                }
                {
                    ll bv = V7 - omTabX[C6 - P7];
                    unsigned ch = 1u;
                    OMCAND(V6 - omTabX[C6 - P6], 2u)
                    OMCAND(V8 - omTabX[C6 - P8] - penM, 0u) OMCAND(V5 - omTabX[C6 - P5] - penP, 3u)
                        OMFIN(6)
                }
                {
                    ll bv = V8 - omTabX[C7 - P8];
                    unsigned ch = 1u;
                    OMCAND(V7 - omTabX[C7 - P7], 2u)
                    OMCAND(V6 - omTabX[C7 - P6] - penP, 3u) OMFIN(7)
                }
                {
                    ll bv = V8 - omTabX[C8 - P8];
                    unsigned ch = 2u;
                    OMCAND(V7 - omTabX[C8 - P7] - penP, 3u) OMFIN(8)
                }
            }
            C0 -= SXOFF;
            C1 -= SXOFF;
            C2 -= SXOFF;
            C3 -= SXOFF;
            C4 -= SXOFF;
            C5 -= SXOFF;
            C6 -= SXOFF;
            C7 -= SXOFF;
            C8 -= SXOFF;
        } else if (cn == cj) {
            {
                ll bv = V0 - omTabF[omCk(C0 - P0)];
                unsigned ch = 1u;
                OMCAND(V1 - omTabF[omCk(C0 - P1)] - penM, 0u) OMFIN(0)
            }
            {
                ll bv = V1 - omTabF[omCk(C1 - P1)];
                unsigned ch = 1u;
                OMCAND(V0 - omTabF[omCk(C1 - P0)], 2u)
                OMCAND(V2 - omTabF[omCk(C1 - P2)] - penM, 0u) OMFIN(1)
            }
            {
                ll bv = V2 - omTabF[omCk(C2 - P2)];
                unsigned ch = 1u;
                OMCAND(V1 - omTabF[omCk(C2 - P1)], 2u)
                OMCAND(V3 - omTabF[omCk(C2 - P3)] - penM, 0u)
                    OMCAND(V0 - omTabF[omCk(C2 - P0)] - penP, 3u) OMFIN(2)
            }
            {
                ll bv = V3 - omTabF[omCk(C3 - P3)];
                unsigned ch = 1u;
                OMCAND(V2 - omTabF[omCk(C3 - P2)], 2u)
                OMCAND(V4 - omTabF[omCk(C3 - P4)] - penM, 0u)
                    OMCAND(V1 - omTabF[omCk(C3 - P1)] - penP, 3u) OMFIN(3)
            }
            {
                ll bv = V4 - omTabF[omCk(C4 - P4)];
                unsigned ch = 1u;
                OMCAND(V3 - omTabF[omCk(C4 - P3)], 2u)
                OMCAND(V5 - omTabF[omCk(C4 - P5)] - penM, 0u)
                    OMCAND(V2 - omTabF[omCk(C4 - P2)] - penP, 3u) OMFIN(4)
            }
            {
                ll bv = V5 - omTabF[omCk(C5 - P5)];
                unsigned ch = 1u;
                OMCAND(V4 - omTabF[omCk(C5 - P4)], 2u)
                OMCAND(V6 - omTabF[omCk(C5 - P6)] - penM, 0u)
                    OMCAND(V3 - omTabF[omCk(C5 - P3)] - penP, 3u) OMFIN(5)
            }
            {
                ll bv = V6 - omTabF[omCk(C6 - P6)];
                unsigned ch = 1u;
                OMCAND(V5 - omTabF[omCk(C6 - P5)], 2u)
                OMCAND(V7 - omTabF[omCk(C6 - P7)] - penM, 0u)
                    OMCAND(V4 - omTabF[omCk(C6 - P4)] - penP, 3u) OMFIN(6)
            }
            {
                ll bv = V7 - omTabF[omCk(C7 - P7)];
                unsigned ch = 1u;
                OMCAND(V6 - omTabF[omCk(C7 - P6)], 2u)
                OMCAND(V8 - omTabF[omCk(C7 - P8)] - penM, 0u)
                    OMCAND(V5 - omTabF[omCk(C7 - P5)] - penP, 3u) OMFIN(7)
            }
            {
                ll bv = V8 - omTabF[omCk(C8 - P8)];
                unsigned ch = 1u;
                OMCAND(V7 - omTabF[omCk(C8 - P7)], 2u)
                OMCAND(V6 - omTabF[omCk(C8 - P6)] - penP, 3u) OMFIN(8)
            }
        } else {
            {
                ll bv = V1 - omTabF[omCk(C0 - P1)];
                unsigned ch = 1u;
                OMCAND(V0 - omTabF[omCk(C0 - P0)], 2u)
                OMCAND(V2 - omTabF[omCk(C0 - P2)] - penM, 0u) OMFIN(0)
            }
            {
                ll bv = V2 - omTabF[omCk(C1 - P2)];
                unsigned ch = 1u;
                OMCAND(V1 - omTabF[omCk(C1 - P1)], 2u)
                OMCAND(V3 - omTabF[omCk(C1 - P3)] - penM, 0u)
                    OMCAND(V0 - omTabF[omCk(C1 - P0)] - penP, 3u) OMFIN(1)
            }
            {
                ll bv = V3 - omTabF[omCk(C2 - P3)];
                unsigned ch = 1u;
                OMCAND(V2 - omTabF[omCk(C2 - P2)], 2u)
                OMCAND(V4 - omTabF[omCk(C2 - P4)] - penM, 0u)
                    OMCAND(V1 - omTabF[omCk(C2 - P1)] - penP, 3u) OMFIN(2)
            }
            {
                ll bv = V4 - omTabF[omCk(C3 - P4)];
                unsigned ch = 1u;
                OMCAND(V3 - omTabF[omCk(C3 - P3)], 2u)
                OMCAND(V5 - omTabF[omCk(C3 - P5)] - penM, 0u)
                    OMCAND(V2 - omTabF[omCk(C3 - P2)] - penP, 3u) OMFIN(3)
            }
            {
                ll bv = V5 - omTabF[omCk(C4 - P5)];
                unsigned ch = 1u;
                OMCAND(V4 - omTabF[omCk(C4 - P4)], 2u)
                OMCAND(V6 - omTabF[omCk(C4 - P6)] - penM, 0u)
                    OMCAND(V3 - omTabF[omCk(C4 - P3)] - penP, 3u) OMFIN(4)
            }
            {
                ll bv = V6 - omTabF[omCk(C5 - P6)];
                unsigned ch = 1u;
                OMCAND(V5 - omTabF[omCk(C5 - P5)], 2u)
                OMCAND(V7 - omTabF[omCk(C5 - P7)] - penM, 0u)
                    OMCAND(V4 - omTabF[omCk(C5 - P4)] - penP, 3u) OMFIN(5)
            }
            {
                ll bv = V7 - omTabF[omCk(C6 - P7)];
                unsigned ch = 1u;
                OMCAND(V6 - omTabF[omCk(C6 - P6)], 2u)
                OMCAND(V8 - omTabF[omCk(C6 - P8)] - penM, 0u)
                    OMCAND(V5 - omTabF[omCk(C6 - P5)] - penP, 3u) OMFIN(6)
            }
            {
                ll bv = V8 - omTabF[omCk(C7 - P8)];
                unsigned ch = 1u;
                OMCAND(V7 - omTabF[omCk(C7 - P7)], 2u)
                OMCAND(V6 - omTabF[omCk(C7 - P6)] - penP, 3u) OMFIN(7)
            }
            {
                ll bv = V8 - omTabF[omCk(C8 - P8)];
                unsigned ch = 2u;
                OMCAND(V7 - omTabF[omCk(C8 - P7)] - penP, 3u) OMFIN(8)
            }
        }
        SPCH(j) = pk;
        V0 = N0;
        V1 = N1;
        V2 = N2;
        V3 = N3;
        V4 = N4;
        V5 = N5;
        V6 = N6;
        V7 = N7;
        V8 = N8;
        P0 = C0 + tq;
        P1 = C1 + tq;
        P2 = C2 + tq;
        P3 = C3 + tq;
        P4 = C4 + tq;
        P5 = C5 + tq;
        P6 = C6 + tq;
        P7 = C7 + tq;
        P8 = C8 + tq;
        cj = cn;
    }
    ll VF[9] = {V0, V1, V2, V3, V4, V5, V6, V7, V8};
    int PF[9] = {P0, P1, P2, P3, P4, P5, P6, P7, P8};
    int bw = -1;
    ll bv = OMNEG >> 1;
    for (int w = 0; w < 9; w++) {
        ll v = VF[w];
        if (v <= (OMNEG >> 1))
            continue;
        int u = cj + w - 4;
        int bl = R - u;
        if (bl < (allowM ? -1 : 0) || bl > (allowP ? 2 : 1))
            continue;
        v -= omTabF[omCk(omFr[i0] + N - PF[w])];
        if (v > bv) {
            bv = v;
            bw = w;
        }
    }
    if (bw < 0)
        return false;
    omPos.resize(sc);
    int u = cj + bw - 4;
    int accb = acc, cc = cj;
    ll p = baseU + u;
    while (p >= n)
        p -= n;
    while (p < 0)
        p += n;
    for (int j = sc - 1; j >= 0; j--) {
        omPos[j] = (int)p;
        if (j == 0)
            break;
        int w = u - cc + 4;
        int bb = (int)((omChP[j] >> (w << 1)) & 3ULL) - 1;
        u -= bb;
        p -= Q + bb;
        if (p < 0)
            p += n;
        int prevAcc = accb - R;
        if (prevAcc < 0) {
            prevAcc += sc;
            cc--;
        }
        accb = prevAcc;
    }
    return true;
}
#undef SPREC
#undef SPFR
#undef SPCH
#undef SPH
#undef OMCAND
#undef OMFIN
#undef PRE
#define OMCANDD(val, code)                                                                         \
    {                                                                                              \
        ll v_ = (val);                                                                             \
        ch = v_ > bv ? (code) : ch;                                                                \
        bv = v_ > bv ? v_ : bv;                                                                    \
    }
#define OMFIND(w)                                                                                  \
    {                                                                                              \
        ll nv_ = bv + H##w;                                                                        \
        nv_ = nv_ < OMNEG ? OMNEG : nv_;                                                           \
        N##w = nv_;                                                                                \
        pk |= ch << ((w) << 1);                                                                    \
    }
bool omDPD2(int t, int sc, int n, int i0) {
    omSteps += sc >> 2;
    int Q = (int)divideNonnegative(n, sc), R = n - (int)multiplyNonnegative(Q, sc);
    ll devU = divideNonnegative(multiplyNonnegative(multiplyNonnegative(F[t], (ll)sc << 1), N), n);
    const ll HV = omHV;
    const ll GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const bool allowM = OA > 0 && Q >= 2;
    const bool allowP = OA > 0;
    const ll pen1 = R == 0 ? devU : 0;
    const ll BIG = (ll)1 << 61;
    const ll penM = allowM ? devU : BIG;
    const ll penP = allowP ? devU : BIG;
    ll hval[4];
    hval[0] = 0;
    hval[1] = HV;
    hval[2] = -GV;
    hval[3] = OMNEG;
    ll V0 = OMNEG, V1 = OMNEG, V2 = hval[omHitS[i0]], V3 = OMNEG, V4 = OMNEG;
    omChP.resize(sc);
    int baseU = i0, cj = 0, acc = 0;
    for (int j = 1; j < sc; j++) {
        baseU += Q;
        int cn = cj;
        acc += R;
        if (acc >= sc) {
            acc -= sc;
            cn++;
        }
        int pos = baseU + cn - 2;
        if (pos >= n) {
            pos -= n;
            if (pos >= n)
                pos -= n;
        } else if (pos < 0)
            pos += n;
        ll H0, H1, H2, H3, H4;
        if (pos + 4 < n) {
            H0 = hval[omHitS[pos]];
            H1 = hval[omHitS[pos + 1]];
            H2 = hval[omHitS[pos + 2]];
            H3 = hval[omHitS[pos + 3]];
            H4 = hval[omHitS[pos + 4]];
        } else {
#define OMLDD(w)                                                                                   \
    {                                                                                              \
        H##w = hval[omHitS[pos]];                                                                  \
        pos++;                                                                                     \
        if (pos >= n)                                                                              \
            pos -= n;                                                                              \
    }
            OMLDD(0) OMLDD(1) OMLDD(2) OMLDD(3) OMLDD(4)
#undef OMLDD
        }
        ll N0, N1, N2, N3, N4;
        unsigned pk = 0;
        if (cn == cj) {
            {
                ll bv = V0;
                unsigned ch = 1;
                OMCANDD(V1 - penM, 0u) OMFIND(0)
            }
            {
                ll bv = V1;
                unsigned ch = 1;
                OMCANDD(V0 - pen1, 2u) OMCANDD(V2 - penM, 0u) OMFIND(1)
            }
            {
                ll bv = V2;
                unsigned ch = 1;
                OMCANDD(V1 - pen1, 2u) OMCANDD(V3 - penM, 0u) OMCANDD(V0 - penP, 3u) OMFIND(2)
            }
            {
                ll bv = V3;
                unsigned ch = 1;
                OMCANDD(V2 - pen1, 2u) OMCANDD(V4 - penM, 0u) OMCANDD(V1 - penP, 3u) OMFIND(3)
            }
            {
                ll bv = V4;
                unsigned ch = 1;
                OMCANDD(V3 - pen1, 2u) OMCANDD(V2 - penP, 3u) OMFIND(4)
            }
        } else {
            {
                ll bv = V1;
                unsigned ch = 1;
                OMCANDD(V0 - pen1, 2u) OMCANDD(V2 - penM, 0u) OMFIND(0)
            }
            {
                ll bv = V2;
                unsigned ch = 1;
                OMCANDD(V1 - pen1, 2u) OMCANDD(V3 - penM, 0u) OMCANDD(V0 - penP, 3u) OMFIND(1)
            }
            {
                ll bv = V3;
                unsigned ch = 1;
                OMCANDD(V2 - pen1, 2u) OMCANDD(V4 - penM, 0u) OMCANDD(V1 - penP, 3u) OMFIND(2)
            }
            {
                ll bv = V4;
                unsigned ch = 1;
                OMCANDD(V3 - pen1, 2u) OMCANDD(V2 - penP, 3u) OMFIND(3)
            }
            {
                ll bv = V4 - pen1;
                unsigned ch = 2;
                OMCANDD(V3 - penP, 3u) OMFIND(4)
            }
        }
        omChP[j] = pk;
        V0 = N0;
        V1 = N1;
        V2 = N2;
        V3 = N3;
        V4 = N4;
        cj = cn;
    }
    int bw = -1;
    ll bv = OMNEG >> 1;
    for (int w = 0; w < 5; w++) {
        ll v = w == 0 ? V0 : (w == 1 ? V1 : (w == 2 ? V2 : (w == 3 ? V3 : V4)));
        if (v <= (OMNEG >> 1))
            continue;
        int u = cj + w - 2;
        int bl = R - u;
        if (bl < (allowM ? -1 : 0) || bl > (allowP ? 2 : 1))
            continue;
        if (bl == -1 || bl == 2)
            v -= devU;
        else if (bl == 1)
            v -= pen1;
        if (v > bv) {
            bv = v;
            bw = w;
        }
    }
    if (bw < 0)
        return false;
    omPos.resize(sc);
    int u = cj + bw - 2;
    int accb = acc, cc = cj;
    ll p = baseU + u;
    while (p >= n)
        p -= n;
    while (p < 0)
        p += n;
    for (int j = sc - 1; j >= 0; j--) {
        omPos[j] = (int)p;
        if (j == 0)
            break;
        int w = u - cc + 2;
        int bb = (int)((omChP[j] >> (w << 1)) & 3ULL) - 1;
        u -= bb;
        p -= Q + bb;
        if (p < 0)
            p += n;
        int prevAcc = accb - R;
        if (prevAcc < 0) {
            prevAcc += sc;
            cc--;
        }
        accb = prevAcc;
    }
    return true;
}
#undef OMCANDD
#undef OMFIND
#define OMCANDD1(val, code)                                                                        \
    {                                                                                              \
        ll v_ = (val);                                                                             \
        ch = v_ > bv ? (code) : ch;                                                                \
        bv = v_ > bv ? v_ : bv;                                                                    \
    }
#define OMFIND1(w)                                                                                 \
    {                                                                                              \
        ll nv_ = bv + H##w;                                                                        \
        nv_ = nv_ < OMNEG ? OMNEG : nv_;                                                           \
        N##w = nv_;                                                                                \
        pk |= ch << ((w) << 1);                                                                    \
    }
bool omDPD1(int t, int sc, int n, int i0) {
    int Q = (int)divideNonnegative(n, sc), R = n - (int)multiplyNonnegative(Q, sc);
    ll devU = divideNonnegative(multiplyNonnegative(multiplyNonnegative(F[t], (ll)sc << 1), N), n);
    const ll HV = omHV;
    const ll GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const bool allowM = OA > 0 && Q >= 2;
    const bool allowP = OA > 0;
    const ll pen1 = R == 0 ? devU : 0;
    const ll BIG = (ll)1 << 61;
    const ll penM = allowM ? devU : BIG;
    const ll penP = allowP ? devU : BIG;
    ll hval[4];
    hval[0] = 0;
    hval[1] = HV;
    hval[2] = -GV;
    hval[3] = OMNEG;
    ll V0 = OMNEG, V1 = hval[omHitS[i0]], V2 = OMNEG;
    omChP.resize(sc);
    int baseU = i0, cj = 0, acc = 0;
    for (int j = 1; j < sc; j++) {
        baseU += Q;
        int cn = cj;
        acc += R;
        if (acc >= sc) {
            acc -= sc;
            cn++;
        }
        int pos = baseU + cn - 1;
        if (pos >= n) {
            pos -= n;
            if (pos >= n)
                pos -= n;
        } else if (pos < 0)
            pos += n;
        ll H0, H1, H2;
#define OMLD1(w)                                                                                   \
    {                                                                                              \
        H##w = hval[omHitS[pos]];                                                                  \
        pos++;                                                                                     \
        if (pos >= n)                                                                              \
            pos -= n;                                                                              \
    }
        OMLD1(0)
        OMLD1(1) OMLD1(2)
#undef OMLD1
            ll N0,
            N1, N2;
        unsigned pk = 0;
        if (cn == cj) {
            {
                ll bv = V0;
                unsigned ch = 1;
                OMCANDD1(V1 - penM, 0u) OMFIND1(0)
            }
            {
                ll bv = V1;
                unsigned ch = 1;
                OMCANDD1(V0 - pen1, 2u) OMCANDD1(V2 - penM, 0u) OMFIND1(1)
            }
            {
                ll bv = V2;
                unsigned ch = 1;
                OMCANDD1(V1 - pen1, 2u) OMCANDD1(V0 - penP, 3u) OMFIND1(2)
            }
        } else {
            {
                ll bv = V1;
                unsigned ch = 1;
                OMCANDD1(V0 - pen1, 2u) OMCANDD1(V2 - penM, 0u) OMFIND1(0)
            }
            {
                ll bv = V2;
                unsigned ch = 1;
                OMCANDD1(V1 - pen1, 2u) OMCANDD1(V0 - penP, 3u) OMFIND1(1)
            }
            {
                ll bv = OMNEG;
                unsigned ch = 1;
                OMCANDD1(V2 - pen1, 2u) OMCANDD1(V1 - penP, 3u) OMFIND1(2)
            }
        }
        ll mx = N0 > N1 ? N0 : N1;
        mx = N2 > mx ? N2 : mx;
        if (mx <= (OMNEG >> 1))
            return false;
        omChP[j] = pk;
        V0 = N0;
        V1 = N1;
        V2 = N2;
        cj = cn;
    }
    int bw = -1;
    ll bv = OMNEG >> 1;
    for (int w = 0; w < 3; w++) {
        ll v = w == 0 ? V0 : (w == 1 ? V1 : V2);
        if (v <= (OMNEG >> 1))
            continue;
        int u = cj + w - 1;
        int bl = R - u;
        if (bl < (allowM ? -1 : 0) || bl > (allowP ? 2 : 1))
            continue;
        if (bl == -1 || bl == 2)
            v -= devU;
        else if (bl == 1)
            v -= pen1;
        if (v > bv) {
            bv = v;
            bw = w;
        }
    }
    if (bw < 0)
        return false;
    omPos.resize(sc);
    int u = cj + bw - 1;
    int accb = acc, cc = cj;
    ll p = baseU + u;
    while (p >= n)
        p -= n;
    while (p < 0)
        p += n;
    for (int j = sc - 1; j >= 0; j--) {
        omPos[j] = (int)p;
        if (j == 0)
            break;
        int w = u - cc + 1;
        int bb = (int)((omChP[j] >> (w << 1)) & 3ULL) - 1;
        u -= bb;
        p -= Q + bb;
        if (p < 0)
            p += n;
        int prevAcc = accb - R;
        if (prevAcc < 0) {
            prevAcc += sc;
            cc--;
        }
        accb = prevAcc;
    }
    return true;
}
#undef OMCANDD1
#undef OMFIND1
void omBres(int sc, int n) {
    omPos.resize(sc);
    int acc = n >> 1, k = 0;
    for (int i = 0; i < n && k < sc; i++) {
        acc += sc;
        if (acc >= n) {
            acc -= n;
            omPos[k++] = i;
        }
    }
}
#define OMGUARD 0
void omLayerDense(int t, int sc, int n, int hits) {
    omPos.resize(sc);
    int Q = (int)divideNonnegative(n, sc);
    int firstHit = -1, i0 = -1;
    if (hits > 0) {
        int prevH = -1;
        for (int i = 0; i < n; i++) {
            if (omHitS[i] != 1)
                continue;
            if (firstHit < 0)
                firstHit = i;
            if (prevH >= 0) {
                int g = i - prevH;
                if (g == Q || g == Q + 1) {
                    i0 = prevH;
                    break;
                }
            }
            prevH = i;
        }
    }
    if (hits == 0 || sc == 1) {
        if (sc == 1 && hits > 0) {
            omPos[0] = firstHit;
            return;
        }
        omBres(sc, n);
        return;
    }
    if (i0 < 0)
        i0 = firstHit;
    bool ok;
    int ddd = pDDD;
    if (OMGUARD)
        while (ddd > 1 && n + Q < ddd)
            ddd--;
    switch (ddd) {
    case 1:
        ok = BLF ? omDPD1(t, sc, n, i0) : omDP<1, false, false>(t, sc, n, i0);
        break;
    case 3:
        ok = omDP<3, false, false>(t, sc, n, i0);
        break;
    case 4:
        ok = omDP<4, false, false>(t, sc, n, i0);
        break;
    case 5:
        ok = omDP<5, false, false>(t, sc, n, i0);
        break;
    case 6:
        ok = omDP<6, false, false>(t, sc, n, i0);
        break;
    case 8:
        ok = omDP<8, false, false>(t, sc, n, i0);
        break;
    case 12:
        ok = omDP<12, false, false>(t, sc, n, i0);
        break;
    default:
        ok = omDPD2(t, sc, n, i0);
        break;
    }
    if (!ok)
        omBres(sc, n);
}
bool omLayerLazy(int t, int sc, int n) {
    int Q = (int)divideNonnegative(n, sc);
    int i0 = -1, firstHit = -1;
    int h = t ? typeHead[t] : (typeSize[0] > 0 ? nextVac(N - 1) : -1);
    if (h >= 0) {
        int cur = h, prevI = -1;
        for (int k = 0; k < sc; k++) {
            int ix = omIdx[cur];
            if (ix >= 0 && !(omRec[ix] & 1) && omPre[cur] == t) {
                if (firstHit < 0)
                    firstHit = ix;
                if (prevI >= 0) {
                    int g = ix - prevI;
                    if (g < 0)
                        g += n;
                    if (g == Q || g == Q + 1) {
                        i0 = prevI;
                        break;
                    }
                }
                prevI = ix;
            }
            cur = t ? nextSame[cur] : nextVac(cur);
            if (cur == h)
                break;
        }
    }
    if (i0 < 0)
        i0 = firstHit;
    if (i0 < 0) {
        int i = n >> 1;
        for (int k = 0; k < n; k++) {
            if (!(omRec[i] & 1)) {
                i0 = i;
                break;
            }
            i++;
            if (i >= n)
                i -= n;
        }
    }
    if (i0 < 0)
        return false;
    if (sc == 1) {
        omPos.resize(1);
        omPos[0] = i0;
        return true;
    }
    int dds = pDDS;
    if (OMGUARD)
        while (dds > 1 && n + Q < dds)
            dds--;
    switch (dds) {
    case 1:
        return omDPS<1>(t, sc, n, i0);
    case 3:
        return DPS3U ? omDPS3(t, sc, n, i0) : omDPS<3>(t, sc, n, i0);
    case 4:
        return omDPS4(t, sc, n, i0);
    case 5:
        return omDPS<5>(t, sc, n, i0);
    case 6:
        return omDPS<6>(t, sc, n, i0);
    case 7:
        return omDPS<7>(t, sc, n, i0);
    case 8:
        return omDPS<8>(t, sc, n, i0);
    case 12:
        return omDPS<12>(t, sc, n, i0);
    default:
        return omDPS2(t, sc, n, i0);
    }
}
SP2_I int omDM(int cell, int t) {
    if (!PREHIT)
        return slotType[cell] != t;
    int pre = changeStamp[cell] == operationStamp ? originalValue[cell] : publicGrid[cell];
    return (serviceId[t] != pre) - (publicGrid[cell] != pre);
}
void omTake(int t, int sc) {
    int k0 = 0;
    for (int k = 1; k < sc; k++)
        if (omPos[k] < omPos[k - 1]) {
            k0 = k;
            break;
        }
    omTabFor(t);
    ll sd = 0;
    int fc = -1, lc = -1;
    int kp = k0;
    const int o = operationStamp, tt = serviceId[t];
    int dm = 0;
    for (int k = 0; k < sc; k++) {
        int cell = omFr[omPos[kp]];
        kp++;
        if (kp >= sc)
            kp = 0;
        rbNTa[cell] = t;
        omTk[cell] = omSer;
        int g = publicGrid[cell], pre = changeStamp[cell] == o ? originalValue[cell] : g;
        dm += (tt != pre) - (g != pre);
        if (lc >= 0)
            sd += omCstF(t, cell - lc);
        else
            fc = cell;
        lc = cell;
    }
    omM += dm;
    if (sc >= 2 && F[t] > 0) {
        sd += omCstF(t, fc + N - lc);
        omP += sd;
    } else
        sd = 0;
    rqDm[t] = dm;
    rqPn[t] = sd;
}
void omTakeRest(int t, int n, bool lazy) {
    omTabFor(t);
    ll sd = 0;
    int fc = -1, lc = -1;
    int dm = 0;
    for (int i = 0; i < n; i++) {
        if (lazy && (omRec[i] & 1))
            continue;
        int cell = omFr[i];
        rbNTa[cell] = t;
        dm += omDM(cell, t);
        if (lc >= 0)
            sd += omCstF(t, cell - lc);
        else
            fc = cell;
        lc = cell;
    }
    omM += dm;
    if (typeSize[t] >= 2 && F[t] > 0 && lc >= 0) {
        sd += omCstF(t, fc + N - lc);
        omP += sd;
    } else
        sd = 0;
    rqDm[t] = dm;
    rqPn[t] = sd;
}
#define RQ_KEEP 0
#define RQ_KL 16
ll omEval(int t, int sc, const RVEC(int) & pos, int &dmOut) {
    omTabFor(t);
    ll sd = 0;
    int fc = -1, lc = -1, dm = 0;
    const int o = operationStamp, tt = serviceId[t];
    for (int k = 0; k < sc; k++) {
        int cell = omFr[pos[k]];
        int g = publicGrid[cell], pre = changeStamp[cell] == o ? originalValue[cell] : g;
        dm += (tt != pre) - (g != pre);
        if (lc >= 0)
            sd += omCstF(t, cell - lc);
        else
            fc = cell;
        lc = cell;
    }
    if (sc >= 2 && F[t] > 0)
        sd += omCstF(t, fc + N - lc);
    else
        sd = 0;
    dmOut = dm;
    return sd;
}
bool omCollectOld(int t, int sc, int n, bool lazy) {
    omPosB.resize(sc);
    int k = 0;
    for (int w = 0; w < NW; w++) {
        ull m = t ? TBit[(t << 8) + w] : vb[w];
        while (m) {
            int cell = (w << 6) + __builtin_ctzll(m);
            m &= m - 1;
            if (k >= sc)
                return false;
            if (lazy) {
                int ix = omIdx[cell];
                if (ix < 0 || (omRec[ix] & 1))
                    return false;
                omPosB[k++] = ix;
            } else {
                if (omTk[cell] == omSer)
                    return false;
                omPosB[k++] = cell;
            }
        }
    }
    if (k != sc)
        return false;
    if (!lazy) {
        int j = 0;
        for (int i = 0; i < n && j < sc; i++)
            if (omFr[i] == omPosB[j])
                omPosB[j++] = i;
        if (j != sc)
            return false;
    }
    return true;
}
void omMaybeKeep(int t, int sc, int n, bool lazy) {
    if (sc < 2 || !omCollectOld(t, sc, n, lazy))
        return;
    int dA, dB;
    int k0 = 0;
    for (int k = 1; k < sc; k++)
        if (omPos[k] < omPos[k - 1]) {
            k0 = k;
            break;
        }
    if (k0)
        rotate(omPos.begin(), omPos.begin() + k0, omPos.end());
    ll cA = omEval(t, sc, omPos, dA), cB = omEval(t, sc, omPosB, dB);
    ll vA = cA + multiplyNonnegative(omLam, dA > 0 ? dA : 0) -
            (dA < 0 ? multiplyNonnegative(omLam, -dA) : 0);
    ll vB = cB + multiplyNonnegative(omLam, dB > 0 ? dB : 0) -
            (dB < 0 ? multiplyNonnegative(omLam, -dB) : 0);
    if (vB <= vA)
        omPos.swap(omPosB);
}
unsigned char omIn[MAXT];
bool omPart = false;
void om2GoodAdj() {
    const int md = OM2_TK(OM2_GU);
    for (int i = 0; i < N; i++) {
        int t = slotType[i];
        if (t == 0)
            continue;
        if (hcT[t]) {
            if (md & 2)
                omGoodS[i] = 0;
        } else if (md & 1)
            omGoodS[i] = 2;
    }
}
int om2Gam0 = 0;
inline void om2Layer(int t) {
    const int cl = t == 0 ? 0 : (hcT[t] ? 1 : 2);
    const int k = cl == 0 ? OM2_TK(OM2_HVV) : (cl == 1 ? OM2_TK(OM2_HVT) : OM2_TK(OM2_HVU));
    if (k != 16)
        omHV = multiplyNonnegative(omHV, k) >> 4;
    const int g = cl == 0 ? OM2_TK(OM2_GAV) : (cl == 1 ? OM2_TK(OM2_GAT) : OM2_TK(OM2_GAU));
    blGAMMA = g >= 0 ? g : om2Gam0;
}
inline void om2RelGood(int t) {
    auto PR = omPre.data();
    auto GS = omGoodS.data();
    if (t != 0) {
        int h = typeHead[t];
        if (h < 0)
            return;
        int cur = h;
        do {
            if (PR[cur] == t)
                GS[cur] = 0;
            cur = nextSame[cur];
        } while (cur != h);
    } else {
        for (int w = 0; w < NW; w++) {
            ull m = vb[w];
            while (m) {
                int cell = (w << 6) + __builtin_ctzll(m);
                m &= m - 1;
                if (PR[cell] == 0)
                    GS[cell] = 0;
            }
        }
    }
}
inline void om2Release(int t) {
    auto IX = omIdx.data();
    auto PR = omPre.data();
    auto RC = omRec.data();
    if (t != 0) {
        int h = typeHead[t];
        if (h < 0)
            return;
        int cur = h;
        do {
            int ix = IX[cur];
            if (ix >= 0 && PR[cur] == t)
                RC[ix] &= ~2;
            cur = nextSame[cur];
        } while (cur != h);
    } else {
        for (int w = 0; w < NW; w++) {
            ull m = vb[w];
            while (m) {
                int cell = (w << 6) + __builtin_ctzll(m);
                m &= m - 1;
                int ix = IX[cell];
                if (ix >= 0 && PR[cell] == 0)
                    RC[ix] &= ~2;
            }
        }
    }
}
#define HC_KEEP 0
#define HC_KW 3
#define HC_KR 2
#define HC_KSKIP 1
#define HC_KEEPN 0
const int HCKW_MAX = 8;
int hcKA[MAXN];
unsigned char hcKCh[MAXN][(HCKW_MAX << 1) + 1];
unsigned char hcKBlk[MAXN], hcKAct[MAXN];
RVEC(int) hcPosB;
int om2KeepM = 0, om2KW = HC_KW, om2KR = HC_KR;
ll omPatVal(int t, int sc, const RVEC(int) & pos, bool lazy) {
    const ll HV = omHV, GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const ll INF = (ll)1 << 61;
    omTabFor(t);
    auto PS = pos.data();
    auto FR = omFr.data();
    auto RC = omRec.data();
    auto HS = omHitS.data();
    int k0 = 0;
    for (int k = 1; k < sc; k++)
        if (PS[k] < PS[k - 1]) {
            k0 = k;
            break;
        }
    ll v = 0;
    int fc = -1, lc = -1, kp = k0;
    for (int k = 0; k < sc; k++) {
        int ix = PS[kp];
        kp++;
        if (kp >= sc)
            kp = 0;
        int cell = FR[ix];
        if (lazy) {
            int r = RC[ix];
            if (r & 1)
                return INF;
            if ((r >> 2) == t)
                v -= HV;
            else if (r & 2)
                v += GV;
        } else {
            int h = HS[ix];
            if (h == 1)
                v -= HV;
            else if (h == 2)
                v += GV;
        }
        if (lc >= 0) {
            if (cell <= lc)
                return INF;
            v += omCstF(t, cell - lc);
        } else
            fc = cell;
        lc = cell;
    }
    if (sc >= 2)
        v += omCstF(t, fc + N - lc);
    return v;
}
// 在有限候选中寻找保留方案，减少重构引入的额外改变。
bool omKeepDP(int t, int sc, int w, bool lazy) {
    if (sc < 3)
        return false;
    if (w > HCKW_MAX)
        w = HCKW_MAX;
    int k = 0;
    if (t != 0 && typeHead[t] >= 0) {
        int h = typeHead[t], cur = h, mi = 0;
        do {
            if (k >= sc)
                return false;
            hcKA[k] = cur;
            if (cur < hcKA[mi])
                mi = k;
            k++;
            cur = nextSame[cur];
        } while (cur != h);
        if (k != sc)
            return false;
        if (mi)
            rotate(hcKA, hcKA + mi, hcKA + sc);
    } else {
        for (int ww = 0; ww < NW; ww++) {
            ull m = t ? TBit[(t << 8) + ww] : vb[ww];
            while (m) {
                if (k >= sc)
                    return false;
                hcKA[k++] = (ww << 6) + __builtin_ctzll(m);
                m &= m - 1;
            }
        }
        if (k != sc)
            return false;
    }
    const ll HV = omHV, GV = multiplyNonnegative(HV, blGAMMA) >> 3;
    const ll INF = (ll)1 << 61;
    auto IXd = omIdx.data();
    auto RCd = omRec.data();
    auto HSd = omHitS.data();
    auto node = [&](int c) -> ll {
        while (c >= N)
            c -= N;
        while (c < 0)
            c += N;
        int ix = IXd[c];
        if (ix < 0)
            return INF;
        if (lazy) {
            int r = RCd[ix];
            if (r & 1)
                return INF;
            return (r >> 2) == t ? -HV : ((r & 2) ? GV : 0);
        }
        int hh = HSd[ix];
        return hh == 1 ? -HV : (hh == 2 ? GV : 0);
    };
    int nbl = 0;
    for (int j = 0; j < sc; j++) {
        hcKBlk[j] = node(hcKA[j]) >= INF;
        nbl += hcKBlk[j];
        hcKAct[j] = 0;
    }
    if (nbl == 0) {
        hcPosB.resize(sc);
        auto PB = hcPosB.data();
        for (int j = 0; j < sc; j++)
            PB[j] = IXd[hcKA[j]];
        return true;
    }
    const int kr_ = om2KR;
    if (kr_ > 0) {
        for (int j = 0; j < sc; j++)
            if (hcKBlk[j])
                for (int e = -kr_; e <= kr_; e++) {
                    int jj = j + e;
                    if (jj < 0)
                        jj += sc;
                    else if (jj >= sc)
                        jj -= sc;
                    hcKAct[jj] = 1;
                }
    } else
        for (int j = 0; j < sc; j++)
            hcKAct[j] = 1;
    int a0 = -1;
    for (int j = 0; j < sc; j++) {
        if (hcKBlk[j])
            continue;
        ll nv = node(hcKA[j]);
        if (nv < 0 && !hcKAct[j]) {
            a0 = j;
            break;
        }
        if (a0 < 0)
            a0 = j;
    }
    if (a0 < 0)
        return false;
    hcKAct[a0] = 0;
    omTabFor(t);
    const int W = (w << 1) + 1;
    ll V[(HCKW_MAX << 1) + 1], Vn[(HCKW_MAX << 1) + 1];
    for (int d = 0; d < W; d++)
        V[d] = INF;
    V[w] = node(hcKA[a0]);
    int prevBase = hcKA[a0], prevAct = 0;
    for (int j = 1; j < sc; j++) {
        int g = a0 + j, wrap = 0;
        if (g >= sc) {
            g -= sc;
            wrap = N;
        }
        int base = hcKA[g] + wrap;
        int ac = hcKAct[g];
        if (!ac && !prevAct) {
            if (V[w] >= INF)
                return false;
            V[w] += omCstF(t, base - prevBase) + node(base);
            hcKCh[j][w] = (unsigned char)w;
            prevBase = base;
            continue;
        }
        int dlo = ac ? 0 : w, dhi = ac ? W - 1 : w;
        int elo = prevAct ? 0 : w, ehi = prevAct ? W - 1 : w;
        for (int d = 0; d < W; d++)
            Vn[d] = INF;
        for (int d = dlo; d <= dhi; d++) {
            ll nc = node(base + d - w);
            if (nc >= INF) {
                hcKCh[j][d] = (unsigned char)w;
                continue;
            }
            ll best = INF;
            int bd = w;
            int p = base + d - w;
            for (int e = elo; e <= ehi; e++) {
                if (V[e] >= INF)
                    continue;
                int gap = p - (prevBase + e - w);
                if (gap < 1)
                    continue;
                ll v = V[e] + omCstF(t, gap);
                if (v < best) {
                    best = v;
                    bd = e;
                }
            }
            Vn[d] = best >= INF ? INF : best + nc;
            hcKCh[j][d] = (unsigned char)bd;
        }
        bool any = false;
        for (int d = 0; d < W; d++) {
            V[d] = Vn[d];
            any |= Vn[d] < INF;
        }
        if (!any)
            return false;
        prevBase = base;
        prevAct = ac;
    }
    ll best = INF;
    int bd = -1;
    for (int d = 0; d < W; d++) {
        if (V[d] >= INF)
            continue;
        int gap = hcKA[a0] + N - (prevBase + d - w);
        if (gap < 1)
            continue;
        ll v = V[d] + omCstF(t, gap);
        if (v < best) {
            best = v;
            bd = d;
        }
    }
    if (bd < 0)
        return false;
    hcPosB.resize(sc);
    auto PB = hcPosB.data();
    int d = bd;
    for (int j = sc - 1; j >= 1; j--) {
        int g = a0 + j;
        if (g >= sc)
            g -= sc;
        int c = hcKA[g] + d - w;
        if (c >= N)
            c -= N;
        else if (c < 0)
            c += N;
        PB[j] = IXd[c];
        d = hcKCh[j][d];
    }
    PB[0] = IXd[hcKA[a0]];
    return true;
}
void omKeepTry(int t, int sc, bool lazy) {
    if (sc < 3 || N < HC_KEEPN)
        return;
    const int km = om2KeepM;
    if (!(km >= 3 || t != 0) || !(km >= 2 || !hcT[t]))
        return;
    if (HC_KSKIP) {
        int hits = 0;
        auto OP = omPos.data();
        auto RC = omRec.data();
        auto HS = omHitS.data();
        for (int k2 = 0; k2 < sc; k2++) {
            int ix = OP[k2];
            hits += lazy ? ((RC[ix] >> 2) == t) : (HS[ix] == 1);
        }
        if (hits >= sc)
            return;
    }
    if (!omKeepDP(t, sc, om2KW, lazy))
        return;
    ll vA = omPatVal(t, sc, omPos, lazy), vB = omPatVal(t, sc, hcPosB, lazy);
    if (vB < vA)
        omPos.swap(hcPosB);
}
#define RQ_PSPARSE 0
int vcInInit = 0;
#define VC_TV0 16
ll vcVacBase = -1;
#define VC_RV0K 16
#define VC_OMHVO 16
#define VC_OMHVT 2
#define VC_OMVP 0
void vcOmPos() {
    if (VC_OMVP <= 0 || N <= NM || (VC_OMVR && vcInInit))
        return;
    int n = (int)omOrd.size(), p = -1;
    for (int i = 0; i < n; i++)
        if (omOrd[i] == 0) {
            p = i;
            break;
        }
    if (p < 0)
        return;
    int k = VC_OMVP < n - 1 ? VC_OMVP : n - 1;
    for (int i = p; i < k; i++)
        omOrd[i] = omOrd[i + 1];
    if (p < k)
        omOrd[k] = 0;
}
#define VC_OMVS 0
#define VC_OMT 16
#define MD2_OMLO 1000
#define MD2_OMV 16
#define MD2_OMVSH 16
#define MD2_OMHV 16
#define MD2_OMHVO 16
#define MD2_OMHVSH 16
SP2_I ll vcOmKey(int t) {
    if (MD2_OMV != 16 && t == 0 && N <= NM && N > MD2_OMLO && !vcInInit &&
        (MD2_OMVSH >= 16 || ((ll)typeSize[0] << 4) <= multiplyNonnegative(N, MD2_OMVSH)))
        return multiplyNonnegative(typeSize[0], MD2_OMV) >> 4;
    if (VC_OMT != 16 && t != 0 && N > NM && hcT[t] && !(VC_OMVR && vcInInit))
        return multiplyNonnegative(typeSize[t], VC_OMT) >> 4;
    if (t == 0 && VC_OMV != 16 && !(VC_OMVR && vcInInit) &&
        ((VC_OMVT & (N > NM ? 2 : 1)) || ((SM_VCT & 2) && smT)) &&
        (VC_OMVS == 0 || ((VC_OMVS == 1) == ((typeSize[0] << 1) <= N))) &&
        (VC_OMVSH >= 16 || ((ll)typeSize[0] << 4) <= multiplyNonnegative(N, VC_OMVSH)))
        return multiplyNonnegative(typeSize[0], VC_OMV) >> 4;
    return (ll)typeSize[t];
}
vector<int> bg1St, bg1Of, bg1Buf;
unsigned short bg1RelM[MAXT + 1];
