// 一次在线增删操作的完整流水线。先更新目标计数与代价，再完成必要放置，并按预算执行修复。
// Included in fixed order by solution.cpp.

// 执行一轮增删：准备本次权重、放置必要改动，再按预算修复。
void processOperation(int x, int add, int c) {
    operationStamp++;
    if (xlsSBon)
        for (int w = 0; w <= NW; w++)
            xlsSB[w] = 0;
    zchNN = 0;
    hvbH = N > HVB_NLO && ((ll)c << 5) >= N;
    hvbX = hvbH;
    if (HVB_VCAP > 0 && hvbH) {
        hvbVol += c;
        if (hvbVol > multiplyNonnegative(N, HVB_VCAP))
            hvbX = 0;
    }
    if (HVB_RD > 0)
        hvbHr += (((int)hvbH << 8) - hvbHr) >> HVB_RDE;
    if (HVB_CR0 > 0 && HVB_CRA > 0 && N > MNHI) {
        ehMnCredit += multiplyNonnegative(N, HVB_CRA) >> 4;
        const ll cp_ = multiplyNonnegative(N, HVB_CR0);
        if (ehMnCredit > cp_)
            ehMnCredit = cp_;
    }
    if (LGM_ANY)
        lgmL = mqT && ((ll)c << 5) < N;
    if (LGM_MNOFF >= 2)
        lgmAdd = add;
    if (SDY_TW && smT) {
        int m = 0;
        for (int t = 1; t < typeSlotCount; t++)
            m += typeSize[t] > 0;
        int f = SDY_TWB + (int)(multiplyNonnegative(m, SDY_TWM) >> 4);
        if (f < SDY_TWLO)
            f = SDY_TWLO;
        if (f > SDY_TWHI)
            f = SDY_TWHI;
        if (f != sdyTw) {
            sdyTw = f;
            for (int t = 1; t < typeSlotCount; t++)
                if (typeSize[t] > 0) {
                    setType(t);
                    typePenaltyDirty[t] = 1;
                }
        }
    }
    if (SDY_HSON && SDY_HT) {
        if (SDY_HSM > 0) {
            int m = 0;
            for (int t = 1; t < typeSlotCount; t++)
                m += typeSize[t] > 0;
            int f = SDY_HSB + (int)(multiplyNonnegative(m, SDY_HSM) >> 4);
            if (f < SDY_HSLO)
                f = SDY_HSLO;
            if (f > SDY_HSHI)
                f = SDY_HSHI;
            sdyHf = f;
        } else
            sdyHf = SDY_HS;
        sdyHr = sdyHf;
        if (SDY_HRM >= 0) {
            int m = 0;
            for (int t = 1; t < typeSlotCount; t++)
                m += typeSize[t] > 0;
            int f = SDY_HRB + (int)(multiplyNonnegative(m, SDY_HRM) >> 4);
            if (f < SDY_HRLO)
                f = SDY_HRLO;
            if (f > SDY_HRHI)
                f = SDY_HRHI;
            sdyHr = f;
        }
    }
    if (BG2_PULL && !add && N > NM && !VC_VRL)
        for (int ww = 0; ww <= NW; ww++)
            vcVb0[ww] = vb[ww];
    if (MQ_GATE > 0)
        mqRich = ehMnCredit >= MQ_GATE;
    if ((VC_VRL && (!HVB_VCH || hvbH)) || (MQ_VRL && mqT) || (BOP_VR1 && !add && N > NM) ||
        (SDY_VRL && smT))
        for (int ww = 0; ww <= NW; ww++)
            vcVb0[ww] = vb[ww];
    if (VC_ZK > 0) {
        ll c16 = (ll)c << 4;
        vcCbar16 = vcCbar16 == 0 ? c16 : vcCbar16 + ((c16 - vcCbar16) >> 2);
    }
    if (TS_TAUE > 0) {
        ll c16 = (ll)c << 4;
        tsCbar16 = tsCbar16 == 0 ? c16 : tsCbar16 + ((c16 - tsCbar16) >> TS_TAUE);
        if (tsCbar16 < 16)
            tsCbar16 = 16;
    }
    if (((ll)c << 2) >= N)
        hugeRun++;
    else
        hugeRun = 0;
    hugeStk = (N >= 100 && hugeRun >= (N >= 1000 ? 8 : 16)) ? 1 : 0;
    {
        const ll n16 = (ll)N << 4;
        rmCls = multiplyNonnegative(tsCbar16, 100) <= n16
                    ? 0
                    : (multiplyNonnegative(tsCbar16, 32) <= n16
                           ? 1
                           : (multiplyNonnegative(tsCbar16, 16) <= n16 ? 2 : 3));
    }
    mdRbOp = 0;
    hcT[x] = 1;
    typePenaltyDirty[x] = 1;
    const bool shBig = c > CBIG && ((add ? 1 : 2) & SH_BOP) != 0;
    int ccap = c > CBIG ? (shBig ? blCCAPB : 0) : (N > NM ? RB_CCAP : CCAP);
    const int budc = (BF_BUDCB >= 0 && N > NM && c > CBIG) ? BF_BUDCB : pBUDC;
    int lsBudget = (N > c && pBUDB + budc > 0)
                       ? pBUDB + (int)multiplyNonnegative(budc, c < ccap ? c : ccap)
                       : 0;
    if (c > CBIG && pBUDBB >= 0)
        lsBudget = N > c ? pBUDBB : 0;
#define RB_NSC 0
    if (NSCALE && N < NSCALE && lsBudget > 0 && !(RB_NSC && N > NM) && !(SM_NSC && smT)) {
        lsBudget = (int)divideNonnegative(multiplyNonnegative(lsBudget, N), NSCALE);
        if (lsBudget < 8)
            lsBudget = 8;
    }
    seedCap = lsBudget > 0 ? lsBudget : 0;
    int lsH = currentHorizon();
    if (MD_LSH > 0 && N > MNLO && N <= MNHI && lsH > MD_LSH)
        lsH = MD_LSH;
    if (SM_LSH > 0 && smT && lsH > SM_LSH)
        lsH = SM_LSH;
    const bool boBig = N >= BO_NMIN && N > c;
    if (BO_LSC && boBig && c >= (N >> BO_LSC)) {
        lsBudget = BO_LSB + (int)(multiplyNonnegative(c, BO_LSK) >> 4);
        seedCap = lsBudget;
        if (lsH > BO_LSH)
            lsH = BO_LSH;
    }
    if (HVB_LSK > 0 && hvbH && lsBudget > 0) {
        lsBudget = (int)(multiplyNonnegative(lsBudget, HVB_LSK) >> 4);
        seedCap = lsBudget;
    }
    curWin = c > CBIG ? WINB : WIN;
    fastPk = c > CFAST;
    if (curWin > ((N - 1) >> 1))
        curWin = (N - 1) >> 1;
    const int s0x = typeSize[x];
    if (add)
        placeAddedGranules(x, c);
    else
        selectRemovedGranules(x, c);
    rbxNS = 0;
    if (!add && N > RBX_NLO && N > c && (!RBX_FHV || hvbH) &&
        ((ll)typeSize[0] << 4) >= multiplyNonnegative(N, RBX_FVLO))
        for (int k = 0; k < nSeeds; k++) {
            const int p = seedA[k];
            if (slotType[p] == 0 && changedNow(p))
                rbxSrc[rbxNS++] = p;
        }
    if (RBX_FA && add && hvbH && N > c && typeSize[0] >= 3 &&
        ((ll)typeSize[0] << 4) >= multiplyNonnegative(N, RBX_FVLO))
        for (int k = 0; k < nSeeds && rbxNS < MAXN; k++) {
            const int p = seedA[k];
            if (slotType[p] == x && changedNow(p)) {
                const int a0 = prevVac(p), b0 = nextVac(p);
                if (a0 >= 0)
                    rbxSrc[rbxNS++] = a0;
                if (b0 >= 0 && b0 != a0 && rbxNS < MAXN)
                    rbxSrc[rbxNS++] = b0;
            }
        }
    if (EH_V0K) {
        ll c16 = (ll)c << 4;
        ehCbar16 = ehCbar16 == 0 ? c16 : ehCbar16 + ((c16 - ehCbar16) >> EH_V0E);
        if (ehCbar16 < 16)
            ehCbar16 = 16;
        if (N > c && typeSize[0] >= 2) {
            const bool mdV = N > MNLO && N <= MNHI;
            int hr = (mdV && MD_V0R > 0) ? MD_V0R : ((BF_V0R > 0 && N > NM) ? BF_V0R : EH_V0R);
            if (SM_V0R > 0 && smT)
                hr = sdyH(SM_V0R);
            if (MQ_V0R > 0 && mqT && MQG(16))
                hr = MQ_V0R;
            if (EH_V0K >= 2) {
                int hh = currentHorizon();
                if (hr > hh)
                    hr = hh;
            }
            if (hr < 1)
                hr = 1;
            ll k = divideNonnegative((ll)typeSize[0]
                                         << (((SM_V0S >= 0 && smT)   ? SM_V0S
                                              : (MQ_V0S >= 0 && mqT) ? MQ_V0S
                                              : (mdV && MD_V0S >= 0)
                                                  ? MD_V0S
                                                  : ((BF_V0S >= 0 && N > NM) ? BF_V0S : EH_V0S)) +
                                             8),
                                     multiplyNonnegative(ehCbar16, hr));
            {
                const int fl_ =
                    N > NM ? BOP_V0MB : (N > 1000 ? BOP_V0MM : (N > 100 ? BOP_V0MS : BOP_V0MT));
                const int fl = fl_ >= 0 ? fl_ : EH_V0MIN;
                if (k < fl)
                    k = fl;
            }
            if (EH_V0K >= 3) {
                ll k1 = divideNonnegative(16, hr);
                if (k < k1)
                    k = k1;
            }
            if (k < 16) {
                ehV0k = (int)k;
                setType(0);
            }
        }
    }
    if (rbxNS > 0 && (!add || RBX_FA)) {
        const ll thr0 = thrM;
        thrM = divideNonnegative(
            multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
            multiplyNonnegative(multiplyNonnegative(11, (add && RBX_FAH > 0) ? RBX_FAH : RBX_FH),
                                N - c));
        const int v0k = ehV0k;
        if (RBX_FV0 && v0k != 16) {
            ehV0k = 16;
            setType(0);
            typePenaltyDirty[0] = 1;
        }
        rbxFar(add);
        if (RBX_FV0 && v0k != 16) {
            ehV0k = v0k;
            setType(0);
            typePenaltyDirty[0] = 1;
        }
        thrM = thr0;
        rbxNS = 0;
    }
#define BOP_RAR 0
    if (BOP_RA && add && s0x > 0 && N >= BOP_RAN && N > c && c >= (N >> BOP_RAC) &&
        (BOP_RAV >= 16 || ((ll)typeSize[0] << 4) < multiplyNonnegative(N, BOP_RAV)) &&
        (BOP_RAR == 0 || ((ll)c << 4) <= multiplyNonnegative(s0x, BOP_RAR))) {
#define BOP_RAH2 0
#define BOP_RAR2 16
        bopReAdd(x, (BOP_RAH2 > 0 && ((ll)c << 4) > multiplyNonnegative(s0x, BOP_RAR2)) ? BOP_RAH2
                                                                                        : BOP_RAH);
    }
    if (BO_RX && boBig && c >= (N >> BO_RXC) && (HVB_VCAP == 0 || hvbX) && typeSize[x] >= 3 &&
        (BO_RXG == 0 || ((ll)c << 4) <= multiplyNonnegative(typeSize[x], BO_RXG)) &&
        ((add && s0x > 0 && (BO_RX & 1)) || (!add && (BO_RX & 2)) ||
         (add && s0x == 0 && (BO_RX & 4)))) {
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, BO_RXT), N - c));
#define BOP_RXV 16
        if (BOP_RXV >= 16 || ((ll)typeSize[0] << 4) < multiplyNonnegative(N, BOP_RXV))
            if (R2_RXS < 0 || r2VacExcess() > (multiplyNonnegative(thr, typeSize[x]) >> R2_RXS))
                relx4(x, BO_RXH, thr);
    }
#define SDY_BOC 5
#define SDY_BOT 2
#define SDY_BOH 2
#define SDY_BOK 0
#define SDY_BOHX 16
    if (SDY_BO && smT && N > c && c >= (N >> SDY_BOC) && typeSize[x] >= 3 &&
        ((add && s0x > 0 && (SDY_BO & 1)) || (!add && (SDY_BO & 2)) ||
         (add && s0x == 0 && (SDY_BO & 4)))) {
        int bh_ = SDY_BOT;
        if (SDY_BOK > 0) {
            int hh = (int)(multiplyNonnegative(sdyLive(), SDY_BOK) >> 4);
            if (hh < 1)
                hh = 1;
            if (hh > SDY_BOHX)
                hh = SDY_BOHX;
            bh_ = hh;
        }
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, bh_), N - c));
        relx4(x, SDY_BOH, thr);
    }
    if (blSH_LSK > 0) {
        ll c16 = (ll)c << 4;
        shCbar16 += (c16 - shCbar16) >> SH_LSE;
        if (shCbar16 < 16)
            shCbar16 = 16;
    }
    const bool zchOn =
        ZCH_P && add && s0x > 0 && N > ZCH_NLO && N > c && c >= (N >> ZCH_C) && zchNN > 0;
    if (zchOn && (ZCH_P & 1)) {
        const ll thr =
            divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                              multiplyNonnegative(multiplyNonnegative(11, ZCH_H), N - c));
        const int sc0 = seedCap;
        if (seedCap < (lsBudget << 1))
            seedCap = lsBudget << 1;
        if (ZCH_DP)
            zchRuns(x, thr, ZCH_W);
        else
            zchPass(x, thr, ZCH_W);
        seedCap = sc0;
    }
    if (N > c && lsBudget > 0) {
        {
            int hh = lsH;
            if (RB_LSHC > 0 && N > NM && hh > RB_LSHC)
                hh = RB_LSHC;
            if (blSH_LSH > 0 && shBig && hh > blSH_LSH)
                hh = blSH_LSH;
            if (blSH_LSK > 0) {
                ll hk = divideNonnegative(multiplyNonnegative(N, blSH_LSK), shCbar16);
                if (hk < 1)
                    hk = 1;
                if (hh > hk)
                    hh = (int)hk;
            }
            if (HVB_LSH > 0 && hvbH)
                hh = HVB_LSH;
            thrM = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                     multiplyNonnegative(multiplyNonnegative(11, hh), N - c));
        }
        seedCap = lsBudget << 1;
        int n0 = nSeeds;
        for (int k = 0; k < n0; k++) {
            int p = seedA[k];
            int t = slotType[p];
            pushSeed(prvT(p, t));
            pushSeed(nxtT(p, t));
        }
        seedCap = lsBudget << 2;
#define BOP_VS 0
#define BOP_VSC 6
#define BOP_VSN 5000
        if (BOP_VS && add && N >= BOP_VSN && c >= (N >> BOP_VSC) && ((s0x > 0 ? 1 : 2) & BOP_VS) &&
            typeSize[0] >= 2) {
            for (int k = 0; k < n0; k++) {
                int p = seedA[k];
                if (slotType[p] == x) {
                    pushSeed(prevVac(p));
                    pushSeed(nextVac(p));
                }
            }
        }
#define LT_FS 0
#define LT_FSN 5000
#define LT_FSM 3
#define LT_FSD 0
#define LT_FSG 2
#define LT_FSCX 0
#define LT_FSCN 0
#define LT_FSV 16
        if (LT_FS > 0 && N >= LT_FSN && ((add ? 1 : 2) & LT_FSM) &&
            (LT_FSCX == 0 || c <= LT_FSCX) && c > LT_FSCN &&
            (typeSize[0] << 4) < multiplyNonnegative(N, LT_FSV)) {
            for (int k = 0; k < n0; k++) {
                const int p = seedA[k], tp = slotType[p];
                for (int d = 1; d <= LT_FS; d++) {
                    int j = p - d;
                    if (j < 0)
                        j += N;
                    int tj = slotType[j];
                    if (tj != 0 && tj != tp) {
                        if (!LT_FSD || dist(j, nextSame[j]) >= dist(prevSame[j], j) + LT_FSG)
                            pushSeed(j);
                    }
                    j = p + d;
                    if (j >= N)
                        j -= N;
                    tj = slotType[j];
                    if (tj != 0 && tj != tp) {
                        if (!LT_FSD || dist(prevSame[j], j) >= dist(j, nextSame[j]) + LT_FSG)
                            pushSeed(j);
                    }
                }
            }
        }
#define RB_LSSTR 0
        if (RB_LSSTR > 1 && N > NM && nSeeds > RB_LSSTR) {
            static int lsTmp[(MAXN << 2) + 16];
            int m = 0;
            for (int r = 0; r < RB_LSSTR; r++)
                for (int k = r; k < nSeeds; k += RB_LSSTR)
                    lsTmp[m++] = seedA[k];
            for (int k = 0; k < m; k++)
                seedA[k] = lsTmp[k];
        }
        vpmMvOn = VPM_LMP && N > VPM_PN && (!VPM_HV || hvbH);
        vpmMvN = 0;
        runLocalSearch(lsBudget);
        vpmMvOn = 0;
    } else {
        for (int k = 0; k < nSeeds; k++)
            inq[seedA[k]] = 0;
        nSeeds = 0;
    }
#define BG2_PVLO 0
#define BG2_PVHI 16
#define BG2_PCLO 0
#define BG2_PCHI 1000000
    if (BG2_PULL && !add && N > NM && N > c && typeSize[0] >= 3 && F[0] > 0 &&
        ((ll)typeSize[0] << 4) >= multiplyNonnegative(N, BG2_PVLO) &&
        ((ll)typeSize[0] << 4) <= multiplyNonnegative(N, BG2_PVHI) && c >= BG2_PCLO &&
        c <= BG2_PCHI) {
        ll thr = thrM;
        if (BG2_PH > 0 || lsBudget <= 0)
            thr = divideNonnegative(
                multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                multiplyNonnegative(multiplyNonnegative(11, BG2_PH > 0 ? BG2_PH : 6), N - c));
        bg2Pull(thr);
    }
    if (HC_V0 && N > c && !add && (typeSize[0] << HC_VSH) <= N) {
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, HC_V0H), N - c));
        rqActM = HC_VACTM;
        rqBud = 1;
        rqActR = HC_V0R;
        relat(0, HC_V0W, thr);
        rqActM = 0;
        rqBud = 0;
        rqActR = RQ_ACT;
    }
#define BOP_VR1L 0
    if (BOP_VR1 && !add && N > NM && N > c && (typeSize[0] << VC_VSH) <= N &&
        c >= (N >> BOP_VR1C) && (BOP_VR1L == 0 || (typeSize[0] << BOP_VR1L) >= N)) {
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, BOP_VR1H), N - c));
        const int k0_ = ehV0k;
        if (BOP_VR1K > 0 && ehV0k < BOP_VR1K) {
            ehV0k = BOP_VR1K;
            setType(0);
        }
        bopVr1(thr);
        if (BOP_VR1K > 0 && ehV0k != k0_) {
            ehV0k = k0_;
            setType(0);
        }
    }
#define BOP_VRC 0
#define BOP_VRN 0
    if (VC_VRL && N > c && ((add ? 2 : 1) & VC_VRL) != 0 && (typeSize[0] << VC_VSH) <= N &&
        (VC_VSL == 0 || (typeSize[0] << VC_VSL) >= N) && (BOP_VRC == 0 || c >= (N >> BOP_VRC)) &&
        N >= BOP_VRN && (!HVB_VCH || hvbH)) {
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, VC_VH), N - c));
        if (VC_REF) {
            rqActM = 1;
            rqBud = 1;
            rqActR = VC_VR;
            relat(0, VC_VW, thr);
            rqActM = 0;
            rqBud = 0;
            rqActR = RQ_ACT;
        } else
            vcRelat0(VC_VW, thr, VC_VR);
    }
    if (SDY_VRL && smT && N > c && ((add ? 2 : 1) & SDY_VRL) != 0 &&
        (typeSize[0] << SDY_VSH) <= N) {
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, SDY_VVH), N - c));
        vcRelat0(SDY_VVW, thr, SDY_VVR);
    }
    if (MQ_VRL && mqT && N > c && ((add ? 2 : 1) & MQ_VRL) != 0 && (typeSize[0] << MQ_VSH) <= N) {
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, MQ_VH), N - c));
        vcRelat0(MQ_VW, thr, MQ_VR);
    }
    if (N > c && N > VPM_PN && vpmMvN > 0) {
        vpmLmp(c);
        vpmMvN = 0;
    }
    if (RQ_VR && N > c && N <= RQ_VRN && !(MD_NOVR && N > MNLO && N <= MNHI)) {
        int vh = RQ_VH;
        if (HZP & 1) {
            int hh = currentHorizon();
            if (vh > hh)
                vh = hh;
        }
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, vh), N - c));
        if (!add && (RQ_VR & 1) != 0) {
            rqActM = RQ_ACTM;
            rqBud = 1;
            relat(0, RQ_VW, thr);
            rqActM = 0;
            rqBud = 0;
        }
        if (add && (RQ_VR & 2) != 0) {
            rqActM = RQ_ACTM;
            rqBud = 1;
            relat(0, RQ_VW, thr);
            rqActM = 0;
            rqBud = 0;
        }
        if (add && (RQ_VR & 4) != 0 && (!(RQ_VR & 16) || typeSize[x] == c) &&
            typeSize[x] <= RQ_SMAX) {
            rqActM = RQ_ACTM;
            rqBud = 1;
            relat(x, c > RQ_CW ? RQ_RWB : RQ_RW, thr);
            rqActM = 0;
            rqBud = 0;
        }
        if (!add && (RQ_VR & 8) != 0 && typeSize[x] > 0) {
            rqActM = 0;
            rqBud = 1;
            relat(x, RQ_RW, thr);
            rqBud = 0;
        }
    }
    if (SM_VR && smT && N > c && (SDY_VRM == 0 || sdyLive() >= SDY_VRM)) {
        int vh_ = SM_VH;
        if (SDY_VRK > 0) {
            int hh = (int)(multiplyNonnegative(sdyLive(), SDY_VRK) >> 4);
            if (hh < 1)
                hh = 1;
            if (hh > SDY_VRHX)
                hh = SDY_VRHX;
            vh_ = hh;
        }
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, vh_), N - c));
        rqActM = SM_VACT;
        rqBud = 1;
        if (!add && (SM_VR & 1) != 0)
            relat(0, SM_VW, thr);
        if (add && (SM_VR & 2) != 0)
            relat(0, SM_VW, thr);
        if (add && (SM_VR & 4) != 0)
            relat(x, SM_RW, thr);
        if (!add && (SM_VR & 8) != 0 && typeSize[x] >= 3)
            relat(x, SM_RW, thr);
        rqActM = 0;
        rqBud = 0;
    }
    if (SM_SWK > 0 && smT && N > c && (operationStamp & (SM_SWK - 1)) == 0) {
        totalLayoutPenalty();
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, SM_SWH), N - c));
        int sel[16];
        ll sv[16];
        int ns = 0;
        for (int t = 0; t < typeSlotCount; t++) {
            int sc = typeSize[t];
            if (sc < 3 || F[t] == 0 || (t == 0 && !SM_SWV))
                continue;
            ll r = rv[t];
            ll ex =
                (t ? PtC[t] : P0c) - multiplyNonnegative(multiplyNonnegative(r, sc - r) << 1, F[t]);
            if (ex <= thr)
                continue;
            int k2 = ns < SM_SWN ? ns++ : SM_SWN;
            if (k2 == SM_SWN) {
                if (ex <= sv[SM_SWN - 1])
                    continue;
                k2 = SM_SWN - 1;
            }
            while (k2 > 0 && sv[k2 - 1] < ex) {
                sv[k2] = sv[k2 - 1];
                sel[k2] = sel[k2 - 1];
                k2--;
            }
            sv[k2] = ex;
            sel[k2] = t;
        }
        rqBud = 1;
        for (int i = 0; i < ns; i++)
            relat(sel[i], SM_SWW, thr);
        rqBud = 0;
    }
    if (zchOn && (ZCH_P & 2)) {
        const ll thr =
            divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                              multiplyNonnegative(multiplyNonnegative(11, ZCH_H), N - c));
        if (ZCH_DP)
            zchRuns(x, thr, ZCH_W);
        else
            zchPass(x, thr, ZCH_W);
    }
#define ZCH_RLC 0
#define ZCH_RLX 0
    if (SH_VRL && add && N > c && N > RQ_VRN && N > NM &&
        (SH_VRG == 0 || ((ll)c << SH_VRG) >= typeSize[x]) &&
        (ZCH_RLC == 0 || (ZCH_RLC > 0 ? c >= (N >> ZCH_RLC) : c < (N >> -ZCH_RLC))) &&
        (ZCH_RLX == 0 || (ZCH_RLX == 1 ? s0x > 0 : s0x == 0)) && (!HVB_VRH || hvbH)) {
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, SH_VRH), N - c));
        ll wb0 = rqWBv;
        rqWBv = SH_VRWB;
        rqActM = SH_VRA;
        rqBud = 1;
        int ar0 = rqActR;
        if (SH_VRAR > 0)
            rqActR = SH_VRAR;
#define ZCH_RMASK 0
        zchMask = ZCH_RMASK;
        relat(x, SH_VRW, thr);
        zchMask = 0;
        rqActM = 0;
        rqBud = 0;
        rqWBv = wb0;
        rqActR = ar0;
    }
    if (HVB_RXR > 0 && hvbH && !add && N > c && typeSize[x] >= 3) {
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, SH_VRH), N - c));
        rqBud = 1;
        relat(x, HVB_RXR, thr);
        rqBud = 0;
    }
    if (RQ_SWK > 0 && N > c && (operationStamp & (RQ_SWK - 1)) == 0) {
        totalLayoutPenalty();
        ll thr = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                   multiplyNonnegative(multiplyNonnegative(11, RQ_SWH), N - c));
        int sel[16];
        ll sv[16];
        int ns = 0;
        for (int t = 0; t < typeSlotCount; t++) {
            int sc = typeSize[t];
            if (sc < 3 || F[t] == 0 || (t == 0 && !RQ_SWV))
                continue;
            ll r = rv[t];
            ll ex =
                (t ? PtC[t] : P0c) - multiplyNonnegative(multiplyNonnegative(r, sc - r) << 1, F[t]);
            if (ex <= thr)
                continue;
            int k2 = ns < RQ_SWN ? ns++ : RQ_SWN;
            if (k2 == RQ_SWN) {
                if (ex <= sv[RQ_SWN - 1])
                    continue;
                k2 = RQ_SWN - 1;
            }
            while (k2 > 0 && sv[k2 - 1] < ex) {
                sv[k2] = sv[k2 - 1];
                sel[k2] = sel[k2 - 1];
                k2--;
            }
            sv[k2] = ex;
            sel[k2] = t;
        }
        for (int i = 0; i < ns; i++)
            relat(sel[i], RQ_SWW, thr);
    }
    if (MND && MNPOS == 0 && N > MNLO && N <= MNHI && N > c)
        mnRun(x, c);
    if (SQ_PRE > 0 && N > SQ_PRELO && N <= SQ_PREHI && (N <= SQ_PRETHI || N > 100) && N > c &&
        (operationStamp & (SQ_PRE - 1)) == 0 && !svWarming)
        sqPre(x, c);
    if (TSN > 0 && N <= TSN && N > c) {
        int hh = TSHF ? TSH : currentHorizon();
        if (hh > TSH)
            hh = TSH;
        thrM = divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                 multiplyNonnegative(multiplyNonnegative(11, hh), N - c));
        hzWork = 0;
        hzLim = TOW;
        tinyDescent(TSP);
    }
    if (VC_RV0K < 16 && N > NM && N > c && typeSize[0] >= 2 && ehV0k > VC_RV0K) {
        ehV0k = VC_RV0K;
        setType(0);
        typePenaltyDirty[0] = 1;
    }
    const bool rmMid = N > MNLO && N <= MNHI;
    if (pTAU > 0 && !(RM_NOREP3 && rmMid && rmCls == 3)) {
        sdyHcur = 0;
        int tauE = sdyR(pTAU), tauAE = sdyR(pTAUA);
        if (rmMid) {
            int ta = rmPick(rmCls, RM_TAUA0, RM_TAUA1, RM_TAUA2, RM_TAUA3);
            if (ta > 0)
                tauAE = ta;
        }
        if (smT) {
            int ta = rmPick(rmCls, SM_TAUA0, SM_TAUA1, SM_TAUA2, SM_TAUA3);
            if (ta > 0)
                tauAE = ta;
        }
        if (HZR) {
            int hh = currentHorizon();
            if (tauE > hh)
                tauE = hh;
            if (tauAE > hh)
                tauAE = hh;
        }
        if (EH_TAUK > 0 && N > c && N <= EH_TAUN) {
            ll hk = divideNonnegative(
                multiplyNonnegative(N, (BG1_TAUKB > 0 && N > NM) ? BG1_TAUKB : EH_TAUK),
                TS_TAUE > 0 ? tsCbar16 : ((ll)c << 4));
            if (hk < 1)
                hk = 1;
            if (SDY_HSON && SDY_HT && hk < 1000000)
                hk = sdyR((int)hk);
            if (tauE > hk)
                tauE = (int)hk;
            if (tauAE > hk)
                tauAE = (int)hk;
        }
        sinceRb++;
        if (EH_RBDEC > 0 && N > EH_RBDN && N <= EH_RBDX)
            rbExcess -= rbExcess >> EH_RBDEC;
        if (RBK > 0) {
            wCredit += RBKB ? (ll)(N >> 4) : (ll)((RBKC ? c : 0) + OPW);
            if (wCredit > wCap)
                wCredit = wCap;
        }
#define SDY_BIGREM 0
#define SDY_BIGMIN -1
#define SDY_BIGSH 0
#define BQ_BIGREMB 0
        const bool hvbDf = HVB_RD > 0 && N > NM && hvbHr >= HVB_RD;
        if (N > c && (svWarmForce ||
                      (sinceRb >= pMINGAP && (sinceRb & (pCHK - 1)) == 0 && !(hvbDf && !hvbH)) ||
                      (pBIGSH > 0 &&
                       sinceRb >= ((BQ_BIGMINB > 0 && N > NM)                     ? BQ_BIGMINB
                                   : (MD2_BIGMIN >= 0 && N > MD2_BRLO && N <= NM) ? MD2_BIGMIN
                                   : (SDY_BIGMIN >= 0 && smT)                     ? SDY_BIGMIN
                                                                                  : BIGMIN) &&
                       c >= (N >> ((SDY_BIGSH > 0 && smT) ? SDY_BIGSH : pBIGSH)) &&
                       (add || !BIGADD || (MD2_BIGREM && N <= NM && N > MD2_BRLO) ||
                        (BQ_BIGREMB && N > NM) || (HVB_RDR && hvbDf) || (SDY_BIGREM && smT))))) {
            ll Pc = totalLayoutPenalty(), Pm = minimumPossiblePenalty();
            ll def = Pc - Pm - rbExcess;
            if (VC_TV0 != 16 && N > NM) {
                ll ve = r2VacExcess();
                if (vcVacBase < 0)
                    vcVacBase = ve;
                ll dv = ve - vcVacBase;
                if (dv > 0)
                    def = VC_TV0 < 16 ? def - (multiplyNonnegative(dv, 16 - VC_TV0) >> 4)
                                      : def + (multiplyNonnegative(dv, VC_TV0 - 16) >> 4);
            }
            bool go;
            ll md2RbM = rbM;
            if (MD2_TRK > 0 && N > MD2_BRLO && N <= NM) {
                md2RbM = rbM - (multiplyNonnegative(c, MD2_TRK) >> 4);
                if (md2RbM < 1)
                    md2RbM = 1;
            }
            if (pTRIG) {
                if (def < 0)
                    def = 0;
                accEx += multiplyNonnegative((lastEx + def) >> 7, sinceRb - lastChk);
                lastEx = def;
                lastChk = sinceRb;
                int lam = pLAM;
                if (rmMid) {
                    int la = rmPick(rmCls, RM_LAM0, RM_LAM1, RM_LAM2, RM_LAM3);
                    if (la > 0)
                        lam = la;
                }
                if (smT) {
                    int la = rmPick(rmCls, SM_LAM0, SM_LAM1, SM_LAM2, SM_LAM3);
                    if (la > 0)
                        lam = la;
                }
#define SDY_LAMK 0
                if (SDY_LAMK > 0 && SDY_HSON && smT && sdyHf > 0)
                    lam = (int)divideNonnegative(multiplyNonnegative(lam, SDY_LAMK), sdyHf);
                go = multiplyNonnegative(multiplyNonnegative(accEx, 11), N - c) >
                     (multiplyNonnegative(
                          multiplyNonnegative(md2RbM, 7),
                          multiplyNonnegative(multiplyNonnegative(N, N) << 3, lam)) >>
                      4);
            } else {
                go = def > 0 &&
                     multiplyNonnegative(
                         multiplyNonnegative(def, 11),
                         multiplyNonnegative(
                             (LGM_RBT > 0 && lgmL)
                                 ? (multiplyNonnegative(tauE,
                                                        (LGM_RBTB > 0 && ((ll)c << LGM_RBTS) >= N)
                                                            ? LGM_RBTB
                                                            : LGM_RBT) >>
                                    4)
                                 : tauE,
                             N - c)) > multiplyNonnegative(multiplyNonnegative(md2RbM, 7),
                                                           multiplyNonnegative(N, N) << 9);
            }
#ifdef RQ_ALWAYS
            go = true;
#endif
            if (svWarmForce)
                go = true;
            if (go && RBK > 0 && N >= RBKN) {
                if (wCredit < wRb)
                    go = false;
                else if (RBKW == 0)
                    wCredit -= wRb;
            }
            if (go && pRBMODE == 1) {
                fullRebuild();
                sinceRb = 0;
                rbExcess = rbPafter - Pm;
                if (rbExcess < 0)
                    rbExcess = 0;
                rbM = rbDeltaM < 1 ? 1 : rbDeltaM;
                accEx = 0;
                lastEx = 0;
                lastChk = 0;
                go = false;
            }
            if (go) {
                if (HZOM) {
                    int hr = currentHorizon();
                    if (hr > sdyR(HRB))
                        hr = sdyR(HRB);
                    if (OM2_TK(OM2_HVA) && hr > tauAE)
                        hr = tauAE;
                    if (OM2_TK(OM2_HVH) > 0 && N > c) {
                        ll hk = divideNonnegative(multiplyNonnegative(N, OM2_TK(OM2_HVH)),
                                                  TS_TAUE > 0 ? tsCbar16 : ((ll)c << 4));
                        if (hk < 1)
                            hk = 1;
                        if (SDY_HSON && SDY_HT && hk < 1000000)
                            hk = sdyR((int)hk);
                        if (hr > hk)
                            hr = (int)hk;
                    }
                    int hvk = (MD_HVK > 0 && N > MNLO && N <= MNHI) ? MD_HVK : blHVK;
                    if (rmMid) {
                        int hv = rmPick(rmCls, RM_HVK0, RM_HVK1, RM_HVK2, RM_HVK3);
                        if (hv > 0)
                            hvk = hv;
                    }
                    if (smT) {
                        int hv = rmPick(rmCls, SM_HVK0, SM_HVK1, SM_HVK2, SM_HVK3);
                        if (hv > 0)
                            hvk = hv;
                    }
                    omHV = multiplyNonnegative(
                        divideNonnegative(multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                                          multiplyNonnegative(multiplyNonnegative(11, hr),
                                                              N - c > 0 ? N - c : 1)),
                        (HC_HVKH > 0 && currentHorizon() < HC_HVKH) ? HC_HVKS : hvk);
                } else
                    omHV = multiplyNonnegative(lamFor(c), blHVK);
                rqC = c;
                omSteps = 0;
                om2Rep = !vcInInit;
                const int om2Pm =
                    (LGM_PART > 0 && lgmL && om2Rep)
                        ? LGM_PART
                        : ((OM2_PART_S || OM2_PART_M || OM2_PART_B) && om2Rep ? OM2_TK(OM2_PART)
                                                                              : 0);
                const int om2SvDDS = pDDS, om2SvDDD = pDDD;
                if (om2Rep) {
                    if (OM2_TK(OM2_DDS) > 0 && !(mqT && !MQG(8))) {
                        if (OM2_DDSC == 7 && OM2_DDSN == 0 && OM2_DDSX == 0)
                            pDDS = OM2_TK(OM2_DDS);
                        else
                            om2WideDDS = OM2_TK(OM2_DDS);
                    }
                    if (HVB_DDS > 0 && hvbH)
                        pDDS = HVB_DDS;
                    if (OM2_TK(OM2_DDD) > 0)
                        pDDD = OM2_TK(OM2_DDD);
                }
                const int om2Bk = om2Rep && (OM2_TK(OM2_BKA) > 0 || OM2_TK(OM2_BKB) > 0);
                if (RQ_PART || (SM_PART && smT))
                    rqSelect(Pc, c);
                else if (om2Pm)
                    om2PartSelect(Pc, c, tauAE, om2Pm);
                else if (smT && (SM_RCH || SM_RCT > 1))
                    smRepairCands(Pc, c, tauAE);
                else if (om2Bk)
                    om2BestOf(Pc, c, tauAE);
                else
                    buildOverlapReconstruction();
                pDDS = om2SvDDS;
                pDDD = om2SvDDD;
                om2WideDDS = 0;
                om2Rep = 0;
                if (RBK > 0 && RBKW > 0 && N >= RBKN) {
                    ll wk = (multiplyNonnegative(N + omSteps, RBK) >> 5) + 1;
                    wCredit -= wk;
                    if (wCredit < 0)
                        wCredit = 0;
                    wRb = wk;
                    wCap = wk << 1;
                }
                int Mn = omM;
                ll Pn = omP;
                ll gain = Pc - Pn;
                if (RQ_ALW || svWarmForce ||
                    (gain > 0 &&
                     (Mn <= 0 || multiplyNonnegative(multiplyNonnegative(gain, 11),
                                                     multiplyNonnegative(tauAE, N - c)) >
                                     multiplyNonnegative(multiplyNonnegative(Mn, 7),
                                                         multiplyNonnegative(N, N) << 9)))) {
                    int rqC0 = 0;
                    if (RQ_UPD || (HC_RV && N >= HC_RVN && (MD_RVHI == 0 || N <= MD_RVHI) &&
                                   !(BF_RVX && N > NM && !(BF_RVBK & 2)))) {
                        if (xlsSBon) {
                            for (int w = 0; w < NW; w++) {
                                ull m = xlsSB[w];
                                while (m) {
                                    const int i = (w << 6) + __builtin_ctzll(m);
                                    m &= m - 1;
                                    rqC0 += publicGrid[i] != originalValue[i];
                                }
                            }
                        } else
                            for (int i = 0; i < N; i++)
                                rqC0 += changeStamp[i] == operationStamp &&
                                        publicGrid[i] != originalValue[i];
                    }
                    applyReconstruction();
                    mdRbOp = 1;
                    sinceRb = 0;
                    if (blRQ_POLR && !(MD_NOPOL && N > MNLO && N <= MNHI)) {
                        int ph = blRQ_PH;
                        if (HZP & 2) {
                            int hh = currentHorizon();
                            if (ph > hh)
                                ph = hh;
                        }
                        ll thr = divideNonnegative(
                            multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                            multiplyNonnegative(multiplyNonnegative(11, ph), N - c));
                        rqActM = RQ_PACTM;
                        rqActR = RQ_PACT;
                        if (RQ_PACTM == 1) {
                            for (int t = 0; t < typeSlotCount; t++)
                                rqChg[t] = 0;
                            for (int i = 0; i < N; i++)
                                rqChg[slotType[i]] += changeStamp[i] == operationStamp &&
                                                      publicGrid[i] != originalValue[i];
                        }
                        rqWork = 0;
                        const int pbud = N <= NT ? RQ_PBUDS : (N > NM ? blPBUD16 : RQ_PBUD);
                        if (pbud > 0) {
                            rqOrd.clear();
                            for (int t = 0; t < typeSlotCount; t++) {
                                int sc = typeSize[t];
                                if (sc < 3 || F[t] == 0 || !(t || (blRQ_POLR & 2)))
                                    continue;
                                ll r = rv[t];
                                rqEx[t] =
                                    (t ? PtC[t] : P0c) -
                                    multiplyNonnegative(multiplyNonnegative(r, sc - r) << 1, F[t]);
                                rqOrd.push_back(t);
                            }
                            sort(rqOrd.begin(), rqOrd.end(), [](int a, int b) {
                                return rqEx[a] > rqEx[b] || (rqEx[a] == rqEx[b] && a < b);
                            });
                            ll bud = N > NM && N > NT ? (multiplyNonnegative(N, pbud) >> 4)
                                                      : multiplyNonnegative(N, pbud);
                            for (int k = 0; k < (int)rqOrd.size() && rqWork < bud; k++) {
                                int t = rqOrd[k];
                                bool big = (typeSize[t] << RQ_PBSH) > N;
                                int pw = big ? blRQ_PWB : blRQ_PW;
                                if (pw > 0)
                                    relat(t, pw, thr);
                            }
                        } else
                            for (int it = 0; it < RQ_PIT; it++)
                                for (int t = 0; t < typeSlotCount; t++)
                                    if (typeSize[t] >= 3 && (t || (blRQ_POLR & 2)) &&
                                        (RQ_PACTM != 1 || rqChg[t] > 0)) {
                                        bool big = (typeSize[t] << RQ_PBSH) > N;
                                        int pw = big ? blRQ_PWB : blRQ_PW;
                                        if (pw > 0)
                                            relat(t, pw, thr);
                                    }
                        rqActM = 0;
                        rqActR = RQ_ACT;
                        if (RQ_UPD) {
                            Pn = totalLayoutPenalty();
                            int c1 = 0;
                            for (int i = 0; i < N; i++)
                                c1 += changeStamp[i] == operationStamp &&
                                      publicGrid[i] != originalValue[i];
                            Mn = c1 - rqC0;
                        }
                    }
                    if (HC_RV > 0 && N >= HC_RVN && (MD_RVHI == 0 || N <= MD_RVHI) &&
                        !(LGM_NORV > 0 && lgmL)) {
                        int rh = sdyR((BF_RVH >= 0 && N > NM) ? BF_RVH : HC_RVH);
                        if (HC_RVHC) {
                            int hh = currentHorizon();
                            if (rh > hh)
                                rh = hh;
                        }
                        ll thr = divideNonnegative(
                            multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                            multiplyNonnegative(multiplyNonnegative(11, rh), N - c));
                        hcRevertLS(
                            N > NM
                                ? (multiplyNonnegative(N, (HVB_RVB > 0 && hvbH) ? HVB_RVB
                                                                                : L_HC_RVB16) >>
                                   6)
                                : (multiplyNonnegative(
                                       N, (LGM_RVB > 0 && lgmL) ? LGM_RVB
                                          : (SM_RVB > 0 && smT)
                                              ? SM_RVB
                                              : (OM2_TK(OM2_RVB) > 0 ? OM2_TK(OM2_RVB) : HC_RVB)) >>
                                   2),
                            thr);
                        {
                            const bool useP = N <= NM || (BF_RVBK & 1);
                            ll Prv = (BF_RVX && !useP) ? 0 : totalLayoutPenalty();
                            if (useP)
                                Pn = Prv;
                            if (N <= NM || (BF_RVBK & 2)) {
                                int c1 = 0;
                                for (int i = 0; i < N; i++)
                                    c1 += changeStamp[i] == operationStamp &&
                                          publicGrid[i] != originalValue[i];
                                Mn = c1 - rqC0;
                            }
                        }
                    }
                    if (BO_RPR && N >= BO_NMIN) {
                        ll thr = divideNonnegative(
                            multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                            multiplyNonnegative(multiplyNonnegative(11, BO_RPRH), N - c));
                        totalLayoutPenalty();
                        rqOrd.clear();
                        for (int t = 1; t < typeSlotCount; t++) {
                            int sc = typeSize[t];
                            if (sc < 3 || F[t] == 0)
                                continue;
                            ll r = rv[t];
                            rqEx[t] = PtC[t] - multiplyNonnegative(
                                                   multiplyNonnegative(r, sc - r) << 1, F[t]);
                            rqOrd.push_back(t);
                        }
                        sort(rqOrd.begin(), rqOrd.end(), [](int a, int b) {
                            return rqEx[a] > rqEx[b] || (rqEx[a] == rqEx[b] && a < b);
                        });
                        ll bud = multiplyNonnegative(N, BO_RPR), used = 0;
                        int sc0 = seedCap;
                        seedCap = 0;
                        for (int k = 0; k < (int)rqOrd.size() && used < bud; k++) {
                            int t = rqOrd[k];
                            used += typeSize[t] + typeSize[0];
                            relx4(t, 2, thr);
                        }
                        seedCap = sc0;
                        Pn = totalLayoutPenalty();
                    }
                    const int om2Pol = OM2_TK(OM2_POL) >= 0 ? OM2_TK(OM2_POL) : pRBPOL;
                    if (om2Pol > 0) {
                        thrM = divideNonnegative(
                            multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                            multiplyNonnegative(multiplyNonnegative(11, currentHorizon()), N - c));
                        seedCap = N << 2;
                        for (int i = 0; i < N; i++)
                            if (changeStamp[i] == operationStamp &&
                                publicGrid[i] != originalValue[i])
                                pushSeed(i);
                        runLocalSearch((int)multiplyNonnegative(Mn > 0 ? Mn : 1, om2Pol));
                        Pn = totalLayoutPenalty();
                    }
                    if (SDY_RSA > 0 && smT) {
                        const int rh_ = SDY_RSH > 0 ? SDY_RSH : tauAE;
                        ll thr_ = divideNonnegative(
                            multiplyNonnegative(multiplyNonnegative(N, N), 7) << 9,
                            multiplyNonnegative(multiplyNonnegative(11, rh_), N - c));
                        sdyAnneal(multiplyNonnegative(N, SDY_RSA) >> 4, thr_, SDY_RSW, SDY_RST);
                        Pn = totalLayoutPenalty();
                        int c1 = 0;
                        for (int i = 0; i < N; i++)
                            c1 += changeStamp[i] == operationStamp &&
                                  publicGrid[i] != originalValue[i];
                        Mn = c1 - rqC0;
                    }
                    for (int t = 0; t < typeSlotCount; t++)
                        hcT[t] = 0;
                }
                rbExcess = Pn - Pm;
                if (rbExcess < 0)
                    rbExcess = 0;
                rbM = Mn < 1 ? 1 : Mn;
                if (VC_TV0 != 16 && N > NM)
                    vcVacBase = r2VacExcess();
                if (pRBMF > 0) {
                    ll fl = multiplyNonnegative(N, pRBMF) >> 6;
                    if (rbM < fl)
                        rbM = fl;
                }
                accEx = 0;
                lastEx = 0;
                lastChk = sinceRb;
            }
        }
    }
    sdyHcur = 1;
    if (MD_V0MN && MND && MNPOS == 1 && N > MNLO && N <= MNHI && N > c && ehV0k != 16) {
        ehV0k = 16;
        setType(0);
        typePenaltyDirty[0] = 1;
    }
    if (MND && MNPOS == 1 && N > MNLO && N <= MNHI && N > c)
        mnRun(x, c);
    if (HVB_MN && hvbX && MND && N > MNHI && N > c && ((add ? 1 : 2) & HVB_MN) &&
        c >= (N >> (add ? HVB_MNCA : HVB_MNCR))) {
        if (HVB_MNV0 && ehV0k != 16) {
            ehV0k = 16;
            setType(0);
            typePenaltyDirty[0] = 1;
        }
        mnRun(x, c);
    }
    if (SM_MN2 > 0 && smT && MND && N > c) {
        smNoCredit = 1;
        for (int r = 0; r < SM_MN2; r++)
            mnRun(x, c);
        smNoCredit = 0;
    }
    if (MQ_MN2 > 0 && mqT && MND && N > c) {
        smNoCredit = 1;
        for (int r = 0; r < MQ_MN2; r++)
            mnRun(x, c);
        smNoCredit = 0;
    }
    if (SM_SA > 0 && smT && N > c && !svWarming)
        smAnneal(c);
    if (ehV0k != 16) {
        ehV0k = 16;
        setType(0);
        typePenaltyDirty[0] = 1;
    }
}
