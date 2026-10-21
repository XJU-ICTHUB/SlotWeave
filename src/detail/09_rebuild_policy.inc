// 重构方案的选择和预算设置。比较完整或局部候选，并保留原引擎的当前状态决策和性能保护。
// Included in fixed order by solution.cpp.

// 构造完整的重叠保持重建；各层选择完成后形成合法网格。
void buildOverlapReconstruction() {
    const ll vcHV0 = omHV;
    const bool vcHVon = (VC_OMHV != 16 || VC_OMHVO != 16) &&
                        ((VC_OMHVT & (N > NM ? 2 : 1)) || ((SM_VCT & 1) && smT)) &&
                        !(VC_OMVR && vcInInit);
    const bool md2HVon =
        (MD2_OMHV != 16 || MD2_OMHVO != 16) && N <= NM && N > MD2_OMLO && !vcInInit &&
        (MD2_OMHVSH >= 16 || ((ll)typeSize[0] << 4) <= multiplyNonnegative(N, MD2_OMHVSH));
    const bool om2Cls_ = OM2_CLSON && om2Rep;
    om2Gam0 = blGAMMA;
    om2KeepM = HC_KEEP;
    om2KW = HC_KW;
    om2KR = HC_KR;
#define BQ_KEEPBX 0
    if (HVB_KEEP > 0 && om2Rep && hvbH)
        om2KeepM = HVB_KEEP;
    else if (om2Rep && OM2_TK(OM2_KEEP) > 0 &&
             (OM2_KEEPNX == 0 || N <= OM2_KEEPNX || (BQ_KEEPBX && N > NM))) {
        om2KeepM = OM2_TK(OM2_KEEP);
        if (OM2_TK(OM2_KW) > 0)
            om2KW = OM2_TK(OM2_KW);
        if (OM2_TK(OM2_KR) >= 0)
            om2KR = OM2_TK(OM2_KR);
    }
    om2Grel = (OM2_GRELON && om2Rep) ? OM2_TK(OM2_GREL) : 0;
    if (OM2_GRELON)
        for (int t = 0; t < typeSlotCount; t++)
            om2Placed[t] = 0;
    if (BG1_RELM)
        for (int t = 0; t <= typeSlotCount; t++)
            bg1RelM[t] = 0xFFFF;
    omTabT = -1;
    omSer++;
    omLam = multiplyNonnegative(lamFor(rqC), RQ_KL) >> 4;
    computeGood();
    omOrd.clear();
    omP = 0;
    omM = 0;
    for (int t = 0; t < typeSlotCount; t++)
        if (typeSize[t] > 0 && (!omPart || omIn[t]))
            omOrd.push_back(t);
    omFr.resize(N);
    omNf.resize(N);
    omHitS.resize(N);
    omPre.resize(N);
#define RB_XPRE 1
    const bool xpre = RB_XPRE && !omPart && !omOrd.empty();
    int xhits = 0;
    if (xpre) {
        sort(omOrd.begin(), omOrd.end(), [](int a, int b) {
            const ll ka = vcOmKey(a), kb = vcOmKey(b);
            return ka > kb || (ka == kb && a < b);
        });
        vcOmPos();
        if (iqSA >= 0 && iqSB < (int)omOrd.size()) {
            int tt = omOrd[iqSA];
            omOrd[iqSA] = omOrd[iqSB];
            omOrd[iqSB] = tt;
        }
        const int t0 = omOrd[0];
        int lastOv = 0, lastY = 0;
        const int op = operationStamp;
        for (int i = 0; i < N; i++) {
            int y = slotType[i];
            if (PREHIT && changeStamp[i] == op && publicGrid[i] != originalValue[i]) {
                int ov = originalValue[i];
                if (!BLF || ov != lastOv) {
                    auto it = typeIndex.find(ov);
                    lastY = it != typeIndex.end() ? it->second : -1;
                    lastOv = ov;
                }
                y = lastY;
            }
            omPre[i] = y;
            omFr[i] = i;
            int h = y == t0;
            omHitS[i] = h ? (unsigned short)1 : omGoodS[i];
            xhits += h;
        }
    } else {
        int lastOv = 0, lastY = 0;
        const int op = operationStamp;
        for (int i = 0; i < N; i++) {
            int y = slotType[i];
            if (PREHIT && changeStamp[i] == op && publicGrid[i] != originalValue[i]) {
                int ov = originalValue[i];
                if (!BLF || ov != lastOv) {
                    auto it = typeIndex.find(ov);
                    lastY = it != typeIndex.end() ? it->second : -1;
                    lastOv = ov;
                }
                y = lastY;
            }
            omPre[i] = y;
        }
    }
    if (omOrd.empty()) {
        for (int i = 0; i < N; i++)
            rbNTa[i] = slotType[i];
        return;
    }
    if (!xpre) {
        sort(omOrd.begin(), omOrd.end(), [](int a, int b) {
            const ll ka = vcOmKey(a), kb = vcOmKey(b);
            return ka > kb || (ka == kb && a < b);
        });
        vcOmPos();
        if (iqSA >= 0 && iqSB < (int)omOrd.size()) {
            int tt = omOrd[iqSA];
            omOrd[iqSA] = omOrd[iqSB];
            omOrd[iqSB] = tt;
        }
    }
    int nty = (int)omOrd.size();
    int n = 0;
    int t = omOrd[0];
    int hits = 0;
    if (xpre) {
        n = N;
        hits = xhits;
    } else if (omPart) {
        for (int i = 0; i < N; i++) {
            rbNTa[i] = slotType[i];
            if (!omIn[slotType[i]])
                continue;
            omFr[n] = i;
            int h = omPre[i] == t;
            omHitS[n] = h ? (unsigned short)1 : omGoodS[i];
            hits += h;
            n++;
        }
    } else
        for (int i = 0; i < N; i++) {
            omFr[n] = i;
            int h = omPre[i] == t;
            omHitS[n] = h ? (unsigned short)1 : omGoodS[i];
            hits += h;
            n++;
        }
    int q = 0;
    for (; q < nty; q++) {
        t = omOrd[q];
        int sc = typeSize[t];
        if (vcHVon)
            omHV = t == 0 ? (multiplyNonnegative(vcHV0, VC_OMHV) >> 4)
                          : (multiplyNonnegative(vcHV0, VC_OMHVO) >> 4);
        else if (md2HVon)
            omHV = t == 0
                       ? (multiplyNonnegative(vcHV0, MD2_OMHV) >> 4)
                       : (MD2_OMHVO != 16 ? (multiplyNonnegative(vcHV0, MD2_OMHVO) >> 4) : vcHV0);
        if (om2Cls_) {
            if (!vcHVon && !md2HVon)
                omHV = vcHV0;
            om2Layer(t);
        }
        if (q == nty - 1) {
            omTakeRest(t, n, false);
            omHV = vcHV0;
            blGAMMA = om2Gam0;
            return;
        }
        if (blQB > 0 && multiplyNonnegative(sc, blQB) <= n)
            break;
        if (omPart && RQ_PSPARSE)
            break;
        omLayerDense(t, sc, n, hits);
        if (RQ_KEEP)
            omMaybeKeep(t, sc, n, false);
        omTake(t, sc);
        if (OM2_GRELON) {
            om2Placed[t] = 1;
            if (om2Grel == 2)
                om2RelGood(t);
            if (BG1_RELM && om2Grel == 1)
                bg1RelM[t + 1] = 0;
        }
        int tn = omOrd[q + 1];
        int k0 = 0;
        for (int k = 1; k < sc; k++)
            if (omPos[k] < omPos[k - 1]) {
                k0 = k;
                break;
            }
        hits = 0;
        int m = 0, i = 0, kp = k0;
        for (int cntk = 0; cntk < sc; cntk++) {
            int pos = omPos[kp];
            kp++;
            if (kp >= sc)
                kp = 0;
            for (; i < pos; i++) {
                int cell = omFr[i];
                omNf[m] = cell;
                const int y_ = omPre[cell];
                int hh = y_ == tn;
                if (BG1_RELM)
                    omHitS[m] =
                        hh ? (unsigned short)1 : (unsigned short)(omGoodS[cell] & bg1RelM[y_ + 1]);
                else
                    omHitS[m] = hh ? (unsigned short)1
                                   : ((OM2_GRELON && om2Grel == 1 && y_ >= 0 && om2Placed[y_])
                                          ? (unsigned short)0
                                          : omGoodS[cell]);
                hits += hh;
                m++;
            }
            i = pos + 1;
        }
        for (; i < n; i++) {
            int cell = omFr[i];
            omNf[m] = cell;
            const int y_ = omPre[cell];
            int hh = y_ == tn;
            if (BG1_RELM)
                omHitS[m] =
                    hh ? (unsigned short)1 : (unsigned short)(omGoodS[cell] & bg1RelM[y_ + 1]);
            else
                omHitS[m] = hh ? (unsigned short)1
                               : ((OM2_GRELON && om2Grel == 1 && y_ >= 0 && om2Placed[y_])
                                      ? (unsigned short)0
                                      : omGoodS[cell]);
            hits += hh;
            m++;
        }
        omFr.swap(omNf);
        n = m;
    }
    omIdx.assign(N, -1);
    omRec.resize(n);
    const bool bg1rb = BG1_RELB && OM2_GRELON && om2Grel == 1;
    if (bg1rb) {
        bg1St.resize(typeSlotCount + 1);
        bg1Of.resize(typeSlotCount + 1);
        bg1Buf.resize(N + typeSlotCount + 1);
        auto ST = bg1St.data();
        auto OF = bg1Of.data();
        auto BF = bg1Buf.data();
        int acc = 0;
        for (int u = 0; u < typeSlotCount; u++) {
            ST[u] = acc;
            OF[u] = acc;
            acc += typeSize[u] + 1;
        }
        auto FR = omFr.data();
        auto PR = omPre.data();
        auto RC = omRec.data();
        auto IX = omIdx.data();
        auto GS = omGoodS.data();
        for (int i = 0; i < n; i++) {
            int cell = FR[i], y = PR[cell], g = GS[cell], tc = slotType[cell];
            IX[cell] = i;
            int pl = y >= 0 ? (int)om2Placed[y] : 0;
            RC[i] = (y < 0 ? (1 << 28) : (y << 2)) | (pl ? 0 : g);
            BF[OF[tc]] = cell;
            OF[tc] += (y == tc) & (g >> 1) & (pl ^ 1);
        }
    } else {
        for (int i = 0; i < n; i++) {
            int cell = omFr[i];
            omIdx[cell] = i;
            omRec[i] = (omPre[cell] < 0 ? (1 << 28) : (omPre[cell] << 2)) | (int)omGoodS[cell];
        }
        if (OM2_GRELON && om2Grel == 1) {
            auto FR = omFr.data();
            auto PR = omPre.data();
            auto RC = omRec.data();
            for (int i = 0; i < n; i++) {
                int y = PR[FR[i]];
                if (y >= 0 && om2Placed[y])
                    RC[i] &= ~2;
            }
        }
    }
    int blocked = 0;
    for (; q < nty; q++) {
        t = omOrd[q];
        int sc = typeSize[t];
        if (vcHVon)
            omHV = t == 0 ? (multiplyNonnegative(vcHV0, VC_OMHV) >> 4)
                          : (multiplyNonnegative(vcHV0, VC_OMHVO) >> 4);
        else if (md2HVon)
            omHV = t == 0
                       ? (multiplyNonnegative(vcHV0, MD2_OMHV) >> 4)
                       : (MD2_OMHVO != 16 ? (multiplyNonnegative(vcHV0, MD2_OMHVO) >> 4) : vcHV0);
        if (om2Cls_) {
            if (!vcHVon && !md2HVon)
                omHV = vcHV0;
            om2Layer(t);
        }
        if (q == nty - 1) {
            omTakeRest(t, n, true);
            omHV = vcHV0;
            blGAMMA = om2Gam0;
            return;
        }
        bool ok = false;
        int om2DdsSv = pDDS;
        if (om2WideDDS > 0) {
            const int cl = t == 0 ? 1 : (hcT[t] ? 2 : 4);
            if ((OM2_DDSC & cl) && (OM2_DDSN == 0 || sc <= OM2_DDSN) &&
                (OM2_DDSX == 0 || sc >= OM2_DDSX))
                pDDS = om2WideDDS;
        }
        if (((blocked + sc) << blBFR) <= n)
            ok = omLayerLazy(t, sc, n);
        if (!ok) {
            int m = 0;
            for (int i = 0; i < n; i++) {
                int cell = omFr[i], r = omRec[i], bl = r & 1;
                omNf[m] = cell;
                omRec[m] = r;
                omIdx[cell] = bl ? -1 : m;
                m += bl ^ 1;
            }
            omFr.swap(omNf);
            n = m;
            blocked = 0;
            if (!omLayerLazy(t, sc, n))
                omBres(sc, n);
        }
        pDDS = om2DdsSv;
        if (RQ_KEEP)
            omMaybeKeep(t, sc, n, true);
        if (om2KeepM)
            omKeepTry(t, sc, true);
        omTake(t, sc);
        for (int k = 0; k < sc; k++)
            omRec[omPos[k]] |= 1;
        blocked += sc;
        if (OM2_GRELON && om2Grel) {
            om2Placed[t] = 1;
            if (bg1rb) {
                if (q + 2 < nty) {
                    auto IX = omIdx.data();
                    auto RC = omRec.data();
                    auto BF = bg1Buf.data();
                    for (int k = bg1St[t], e = bg1Of[t]; k < e; k++) {
                        int ix = IX[BF[k]];
                        if (ix >= 0)
                            RC[ix] &= ~2;
                    }
                }
            } else
                om2Release(t);
        }
    }
    omHV = vcHV0;
    blGAMMA = om2Gam0;
}
#define RBPOL 0
#define RBMF 0
#define NT 0
#define MDQ_ZAC -1
#define MDQ_ZACR -1
#define MDQ_ZACX -1
#define MDM_ZAC -1
#define MDM_ZACR -1
#define MDM_ZACX -1
#define MDQ_BUDB -1
#define MDQ_BUDC -1
#define MDQ_TAU -1
#define MDQ_TAUA -1
#define MDQ_CHK -1
#define MDQ_MINGAP -1
#define MDQ_BIGSH -1
#define MDQ_DDS -1
#define MDQ_DDD -1
#define MDQ_TRIG -1
#define MDQ_LAM -1
#define MDQ_RBPOL -1
#define MDQ_RBMF -1
#define MDM_BUDB -1
#define MDM_BUDC -1
#define MDM_TAU -1
#define MDM_TAUA -1
#define MDM_CHK -1
#define MDM_MINGAP -1
#define MDM_BIGSH -1
#define MDM_DDS -1
#define MDM_DDD -1
#define MDM_TRIG -1
#define MDM_LAM -1
#define MDM_RBPOL -1
#define MDM_RBMF -1
#define MD2_ZLO 1000
#define MD2_BRLO 1000
#define MD2_BIGREM 0
#define MD2_BIGSH 0
#define MD2_TRK 0
#define MD2_BIGMIN -1
#define MD2S_CHK -1
#define MD2S_MINGAP -1
#define MD2S_TAU -1
#define MD2S_TAUA -1
#define MD2S_LAM -1
#define MD2S_BUDB -1
#define MD2S_BUDC -1
#define MD2S_RBPOL -1
// 集中配置当前规模下的搜索预算和候选窗口，不改变评分定义。
void configureWorkBudgets() {
    smT = N > SM_LO && N <= SM_HI;
    mqT = N > MQ_LO && N <= MQ_HI;
    if (N <= NT) {
        pBUDB = T_BUDB;
        pBUDC = T_BUDC;
        pBUDBB = T_BUDBB;
        pTAU = T_TAU;
        pTAUA = T_TAUA;
        pCHK = T_CHK;
        pMINGAP = T_MINGAP;
        pBIGSH = T_BIGSH;
        pDDS = T_DDS;
        pDDD = T_DDD;
        pINITB = T_INITB;
        pTRIG = T_TRIG;
        pLAM = T_LAM;
        pRBPOL = T_RBPOL;
        pZAC = T_ZAC;
        pZACR = T_ZACR;
        pRBMODE = T_RBMODE;
        pZACX = T_ZACX;
        pRBMF = T_RBMF;
        pINITOM = T_INITOM;
    } else if (N <= NQ) {
        pBUDB = Q_BUDB;
        pBUDC = Q_BUDC;
        pBUDBB = Q_BUDBB;
        pTAU = Q_TAU;
        pTAUA = Q_TAUA;
        pCHK = Q_CHK;
        pMINGAP = Q_MINGAP;
        pBIGSH = Q_BIGSH;
        pDDS = Q_DDS;
        pDDD = Q_DDD;
        pINITB = Q_INITB;
        pTRIG = Q_TRIG;
        pLAM = Q_LAM;
        pRBPOL = Q_RBPOL;
        pZAC = Q_ZAC;
        pZACR = Q_ZACR;
        pRBMODE = Q_RBMODE;
        pZACX = Q_ZACX;
        pRBMF = Q_RBMF;
        pINITOM = Q_INITOM;
    } else if (N <= NM) {
        pBUDB = M_BUDB;
        pBUDC = M_BUDC;
        pBUDBB = M_BUDBB;
        pTAU = M_TAU;
        pTAUA = M_TAUA;
        pCHK = M_CHK;
        pMINGAP = M_MINGAP;
        pBIGSH = M_BIGSH;
        pDDS = M_DDS;
        pDDD = M_DDD;
        pINITB = M_INITB;
        pTRIG = M_TRIG;
        pLAM = M_LAM;
        pRBPOL = M_RBPOL;
        pZAC = M_ZAC;
        pZACR = M_ZACR;
        pRBMODE = M_RBMODE;
        pZACX = M_ZACX;
        pRBMF = M_RBMF;
        pINITOM = M_INITOM;
    } else {
        pBUDB = BUDB;
        pBUDC = BUDC;
        pBUDBB = BUDBB;
        pTAU = TAU;
        pTAUA = TAUA;
        pCHK = CHK;
        pMINGAP = MINGAP;
        pBIGSH = BIGSH;
        pDDS = DDS;
        pDDD = DDD;
        pINITB = INITB;
        pTRIG = TRIG;
        pLAM = LAM;
        pRBPOL = RBPOL;
        pZAC = ZAC;
        pZACR = ZACR;
        pRBMODE = RBMODE;
        pZACX = ZACX;
        pRBMF = RBMF;
        pINITOM = INITOM;
    }
    if (N > MNLO && N <= NQ) {
        if (MDQ_BUDB >= 0)
            pBUDB = MDQ_BUDB;
        if (MDQ_BUDC >= 0)
            pBUDC = MDQ_BUDC;
        if (MDQ_TAU >= 0)
            pTAU = MDQ_TAU;
        if (MDQ_TAUA >= 0)
            pTAUA = MDQ_TAUA;
        if (MDQ_CHK >= 0)
            pCHK = MDQ_CHK;
        if (MDQ_MINGAP >= 0)
            pMINGAP = MDQ_MINGAP;
        if (MDQ_BIGSH >= 0)
            pBIGSH = MDQ_BIGSH;
        if (MDQ_DDS >= 0)
            pDDS = MDQ_DDS;
        if (MDQ_DDD >= 0)
            pDDD = MDQ_DDD;
        if (MDQ_TRIG >= 0)
            pTRIG = MDQ_TRIG;
        if (MDQ_LAM >= 0)
            pLAM = MDQ_LAM;
        if (MDQ_RBPOL >= 0)
            pRBPOL = MDQ_RBPOL;
        if (MDQ_RBMF >= 0)
            pRBMF = MDQ_RBMF;
        if (MDQ_ZAC >= 0)
            pZAC = MDQ_ZAC;
        if (MDQ_ZACR >= 0)
            pZACR = MDQ_ZACR;
        if (MDQ_ZACX >= 0)
            pZACX = MDQ_ZACX;
    }
    if (N > NQ && N <= MNHI) {
        if (MDM_BUDB >= 0)
            pBUDB = MDM_BUDB;
        if (MDM_BUDC >= 0)
            pBUDC = MDM_BUDC;
        if (MDM_TAU >= 0)
            pTAU = MDM_TAU;
        if (MDM_TAUA >= 0)
            pTAUA = MDM_TAUA;
        if (MDM_CHK >= 0)
            pCHK = MDM_CHK;
        if (MDM_MINGAP >= 0)
            pMINGAP = MDM_MINGAP;
        if (MDM_BIGSH >= 0)
            pBIGSH = MDM_BIGSH;
        if (MDM_DDS >= 0)
            pDDS = MDM_DDS;
        if (MDM_DDD >= 0)
            pDDD = MDM_DDD;
        if (MDM_TRIG >= 0)
            pTRIG = MDM_TRIG;
        if (MDM_LAM >= 0)
            pLAM = MDM_LAM;
        if (MDM_RBPOL >= 0)
            pRBPOL = MDM_RBPOL;
        if (MDM_RBMF >= 0)
            pRBMF = MDM_RBMF;
        if (MDM_ZAC >= 0)
            pZAC = MDM_ZAC;
        if (MDM_ZACR >= 0)
            pZACR = MDM_ZACR;
        if (MDM_ZACX >= 0)
            pZACX = MDM_ZACX;
    }
    if (MD2_BIGSH > 0 && N > MD2_BRLO && N <= NM)
        pBIGSH = MD2_BIGSH;
    if (N > MNLO && N <= MD2_SN) {
        if (MD2S_CHK >= 0)
            pCHK = MD2S_CHK;
        if (MD2S_MINGAP >= 0)
            pMINGAP = MD2S_MINGAP;
        if (MD2S_TAU >= 0)
            pTAU = MD2S_TAU;
        if (MD2S_TAUA >= 0)
            pTAUA = MD2S_TAUA;
        if (MD2S_LAM >= 0)
            pLAM = MD2S_LAM;
        if (MD2S_BUDB >= 0)
            pBUDB = MD2S_BUDB;
        if (MD2S_BUDC >= 0)
            pBUDC = MD2S_BUDC;
        if (MD2S_RBPOL >= 0)
            pRBPOL = MD2S_RBPOL;
    }
    if (N > NM) {
        blGAMMA = L_GAMMA;
        blHVK = L_HVK;
        blBFR = L_BFR;
        blQB = L_QB;
        blRQ_POLR = L_RQ_POLR;
        blRQ_PW = L_RQ_PW;
        blRQ_PWB = L_RQ_PWB;
        blRQ_PH = L_RQ_PH;
        blCCAPB = L_CCAPB;
        blSH_LSK = L_SH_LSK;
        blSH_LSH = L_SH_LSH;
        blPBUD16 = L_RQ_PBUD16;
    } else {
        blGAMMA = GAMMA;
        blHVK = HVK;
        blBFR = BFR;
        blQB = QB;
        blRQ_POLR = RQ_POLR;
        blRQ_PW = RQ_PW;
        blRQ_PWB = RQ_PWB;
        blRQ_PH = RQ_PH;
        blCCAPB = CCAPB;
        blSH_LSK = SH_LSK;
        blSH_LSH = SH_LSH;
        blPBUD16 = RQ_PBUD << 4;
    }
    if (N <= NQ || N <= NM) {
        placement_dp::zWHL = Q_ZWHL;
        placement_dp::zP0 = Q_ZP0;
        placement_dp::zP1 = Q_ZP1;
        placement_dp::zWS = Q_ZW_SMALL;
        placement_dp::zWM2 = Q_ZW_M2;
        placement_dp::zWR = Q_ZWR;
        for (int u = 0; u < 3; u++) {
            placement_dp::zWM2u[u] = Q_ZW_M2;
            placement_dp::zWMu[u] = ZW_MID;
            placement_dp::zWBu[u] = ZW_BIG;
        }
        if (N > MD2_ZLO) {
            placement_dp::zWS = MD2_ZWS;
            placement_dp::zWM2u[0] = MD2_ZWM2_N;
            placement_dp::zWMu[0] = MD2_ZWM_N;
            placement_dp::zWBu[0] = MD2_ZWB_N;
            placement_dp::zWM2u[1] = MD2_ZWM2_A;
            placement_dp::zWMu[1] = MD2_ZWM_A;
            placement_dp::zWBu[1] = MD2_ZWB_A;
            placement_dp::zWM2u[2] = MD2_ZWM2_R;
            placement_dp::zWMu[2] = MD2_ZWM_R;
            placement_dp::zWBu[2] = MD2_ZWB_R;
        }
    } else {
        placement_dp::zWHL = ZWHL;
        placement_dp::zP0 = ZP0;
        placement_dp::zP1 = ZP1;
        placement_dp::zWS = ZW_SMALL;
        placement_dp::zWM2 = ZW_M2;
        placement_dp::zWR = VC_LZWR;
        placement_dp::zWM2u[0] = VC_LZWM2_N;
        placement_dp::zWMu[0] = VC_LZWM_N;
        placement_dp::zWBu[0] = VC_LZWB_N;
        placement_dp::zWM2u[1] = VC_LZWM2_A;
        placement_dp::zWMu[1] = VC_LZWM_A;
        placement_dp::zWBu[1] = VC_LZWB_A;
        placement_dp::zWM2u[2] = VC_LZWM2_R;
        placement_dp::zWMu[2] = VC_LZWM_R;
        placement_dp::zWBu[2] = VC_LZWB_R;
    }
    if (mqT) {
        if (MQ_CHK > 0)
            pCHK = MQ_CHK;
        if (MQ_MINGAP >= 0)
            pMINGAP = MQ_MINGAP;
        if (MQ_TAU >= 0)
            pTAU = MQ_TAU;
        if (MQ_TAUA >= 0)
            pTAUA = MQ_TAUA;
        if (MQ_LAM >= 0)
            pLAM = MQ_LAM;
        if (MQ_DDS >= 0)
            pDDS = MQ_DDS;
        if (MQ_DDD >= 0)
            pDDD = MQ_DDD;
        if (MQ_BUDB >= 0)
            pBUDB = MQ_BUDB;
        if (MQ_BUDC >= 0)
            pBUDC = MQ_BUDC;
        if (MQ_RBPOL >= 0)
            pRBPOL = MQ_RBPOL;
        if (MQ_BIGSH >= 0)
            pBIGSH = MQ_BIGSH;
    }
    if (smT) {
        if (SM_ZWS > 0)
            placement_dp::zWS = SM_ZWS;
        if (SM_ZWM2 > 0)
            for (int u = 0; u < 3; u++)
                placement_dp::zWM2u[u] = SM_ZWM2;
        if (SM_ZWM > 0)
            for (int u = 0; u < 3; u++)
                placement_dp::zWMu[u] = SM_ZWM;
        if (SM_ZWHL > 0)
            placement_dp::zWHL = SM_ZWHL;
        if (SM_ZWR > 0)
            placement_dp::zWR = SM_ZWR;
        if (SM_CHK > 0)
            pCHK = SM_CHK;
        if (SM_MINGAP >= 0)
            pMINGAP = SM_MINGAP;
        if (SM_BUDB >= 0)
            pBUDB = SM_BUDB;
        if (SM_BUDC >= 0)
            pBUDC = SM_BUDC;
        if (SM_DDD > 0)
            pDDD = SM_DDD;
        if (SM_DDS > 0)
            pDDS = SM_DDS;
    }
}
#define RBK 0
#define OPW 64
#define RBKC 1
#define RBKW 0
#define RBKF 0
#define RBKB 0
#define RBKN 5000
#ifdef RQ_ALWAYS
#define RQ_ALW 1
#else
#define RQ_ALW 0
#endif
