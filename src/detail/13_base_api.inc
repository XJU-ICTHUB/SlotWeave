// 主引擎初始化与增删入口。维护稀疏服务 ID 的内部索引，对实际可执行数量进行截断，并输出当前布局。
// Included in fixed order by solution.cpp.

void init0(int n, const vector<pair<int, int>> &services);
void apply_add(int id, int count);
void apply_remove(int id, int count);
int svCnt(int id) {
    auto it = typeIndex.find(id);
    return it == typeIndex.end() ? 0 : typeSize[it->second];
}
void svRem(int id, int c) {
    int s = svCnt(id);
    if (s <= 0)
        return;
    if (c > s)
        c = s;
    if (c < 1)
        c = 1;
    apply_remove(id, c);
}
void svAdd(int id, int c) {
    if (vacancyCount <= 0)
        return;
    if (c > vacancyCount)
        c = vacancyCount;
    if (c < 1)
        c = 1;
    apply_add(id, c);
}
void svWarmOps() {
    int X = 0, sX = 0, Y = 0, sY = 0;
    for (int t = 1; t < typeSlotCount; t++) {
        if (typeSize[t] <= 0 || !typeIndex.count(serviceId[t]))
            continue;
        if (typeSize[t] > sX) {
            Y = X;
            sY = sX;
            X = serviceId[t];
            sX = typeSize[t];
        } else if (typeSize[t] > sY) {
            Y = serviceId[t];
            sY = typeSize[t];
        }
    }
    int Z = 0x7fffff00;
    while (typeIndex.count(Z))
        Z--;
    int Z2 = Z - 1;
    while (typeIndex.count(Z2))
        Z2--;
    if (SV_WARM == 1) {
        svWarmForce = 1;
        if (sX >= 4)
            apply_remove(X, sX >> 1);
        if (svCnt(X) >= 2)
            apply_remove(X, 1);
        if (vacancyCount >= 4)
            apply_add(Z, vacancyCount >> 2);
        if (vacancyCount >= 2)
            apply_add(X, 1);
        if (vacancyCount >= 8)
            apply_add(X, vacancyCount >> 2);
        if (vacancyCount >= 2)
            apply_add(Z, 1);
        if (typeIndex.count(Z))
            apply_remove(Z, 1);
        if (typeIndex.count(Z))
            apply_remove(Z, typeSize[typeIndex[Z]]);
        if (typeIndex.count(X) && typeSize[typeIndex[X]] >= 3)
            apply_remove(X, 2);
        svWarmForce = 0;
        return;
    }
    if (X) {
        svRem(X, 1);
        svRem(X, 2);
        svRem(X, (svCnt(X) >> 5) + 1);
    }
    if (Y)
        svRem(Y, (sY >> 1) + 1);
    svWarmForce = 1;
    if (X)
        svRem(X, svCnt(X) >> 1);
    svWarmForce = 0;
    svAdd(Z, vacancyCount >> 2);
    svAdd(Z2, 3);
    if (X) {
        svAdd(X, 1);
        svAdd(X, 5);
    }
    svWarmForce = 1;
    if (Y)
        svAdd(Y, vacancyCount >> 2);
    else
        svAdd(Z2, vacancyCount >> 2);
    svWarmForce = 0;
    svAdd(Z, (vacancyCount >> 3) + 1);
    svAdd(Z2, 17);
    svRem(Z, svCnt(Z));
    svRem(Z2, 1);
    svRem(Z2, 9);
    svWarmForce = 1;
    svRem(Z2, svCnt(Z2));
    svWarmForce = 0;
    if (X)
        svRem(X, 3);
    svAdd(Z, 2);
    svRem(Z, 2);
}
void init(int n, const vector<pair<int, int>> &services) {
    vcInInit = 1;
    if (SV_WARM && n > 100) {
        svWarming = 1;
        init0(n, services);
        svWarmOps();
        svWarming = 0;
    }
    init0(n, services);
    vcInInit = 0;
}
void init0(int n, const vector<pair<int, int>> &services) {
    N = n;
    shCbar16 = 0;
    if (MD_RESET) {
        ehMnCredit = EH_MNC0;
        ehCbar16 = 0;
    }
    if (HVB_CR0 > 0 && n > MNHI)
        ehMnCredit = multiplyNonnegative(n, HVB_CR0);
    sqPreCred = SQ_PRECAP;
    tsCbar16 = 0;
    vcCbar16 = 0;
    vcVacBase = -1;
    iqRng = 0x9E3779B97F4A7C15ULL;
    smRng = 0x2545F4914F6CDD1DULL;
    if (SV_WARM)
        hzRng = 88172645463325252ULL;
    NW = (N + 63) >> 6;
    NS = (NW + 63) >> 6;
    xlsSBon = N > MNLO && N <= MNHI;
    for (int w = 0; w <= NW; w++)
        xlsSB[w] = 0;
    configureWorkBudgets();
    if (MD_RESET && MQ_MNC0 > 0 && mqT)
        ehMnCredit = MQ_MNC0;
    publicGrid.assign(N, 0);
    for (int i = 0; i < N + 64 && i < MAXN; i++) {
        slotType[i] = 0;
        nextSame[i] = 0;
        prevSame[i] = 0;
        changeStamp[i] = 0;
        originalValue[i] = 0;
        inq[i] = 0;
    }
    for (int w = 0; w <= NW; w++)
        vb[w] = 0;
    for (int w = 0; w < 4; w++)
        vs[w] = 0;
    typeIndex.clear();
    freeList.clear();
    nSeeds = 0;
    if (!selTabReady)
        buildSelTab();
    placement_dp::HSH = 0;
    while (((ll)(N << 1) >> placement_dp::HSH) >= 1024)
        placement_dp::HSH++;
    typeIndex[0] = 0;
    typeSlotCount = 1;
    for (int t = 0; t < MAXT; t++) {
        typePenaltyDirty[t] = 1;
        hcT[t] = 0;
        rmK[t] = 16;
    }
    serviceId[0] = 0;
    typeSize[0] = 0;
    F[0] = 0;
    qv[0] = 0;
    rv[0] = 0;
    typeHead[0] = -1;
    operationStamp = 0;
    operationCount = 0;
    hugeRun = 0;
    hugeStk = 0;
    sdyTw = 16;
    sdyHf = 16;
    sdyHr = 16;
    sdyHcur = 1;
    int used = 0;
    unordered_map<int, int> c0;
    for (auto &p : services) {
        if (p.second > 0 && p.first != 0 && used + p.second <= N) {
            c0[p.first] += p.second;
            used += p.second;
        }
    }
    vector<pair<int, int>> ty;
    for (auto &p : c0)
        ty.push_back({p.second, p.first});
    vacancyCount = N - used;
    ty.push_back({vacancyCount, 0});
    buildInitialLayout(ty);
    for (auto &p : c0) {
        int t = getIdx(p.first);
        typeSize[t] = p.second;
    }
    typeSize[0] = vacancyCount;
    for (int i = 0; i < N; i++) {
        slotType[i] = typeIndex[publicGrid[i]];
        if (slotType[i] == 0)
            vbSet(i);
    }
    if (TBITS)
        for (int i = 0; i < N; i++)
            if (slotType[i])
                TBSET(slotType[i], i);
    vector<int> lastOf(typeSlotCount, -1), firstOf(typeSlotCount, -1);
    for (int i = 0; i < N; i++) {
        int t = slotType[i];
        if (firstOf[t] < 0)
            firstOf[t] = i;
        else {
            nextSame[lastOf[t]] = i;
            prevSame[i] = lastOf[t];
        }
        lastOf[t] = i;
    }
    for (int t = 0; t < typeSlotCount; t++) {
        typeHead[t] = firstOf[t];
        if (firstOf[t] >= 0) {
            nextSame[lastOf[t]] = firstOf[t];
            prevSame[firstOf[t]] = lastOf[t];
        }
        setType(t);
    }
    if (pINITOM && N > 3) {
        operationStamp = 1;
        omHV = 0;
        buildOverlapReconstruction();
        if (IQK > 1 && !svWarming) {
            ll bestP = omP;
            for (int i = 0; i < N; i++)
                iqBestNT[i] = rbNTa[i];
            int nty = 0;
            for (int t = 0; t < typeSlotCount; t++)
                if (typeSize[t] > 0)
                    nty++;
            int K = nty < IQK ? nty : IQK;
            for (int a = 0; a < K; a++)
                for (int b = a + 1; b < K; b++) {
                    iqSA = a;
                    iqSB = b;
                    buildOverlapReconstruction();
                    if (omP < bestP) {
                        bestP = omP;
                        for (int i = 0; i < N; i++)
                            iqBestNT[i] = rbNTa[i];
                    }
                }
            iqSA = -1;
            iqSB = -1;
            for (int i = 0; i < N; i++)
                rbNTa[i] = iqBestNT[i];
        }
        applyReconstruction();
    }
    if (pINITB > 0 && N > 3 && !svWarming) {
        operationStamp = 1;
        thrM = 0;
        seedCap = N << 2;
        for (int i = 0; i < N; i++)
            pushSeed(i);
        runLocalSearch((int)multiplyNonnegative(pINITB, N));
        operationStamp = 2;
    }
    if (N > 3 && !svWarming && (IQQ || IQM > 0 || IQW > 0 || IQSA > 0)) {
        int op0 = operationStamp;
        operationStamp = 1;
        polishInitialLayout();
        if (IQSA > 0 && N <= IQSAN) {
            const bool mdI = N > MNLO && N <= MNHI;
            ll it = multiplyNonnegative((mdI && MD_IQSA > 0) ? MD_IQSA : IQSA, N);
            const ll cap = (mdI && MD_IQCAP > 0) ? MD_IQCAP : IQCAP;
            if (it > cap)
                it = cap;
            const int nsr = (mdI && MD_IQSR > 0) ? MD_IQSR : IQSR;
            ll bestP = totalLayoutPenalty();
            for (int i = 0; i < N; i++)
                iqBestNT[i] = slotType[i];
            for (int r = 0; r < nsr; r++) {
                annealInitialLayout(divideNonnegative(it, nsr), IQAW);
                polishInitialLayout();
                ll P = totalLayoutPenalty();
                if (P < bestP) {
                    bestP = P;
                    for (int i = 0; i < N; i++)
                        iqBestNT[i] = slotType[i];
                } else if (IQSRB) {
                    for (int i = 0; i < N; i++)
                        rbNTa[i] = iqBestNT[i];
                    applyReconstruction();
                }
            }
            if (totalLayoutPenalty() > bestP) {
                for (int i = 0; i < N; i++)
                    rbNTa[i] = iqBestNT[i];
                applyReconstruction();
            }
        }
        operationStamp = op0 > 1 ? op0 : 1;
    }
    if (TIN > 0 && N <= TIN && N > 1) {
        operationStamp = 3;
        tinyInit(TIR);
        operationStamp = 4;
    }
    rbExcess = totalLayoutPenalty() - minimumPossiblePenalty();
    if (rbExcess < 0)
        rbExcess = 0;
    rbM = (N <= TS_RBMN ? (N >> TS_RBM0) : (N >> 1)) + 1;
    sinceRb = 0;
    accEx = 0;
    lastEx = 0;
    lastChk = 0;
    hvbHr = 0;
    hvbVol = 0;
    wRb = RBKF > 0 ? ((ll)RBKF << 6) : (multiplyNonnegative(N, RBK) >> 4) + 1;
    wCap = wRb << 1;
    wCredit = wRb;
}
void apply_add(int id, int count) {
    operationCount++;
    if (count <= 0 || vacancyCount <= 0 || id == 0)
        return;
    int c = count < vacancyCount ? count : vacancyCount;
    int x = getIdx(id);
    processOperation(x, 1, c);
    vacancyCount -= c;
}
void apply_remove(int id, int count) {
    operationCount++;
    auto it = typeIndex.find(id);
    if (it == typeIndex.end() || count <= 0 || id == 0)
        return;
    int x = it->second;
    int oldS = typeSize[x];
    if (oldS <= 0)
        return;
    int c = count < oldS ? count : oldS;
    processOperation(x, 0, c);
    vacancyCount += c;
    if (typeSize[x] == 0) {
        typeIndex.erase(it);
        freeList.push_back(x);
    }
}
const vector<int> &grid() {
    return RVSTD(publicGrid);
}
