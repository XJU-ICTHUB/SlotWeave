// 初始化后的局部改进。以间隔代价的精确局部差值驱动交换、迁移和退火，所有搜索都有工作上限。
// Included in fixed order by solution.cpp.

void iqPolish(int W, ll budget) {
    if (W > (N >> 1) - 1)
        W = (N >> 1) - 1;
    if (W < 1)
        return;
    for (;;) {
        int imp = 0;
        for (int i = 0; i < N; i++) {
            for (int d = 1; d <= W; d++) {
                int j = i + d;
                if (j >= N)
                    j -= N;
                int a = slotType[i], b = slotType[j];
                if (a == b)
                    continue;
                budget--;
                ll da = dMoveW(a, i, j);
                if (da == INVALID)
                    continue;
                ll db = dMoveW(b, j, i);
                if (db == INVALID)
                    continue;
                if (da + db < 0) {
                    doSwap(i, j);
                    imp++;
                }
            }
            if (budget <= 0)
                return;
        }
        if (!imp)
            return;
    }
}
void iqReloc(int W, ll budget) {
    for (;;) {
        int imp = 0;
        for (int i = 0; i < N; i++) {
            int a = slotType[i];
            int sa = typeSize[a];
            if (sa < 2 || F[a] == 0)
                continue;
            int L = prvT(i, a), R = nxtT(i, a);
            int gl = sa == 2 ? N : dist(L, i) + dist(i, R);
            int h1 = gl >> 1;
            int m = L + h1;
            if (m >= N)
                m -= N;
            ll best = 0;
            int bj = -1;
            for (int d = -W; d <= W; d++) {
                int j = m + d;
                if (j >= N)
                    j -= N;
                else if (j < 0)
                    j += N;
                int b = slotType[j];
                if (b == a)
                    continue;
                budget--;
                ll da = dMoveW(a, i, j);
                if (da == INVALID || da >= best)
                    continue;
                ll db = dMoveW(b, j, i);
                if (db == INVALID)
                    continue;
                if (da + db < best) {
                    best = da + db;
                    bj = j;
                }
            }
            if (bj >= 0) {
                doSwap(i, bj);
                imp++;
            }
            if (budget <= 0)
                return;
        }
        if (!imp)
            return;
    }
}
ull iqRng = 0x9E3779B97F4A7C15ULL;
SP2_I ull iqRand() {
    iqRng ^= iqRng << 13;
    iqRng ^= iqRng >> 7;
    iqRng ^= iqRng << 17;
    return iqRng;
}
SP2_I int iqBelow(int n) {
    const ull m = ~0ULL >> __builtin_clzll((ull)n);
    for (;;) {
        int v = (int)(iqRand() & m);
        if (v < n)
            return v;
    }
}
ll iqDelta(int i, int j) {
    int a = slotType[i], b = slotType[j];
    if (a == b)
        return INVALID;
    ll da = dMoveW(a, i, j);
    if (da == INVALID)
        return INVALID;
    ll db = dMoveW(b, j, i);
    if (db == INVALID)
        return INVALID;
    return da + db;
}
int iqPartner(int i, int W) {
    if (iqRand() & 1) {
        int a = slotType[i];
        int sa = typeSize[a];
        if (sa >= 2) {
            int L = prvT(i, a), R = nxtT(i, a);
            int gl = sa == 2 ? N : dist(L, i) + dist(i, R);
            int m = L + (gl >> 1) + iqBelow((W << 1) + 1) - W;
            while (m >= N)
                m -= N;
            while (m < 0)
                m += N;
            return m;
        }
    }
    int d = iqBelow(W) + 1;
    int j = (iqRand() & 2) ? i + d : i - d;
    if (j >= N)
        j -= N;
    else if (j < 0)
        j += N;
    return j;
}
// 初始化阶段的受限退火搜索，用于跳出单纯交换下降的局部最优。
void annealInitialLayout(ll iters, int W) {
    if (W > (N >> 1) - 1)
        W = (N >> 1) - 1;
    if (W < 1 || iters <= 0)
        return;
    vector<ll> smp;
    for (int k = 0; k < 2000; k++) {
        int i = iqBelow(N), j = iqPartner(i, W);
        ll d = iqDelta(i, j);
        if (d != INVALID && d > 0)
            smp.push_back(d);
    }
    if (smp.empty())
        return;
    sort(smp.begin(), smp.end());
    ll t0 = smp[smp.size() >> IQT0];
    ll seg = iters >> 8;
    if (seg < 1)
        seg = 1;
    ll thr = t0, dthr = t0 >> 8;
    ll cnt = 0;
    for (ll k = 0; k < iters; k++) {
        if (++cnt >= seg) {
            cnt = 0;
            thr -= dthr;
            if (thr < 0)
                thr = 0;
        }
        int i = iqBelow(N), j = iqPartner(i, W);
        ll d = iqDelta(i, j);
        if (d == INVALID)
            continue;
        if (d < thr || d < 0)
            doSwap(i, j);
    }
}
RVEC(int) iqQ;
RVEC(char) iqIn;
SP2_I void iqPush(int i) {
    if (i >= 0 && !iqIn[i]) {
        iqIn[i] = 1;
        iqQ.push_back(i);
    }
}
void iqQueueLS(int Wm, int Ww, ll budget) {
    if (Ww > (N >> 1) - 1)
        Ww = (N >> 1) - 1;
    if (Wm > (N >> 1) - 1)
        Wm = (N >> 1) - 1;
    iqQ.clear();
    iqIn.assign(N, 0);
    for (int i = 0; i < N; i++)
        iqPush(i);
    size_t h = 0;
    while (h < iqQ.size() && budget > 0) {
        int i = iqQ[h++];
        iqIn[i] = 0;
        if (h > (size_t)(N << 2)) {
            iqQ.erase(iqQ.begin(), iqQ.begin() + h);
            h = 0;
        }
        int a = slotType[i];
        int sa = typeSize[a];
        ll best = 0;
        int bj = -1;
        if (sa >= 2 && F[a] != 0 && Wm > 0) {
            int L = prvT(i, a), R = nxtT(i, a);
            int gl = sa == 2 ? N : dist(L, i) + dist(i, R);
            int m = L + (gl >> 1);
            if (m >= N)
                m -= N;
            for (int d = -Wm; d <= Wm; d++) {
                int j = m + d;
                if (j >= N)
                    j -= N;
                else if (j < 0)
                    j += N;
                int b = slotType[j];
                if (b == a)
                    continue;
                budget--;
                ll da = dMoveW(a, i, j);
                if (da == INVALID || da >= best)
                    continue;
                ll db = dMoveW(b, j, i);
                if (db == INVALID)
                    continue;
                if (da + db < best) {
                    best = da + db;
                    bj = j;
                }
            }
        }
        for (int d = -Ww; d <= Ww; d++) {
            if (d == 0)
                continue;
            int j = i + d;
            if (j >= N)
                j -= N;
            else if (j < 0)
                j += N;
            int b = slotType[j];
            if (b == a)
                continue;
            budget--;
            ll da = dMoveW(a, i, j);
            if (da == INVALID)
                continue;
            ll db = dMoveW(b, j, i);
            if (db == INVALID)
                continue;
            if (da + db < best) {
                best = da + db;
                bj = j;
            }
        }
        if (bj >= 0) {
            int b = slotType[bj];
            int La = prvT(i, a), Ra = nxtT(i, a), Lb = prvT(bj, b), Rb = nxtT(bj, b);
            doSwap(i, bj);
            iqPush(La);
            iqPush(Ra);
            iqPush(Lb);
            iqPush(Rb);
            iqPush(prvT(i, b));
            iqPush(nxtT(i, b));
            iqPush(prvT(bj, a));
            iqPush(nxtT(bj, a));
            iqPush(i);
            iqPush(bj);
        }
    }
    for (size_t k = h; k < iqQ.size(); k++)
        iqIn[iqQ[k]] = 0;
    iqQ.clear();
}
// 组合初始化阶段的交换与迁移改进，保持类型计数合法。
void polishInitialLayout() {
    if (IQQ) {
        iqQueueLS(IQM, IQW, multiplyNonnegative(IQB, N));
        return;
    }
    if (IQM > 0)
        iqReloc(IQM, multiplyNonnegative(IQB, N));
    if (IQW > 0)
        iqPolish(IQW, multiplyNonnegative(IQB, N));
    if (IQM > 0 && IQW > 0)
        iqReloc(IQM, multiplyNonnegative(IQB, N));
}
#define IQSR 1
#define IQSRB 1
} // namespace
