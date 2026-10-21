// 分层初始布局与空位候选查询。在可用位置中展开均匀目标，并以位图快速定位允许放置的颗粒。
// Included in fixed order by solution.cpp.

// 依次在剩余位置中铺开各类型，得到合法的分层均匀初态。
void buildInitialLayout(vector<pair<int, int>> &ty) {
    sort(ty.begin(), ty.end(), [](const pair<int, int> &a, const pair<int, int> &b) {
        return a.first > b.first || (a.first == b.first && a.second < b.second);
    });
    vector<int> fr(N), nf;
    for (int i = 0; i < N; i++)
        fr[i] = i;
    for (auto &t : ty) {
        int s = t.first, n = (int)fr.size();
        if (s <= 0)
            continue;
        nf.clear();
        int acc = n >> 1;
        for (int i = 0; i < n; i++) {
            acc += s;
            if (acc >= n) {
                acc -= n;
                publicGrid[fr[i]] = t.second;
            } else
                nf.push_back(fr[i]);
        }
        fr.swap(nf);
    }
}
RVEC(int) pend, picks, xs;
RVEC(ll) gord;
int histG4[(MAXN << 2) + 32];
__attribute__((noinline)) ll fillCost(int v) {
    int L = prevVac(v);
    if (L == v || L < 0)
        return 0;
    int R = nextVac(v);
    return cst(0, dist(L, R)) - cst(0, dist(L, v)) - cst(0, dist(v, R));
}
int curWin = WIN;
bool fastPk = false;
#define CFAST 1000000
ll pxv = 0;
ll fillLB = 0;
int pickVac(int p, int lo, int span) {
    int best = -1;
    ll bv = 0;
    ll pen = 0;
    for (int d = 0; d <= curWin; d++) {
        if (best >= 0 && pen + fillLB >= bv)
            break;
        for (int sg = 0; sg < 2; sg++) {
            if (d == 0 && sg)
                break;
            int c = sg ? p - d : p + d;
            if (c >= N)
                c -= N;
            else if (c < 0)
                c += N;
            if (slotType[c] != 0)
                continue;
            if (lo >= 0 && dist(lo, c) >= span)
                continue;
            ll v = fillCost(c) + pen;
            if (best < 0 || v < bv) {
                bv = v;
                best = c;
            }
        }
        pen += pxv;
    }
    if (best >= 0)
        return best;
    int a = nextVac(p), b = prevVac(p);
    int da = a >= 0 ? dist(p, a) : N + 1, db = b >= 0 ? dist(b, p) : N + 1;
    bool ina = a >= 0 && (lo < 0 || dist(lo, a) < span);
    bool inb = b >= 0 && (lo < 0 || dist(lo, b) < span);
    if (ina && (!inb || da <= db))
        return a;
    if (inb)
        return b;
    return -1;
}
ll rxw = 0;
ll xcT[MAXN + 8];
int xcMax = 0;
void buildXcT(int x, int mx) {
    if (mx > N)
        mx = N;
    xcMax = mx;
    ll A = multiplyNonnegative(N, rxw), B = multiplyNonnegative(typeSize[x], rxw);
    ll v = -A;
    for (int g = 0; g <= mx; g++) {
        xcT[g] = (v < 0 ? -v : v) >> 10;
        v += B;
    }
}
__attribute__((noinline)) ll xcostSlow(int x, int g) {
    return multiplyNonnegative(cst(x, g), rxw) >> 10;
}
SP2_I ll xcostw(int x, int g) {
    return g <= xcMax ? xcT[g] : xcostSlow(x, g);
}
SP2_I ll fillCostW2(int c, ull wl, ull wh, int k) {
    int a = -1, b = -1;
    if (k >= 64) {
        int kk = k - 64;
        ull lm = kk ? (wh & ((1ULL << kk) - 1)) : 0;
        if (lm)
            a = kk - (63 - __builtin_clzll(lm));
        else if (wl)
            a = kk + 64 - (63 - __builtin_clzll(wl));
        ull rm = kk < 63 ? (wh >> (kk + 1)) : 0;
        if (rm)
            b = __builtin_ctzll(rm) + 1;
    } else {
        ull lm = wl & ((1ULL << k) - 1);
        if (lm)
            a = k - (63 - __builtin_clzll(lm));
        ull rm = k < 63 ? (wl >> (k + 1)) : 0;
        if (rm)
            b = __builtin_ctzll(rm) + 1;
        else if (wh)
            b = 64 - k + __builtin_ctzll(wh);
    }
    if (a < 0 || b < 0)
        return fillCost(c);
    return ctab0[a + b] - ctab0[a] - ctab0[b];
}
const int NOPICK = 1 << 20;
static inline __attribute__((always_inline)) int pickCore2(int p, int dp, int span, bool arc,
                                                           bool useX) {
    int W = curWin;
    int fmax = W, bmax = W;
    if (arc) {
        fmax = dp < span ? span - 1 - dp : -1;
        if (fmax > W)
            fmax = W;
        bmax = dp <= span ? dp - 1 : 0;
        if (bmax > W)
            bmax = W;
    }
    int base = p - 32;
    if (base < 0)
        base += N;
    ull w = bitsAt(base);
    int bestD = NOPICK;
    ll bv = 0;
    ll lb = fillLB;
    if (fmax >= 0 && ((w >> 32) & 1) && useX) {
        ull lm = w & 0xffffffffULL, rm = w >> 33;
        if (lm && rm) {
            int a = 32 - (63 - __builtin_clzll(lm)), b = __builtin_ctzll(rm) + 1;
            if (ctab0[a + b] - ctab0[a] - ctab0[b] == lb) {
                ll x0 = xcT[dp] + xcT[span - dp];
                bool okF = b > fmax || xcT[dp + b] + xcT[span - dp - b] >= x0;
                bool okB = a > bmax || xcT[dp - a] + xcT[span - dp + a] >= x0;
                if (okF && okB)
                    return 0;
            }
        }
    }
    if (fmax >= 0) {
        ull wf = w >> 32;
        ull m = wf & ((2ULL << fmax) - 1);
        if (m) {
            ull below = w & 0xffffffffULL;
            int prev = below ? (63 - __builtin_clzll(below)) - 32 : -64;
            while (m) {
                int d = __builtin_ctzll(m);
                m &= m - 1;
                ll xc = 0;
                if (useX) {
                    int dl = dp + d;
                    xc = xcT[dl] + xcT[span - dl];
                }
                if (bestD != NOPICK && d > 0 && xc + lb >= bv)
                    break;
                ull after = wf >> d >> 1;
                ll fc;
                if (prev > -64 && after) {
                    int a = d - prev, b = __builtin_ctzll(after) + 1;
                    fc = ctab0[a + b] - ctab0[a] - ctab0[b];
                } else {
                    int c = p + d;
                    if (c >= N)
                        c -= N;
                    fc = fillCost(c);
                }
                ll v = fc + xc;
                if (bestD == NOPICK || v < bv) {
                    bv = v;
                    bestD = d;
                }
                prev = d;
            }
        }
    }
    if (bmax >= 1) {
        ull m = (w >> (32 - bmax)) & ((1ULL << bmax) - 1);
        while (m) {
            int j = 63 - __builtin_clzll(m);
            m ^= 1ULL << j;
            int d = bmax - j;
            ll xc = 0;
            if (useX) {
                int dl = dp - d;
                xc = xcT[dl] + xcT[span - dl];
            }
            if (bestD != NOPICK && xc + lb >= bv)
                break;
            int k = 32 - d;
            ull lm = w & ((1ULL << k) - 1);
            ull rm = w >> (k + 1);
            ll fc;
            if (lm && rm) {
                int a = k - (63 - __builtin_clzll(lm)), b = __builtin_ctzll(rm) + 1;
                fc = ctab0[a + b] - ctab0[a] - ctab0[b];
            } else {
                int c = p - d;
                if (c < 0)
                    c += N;
                fc = fillCost(c);
            }
            ll v = fc + xc;
            if (bestD == NOPICK || v < bv) {
                bv = v;
                bestD = -d;
            }
        }
    }
    return bestD;
}
static inline __attribute__((always_inline)) int pickCoreW(int p, int dp, int span) {
    int W = curWin;
    int fmax = dp < span ? span - 1 - dp : -1;
    if (fmax > W)
        fmax = W;
    int bmax = dp <= span ? dp - 1 : 0;
    if (bmax > W)
        bmax = W;
    int base = p - 64;
    if (base < 0)
        base += N;
    ull wl = bitsAt(base), wh = bitsAt(p);
    ll lb = fillLB;
    if (fmax >= 0 && (wh & 1) && wl && (wh >> 1)) {
        int a = 64 - (63 - __builtin_clzll(wl)), b = __builtin_ctzll(wh >> 1) + 1;
        if (ctab0[a + b] - ctab0[a] - ctab0[b] == lb) {
            ll x0 = xcT[dp] + xcT[span - dp];
            bool okF = b > fmax || xcT[dp + b] + xcT[span - dp - b] >= x0;
            bool okB = a > bmax || xcT[dp - a] + xcT[span - dp + a] >= x0;
            if (okF && okB)
                return 0;
        }
    }
    int bestD = NOPICK;
    ll bv = 0;
    if (fmax >= 0) {
        ull m = wh & lowMask(fmax + 1);
        int prev = wl ? (63 - __builtin_clzll(wl)) - 64 : -100;
        while (m) {
            int d = __builtin_ctzll(m);
            m &= m - 1;
            int dl = dp + d;
            ll xc = xcT[dl] + xcT[span - dl];
            if (bestD != NOPICK && d > 0 && xc + lb >= bv)
                break;
            ull after = d < 63 ? wh >> (d + 1) : 0;
            ll fc;
            if (prev > -100 && after) {
                int a = d - prev, b = __builtin_ctzll(after) + 1;
                fc = ctab0[a + b] - ctab0[a] - ctab0[b];
            } else {
                int c = p + d;
                if (c >= N)
                    c -= N;
                fc = fillCost(c);
            }
            ll v = fc + xc;
            if (bestD == NOPICK || v < bv) {
                bv = v;
                bestD = d;
            }
            prev = d;
        }
    }
    if (bmax >= 1) {
        ull m = (wl >> (64 - bmax)) & lowMask(bmax);
        while (m) {
            int j = 63 - __builtin_clzll(m);
            m ^= 1ULL << j;
            int d = bmax - j;
            int dl = dp - d;
            ll xc = xcT[dl] + xcT[span - dl];
            if (bestD != NOPICK && xc + lb >= bv)
                break;
            int c = p - d;
            if (c < 0)
                c += N;
            ll v = fillCostW2(c, wl, wh, 64 - d) + xc;
            if (bestD == NOPICK || v < bv) {
                bv = v;
                bestD = -d;
            }
        }
    }
    return bestD;
}
#define BLF 1
static inline __attribute__((always_inline)) ull bitsAtN(int pos, int n_) {
    int w = pos >> 6, sh = pos & 63;
    ull v = sh ? ((vb[w] >> sh) | (vb[w + 1] << (64 - sh))) : vb[w];
    int rem = n_ - pos;
    if (rem < 64)
        v |= vb[0] << rem;
    return v;
}
__attribute__((noinline)) ll fillCost(int v);
const int PKSLOW = NOPICK + 1;
template <int W>
static inline __attribute__((always_inline)) int pick3(int dp, int span, ull w, ll lb, int thr) {
    int fmax = dp < span ? span - 1 - dp : -1;
    if (fmax > W)
        fmax = W;
    int bmax = dp <= span ? dp - 1 : 0;
    if (bmax > W)
        bmax = W;
    const ull lw = w & 0xffffffffULL, wf = w >> 32;
    int bestD = NOPICK;
    ll bv = 0;
    if (fmax >= 0) {
        ull m = wf & ((2ULL << fmax) - 1);
        int prev = lw ? (63 - __builtin_clzll(lw)) - 32 : -64;
        if (wf & 1) {
            ull rm = wf >> 1;
            if (__builtin_expect(!lw || !rm, 0))
                return PKSLOW;
            int a = -prev, b = __builtin_ctzll(rm) + 1;
            ll x0 = xcT[dp] + xcT[span - dp];
            if (a + b <= thr) {
                bool okF = b > fmax || xcT[dp + b] + xcT[span - dp - b] >= x0;
                bool okB = a > bmax || xcT[dp - a] + xcT[span - dp + a] >= x0;
                if (okF && okB)
                    return 0;
                bv = lb + x0;
            } else
                bv = ctab0[a + b] - ctab0[a] - ctab0[b] + x0;
            bestD = 0;
            prev = 0;
            m &= m - 1;
        }
        while (m) {
            int d = __builtin_ctzll(m);
            m &= m - 1;
            int dl = dp + d;
            ll xc = xcT[dl] + xcT[span - dl];
            if (bestD != NOPICK && xc + lb >= bv)
                break;
            ull after = wf >> d >> 1;
            if (__builtin_expect(prev <= -64 || !after, 0))
                return PKSLOW;
            int a = d - prev, b = __builtin_ctzll(after) + 1;
            ll v = ctab0[a + b] - ctab0[a] - ctab0[b] + xc;
            if (bestD == NOPICK || v < bv) {
                bv = v;
                bestD = d;
            }
            prev = d;
        }
    }
    if (bmax >= 1) {
        ull m = (w >> (32 - bmax)) & ((1ULL << bmax) - 1);
        while (m) {
            int j = 63 - __builtin_clzll(m);
            m ^= 1ULL << j;
            int d = bmax - j;
            int dl = dp - d;
            ll xc = xcT[dl] + xcT[span - dl];
            if (bestD != NOPICK && xc + lb >= bv)
                break;
            int k = 32 - d;
            ull lm = w & ((1ULL << k) - 1);
            ull rm = w >> (k + 1);
            if (__builtin_expect(!lm || !rm, 0))
                return PKSLOW;
            int a = k - (63 - __builtin_clzll(lm)), b = __builtin_ctzll(rm) + 1;
            ll v = ctab0[a + b] - ctab0[a] - ctab0[b] + xc;
            if (bestD == NOPICK || v < bv) {
                bv = v;
                bestD = -d;
            }
        }
    }
    return bestD;
}
int fillThr() {
    int s0 = typeSize[0];
    if (s0 <= 1 || s0 >= N)
        return 1 << 20;
    int q0 = qv[0];
    return q0 >= 2 ? q0 : 2;
}
__attribute__((noinline)) int pickSlow(int p, int dp, int span) {
    return pickCore2(p, dp, span, true, true);
}
__attribute__((noinline)) void pendPush(int p) {
    pend.push_back(p);
}
int nearestVacArc(int p, int lo, int spanLo) {
    int a = nextVac(p), b = prevVac(p);
    int da = a >= 0 ? dist(p, a) : N + 1, db = b >= 0 ? dist(b, p) : N + 1;
    bool ina = a >= 0 && (lo < 0 || dist(lo, a) < spanLo);
    bool inb = b >= 0 && (lo < 0 || dist(lo, b) < spanLo);
    if (ina && (!inb || da <= db))
        return a;
    if (inb)
        return b;
    return -1;
}
int pickVacX(int x, int p, int lo, int hi) {
    int best = -1;
    ll bv = 0;
    int spanLo = lo >= 0 ? dist(lo, hi) : N + 1;
    bool useX = lo >= 0 && typeSize[x] >= 2;
    if (N >= 192 && curWin <= 16 && (!useX || spanLo <= xcMax)) {
        int d = pickCore2(p, lo >= 0 ? dist(lo, p) : 0, spanLo, lo >= 0, useX);
        if (d != NOPICK) {
            int v = p + d;
            if (v >= N)
                v -= N;
            else if (v < 0)
                v += N;
            return v;
        }
        return nearestVacArc(p, lo, spanLo);
    }
    if (N >= 192 && curWin <= 63) {
        int fmax, bmax, dp = 0;
        if (lo < 0) {
            fmax = curWin;
            bmax = curWin;
        } else {
            dp = dist(lo, p);
            fmax = dp < spanLo ? spanLo - 1 - dp : -1;
            if (fmax > curWin)
                fmax = curWin;
            bmax = dp <= spanLo ? dp - 1 : 0;
            if (bmax > curWin)
                bmax = curWin;
        }
        int base = p - 64;
        if (base < 0)
            base += N;
        ull wl = bitsAt(base), wh = bitsAt(p);
        bool dx = useX && spanLo <= xcMax;
        if (fmax >= 0) {
            ull m = wh & lowMask(fmax + 1);
            int prev = wl ? (63 - __builtin_clzll(wl)) - 64 : -100;
            while (m) {
                int d = __builtin_ctzll(m);
                m &= m - 1;
                ll xc = 0;
                if (dx) {
                    int dl = dp + d;
                    xc = xcT[dl] + xcT[spanLo - dl];
                } else if (useX) {
                    int dl = dp + d;
                    xc = xcostw(x, dl) + xcostw(x, spanLo - dl);
                }
                if (best >= 0 && d > 0 && xc + fillLB >= bv)
                    break;
                int c = p + d;
                if (c >= N)
                    c -= N;
                ull after = d < 63 ? wh >> (d + 1) : 0;
                ll fc;
                if (prev > -100 && after) {
                    int a = d - prev, b = __builtin_ctzll(after) + 1;
                    fc = ctab0[a + b] - ctab0[a] - ctab0[b];
                } else
                    fc = fillCost(c);
                ll v = fc + xc;
                if (best < 0 || v < bv) {
                    bv = v;
                    best = c;
                }
                prev = d;
            }
        }
        if (bmax >= 1) {
            ull m = (wl >> (64 - bmax)) & lowMask(bmax);
            while (m) {
                int j = 63 - __builtin_clzll(m);
                m ^= 1ULL << j;
                int d = bmax - j;
                ll xc = 0;
                if (dx) {
                    int dl = dp - d;
                    xc = xcT[dl] + xcT[spanLo - dl];
                } else if (useX) {
                    int dl = dp - d;
                    xc = xcostw(x, dl) + xcostw(x, spanLo - dl);
                }
                if (best >= 0 && xc + fillLB >= bv)
                    break;
                int c = p - d;
                if (c < 0)
                    c += N;
                ll v = fillCostW2(c, wl, wh, 64 - d) + xc;
                if (best < 0 || v < bv) {
                    bv = v;
                    best = c;
                }
            }
        }
    } else {
        for (int sg = 0; sg < 2; sg++) {
            for (int d = sg; d <= curWin; d++) {
                int c = sg ? p - d : p + d;
                if (c >= N)
                    c -= N;
                else if (c < 0)
                    c += N;
                int dl = lo >= 0 ? dist(lo, c) : 1;
                if (lo >= 0 && (dl >= spanLo || c == lo))
                    break;
                if (slotType[c] != 0)
                    continue;
                ll xc = 0;
                if (useX)
                    xc = xcostw(x, dl) + xcostw(x, spanLo - dl);
                if (best >= 0 && d > 0 && xc + fillLB >= bv)
                    break;
                ll v = fillCost(c) + xc;
                if (best < 0 || v < bv) {
                    bv = v;
                    best = c;
                }
            }
        }
    }
    if (best >= 0)
        return best;
    return nearestVacArc(p, lo, spanLo);
}
#define FILLV(v)                                                                                   \
    do {                                                                                           \
        int w_ = (v) >> 6;                                                                         \
        ull nb_ = vb[w_] & ~(1ULL << ((v) & 63));                                                  \
        vb[w_] = nb_;                                                                              \
        if (!nb_) {                                                                                \
            vs[w_ >> 6] &= ~(1ULL << (w_ & 63));                                                   \
        }                                                                                          \
        changeStamp[v] = o;                                                                        \
        XSB(v) originalValue[v] = 0;                                                               \
        slotType[v] = x;                                                                           \
        publicGrid[v] = xid;                                                                       \
        if (TBITS)                                                                                 \
            TBSET(x, v);                                                                           \
    } while (0)
__attribute__((noinline)) int addNewCold(int x, int pos, int last, int span, int hi, int dp,
                                         int d) {
    if (span <= xcMax) {
        if (d == PKSLOW)
            d = pickSlow(pos, dp, span);
        if (d != NOPICK) {
            int v = pos + d;
            if (v >= N)
                v -= N;
            else if (v < 0)
                v += N;
            return v;
        }
        return nearestVacArc(pos, last, span);
    }
    return pickVacX(x, pos, last, hi);
}
template <int W>
__attribute__((noinline)) int placeAddNewN(int x, int c, int a, int ra, int &lastR, int &firstR) {
    const int n_ = N, o = operationStamp, xid = serviceId[x], xb = x << 8, xcM = xcMax, sN = c,
              thr = fillThr();
    const ll lb = fillLB;
    const int cap = seedCap;
    int nS = nSeeds;
    int pos = a >> 1, rem = 0;
    int placed = 0, last = -1, first = -1, dFirst = 0;
    {
        int v = pickVac(pos, -1, 0);
        if (v < 0) {
            lastR = -1;
            firstR = -1;
            return 0;
        }
        {
            int w_ = v >> 6;
            ull nb_ = vb[w_] & ~(1ULL << (v & 63));
            vb[w_] = nb_;
            if (!nb_)
                vs[w_ >> 6] &= ~(1ULL << (w_ & 63));
        }
        changeStamp[v] = o;
        XSB(v) originalValue[v] = 0;
        slotType[v] = x;
        publicGrid[v] = xid;
        TBit[xb + (v >> 6)] |= 1ULL << (v & 63);
        first = v;
        typeHead[x] = v;
        if (nS < cap && !inq[v]) {
            inq[v] = 1;
            seedA[nS++] = v;
        }
        last = v;
        placed = 1;
        dFirst = n_;
        pos += a;
        rem += ra;
        if (rem >= sN) {
            rem -= sN;
            pos++;
        }
        if (pos >= n_)
            pos -= n_;
    }
    for (int k = 1; k < c; k++) {
        int np = pos + a;
        if (rem + ra >= sN)
            np++;
        if (np >= n_)
            np -= n_;
        int hi = k + 1 < c ? np : first;
        int span = hi - last;
        if (span <= 0)
            span += n_;
        int dp = pos - last;
        if (dp <= 0)
            dp += n_;
        int v;
        int d = PKSLOW;
        if (__builtin_expect(span <= xcM, 1)) {
            int base = pos - 32;
            if (base < 0)
                base += n_;
            d = pick3<W>(dp, span, bitsAtN(base, n_), lb, thr);
        }
        if (__builtin_expect(d < NOPICK, 1)) {
            v = pos + d;
            if (v >= n_)
                v -= n_;
            else if (v < 0)
                v += n_;
        } else
            v = addNewCold(x, pos, last, span, hi, dp, d);
        int dv = v - last;
        if (dv <= 0)
            dv += n_;
        if (__builtin_expect(v < 0 || dv >= dFirst, 0)) {
            if (PENDNEW)
                pendPush(pos);
            else
                break;
        } else {
            {
                int w_ = v >> 6;
                ull nb_ = vb[w_] & ~(1ULL << (v & 63));
                vb[w_] = nb_;
                if (!nb_)
                    vs[w_ >> 6] &= ~(1ULL << (w_ & 63));
            }
            changeStamp[v] = o;
            XSB(v) originalValue[v] = 0;
            slotType[v] = x;
            publicGrid[v] = xid;
            TBit[xb + (v >> 6)] |= 1ULL << (v & 63);
            nextSame[last] = v;
            prevSame[v] = last;
            if (nS < cap && !inq[v]) {
                inq[v] = 1;
                seedA[nS++] = v;
            }
            last = v;
            placed++;
            dFirst = first - v;
            if (dFirst <= 0)
                dFirst += n_;
        }
        pos += a;
        rem += ra;
        if (rem >= sN) {
            rem -= sN;
            pos++;
        }
        if (pos >= n_)
            pos -= n_;
    }
    nSeeds = nS;
    lastR = last;
    firstR = first;
    return placed;
}
// 新服务首次出现时，在空位约束下铺开它的颗粒。
__attribute__((noinline)) void placeAddNew(int x, int c) {
    int sN = c;
    typeSize[x] = sN;
    setType(x);
    ll pxu = multiplyNonnegative((ll)sN << 1, F[x]);
    pxv = F[0] > 0 ? divideNonnegative(pxu, F[0]) : pxu;
    ll a = divideNonnegative(N, sN), ra = N - multiplyNonnegative(a, sN);
    int pos = (int)(a >> 1);
    ll rem = 0;
    int placed = 0, last = -1, first = -1;
    const int o = operationStamp, xid = serviceId[x];
    rxw = F[0] > 0 ? divideNonnegative(F[x] << 10, F[0]) : 1024;
    buildXcT(x, XCW ? (int)(a << 1) + (curWin << 1) + 64 : (int)a + (curWin << 1) + 4);
    bool smallW = N >= 192 && curWin <= 63 && sN >= 2;
    const bool narrow = curWin <= 16;
    pend.clear();
    int cl = c;
    if (BLF && smallW && ((curWin >= 2 && curWin <= 8) || curWin == 12 || curWin == 16) &&
        !fastPk && TBITS) {
        const int ia = (int)a, ir = (int)ra;
        switch (curWin) {
        case 12:
            placed = placeAddNewN<12>(x, c, ia, ir, last, first);
            break;
        case 16:
            placed = placeAddNewN<16>(x, c, ia, ir, last, first);
            break;
        case 2:
            placed = placeAddNewN<2>(x, c, ia, ir, last, first);
            break;
        case 3:
            placed = placeAddNewN<3>(x, c, ia, ir, last, first);
            break;
        case 4:
            placed = placeAddNewN<4>(x, c, ia, ir, last, first);
            break;
        case 5:
            placed = placeAddNewN<5>(x, c, ia, ir, last, first);
            break;
        case 6:
            placed = placeAddNewN<6>(x, c, ia, ir, last, first);
            break;
        case 7:
            placed = placeAddNewN<7>(x, c, ia, ir, last, first);
            break;
        default:
            placed = placeAddNewN<8>(x, c, ia, ir, last, first);
            break;
        }
        cl = 0;
    }
    for (int k = 0; k < cl; k++) {
        int v;
        if (last < 0)
            v = pickVac(pos, -1, 0);
        else {
            int np = pos + (int)a;
            ll nr = rem + ra;
            if (nr >= sN)
                np++;
            if (np >= N)
                np -= N;
            int hi = k + 1 < c ? np : first;
            int span = dist(last, hi);
            if (fastPk)
                v = nearestVacArc(pos, last, span);
            else if (smallW && span <= xcMax) {
                int d = narrow ? pickCore2(pos, dist(last, pos), span, true, true)
                               : pickCoreW(pos, dist(last, pos), span);
                if (d != NOPICK) {
                    v = pos + d;
                    if (v >= N)
                        v -= N;
                    else if (v < 0)
                        v += N;
                } else
                    v = nearestVacArc(pos, last, span);
            } else
                v = pickVacX(x, pos, last, hi);
            if (v >= 0 && dist(last, v) >= dist(last, first))
                v = -1;
        }
        if (v < 0) {
            if (last < 0 || !PENDNEW)
                break;
            pend.push_back(pos);
        } else {
            FILLV(v);
            if (last >= 0) {
                nextSame[last] = v;
                prevSame[v] = last;
            } else {
                first = v;
                typeHead[x] = v;
            }
            pushSeed(v);
            last = v;
            placed++;
        }
        pos += (int)a;
        rem += ra;
        if (rem >= sN) {
            rem -= sN;
            pos++;
        }
        if (pos >= N)
            pos -= N;
    }
    if (last >= 0) {
        nextSame[last] = first;
        prevSame[first] = last;
    }
    for (int p : pend) {
        if (placed >= c)
            break;
        int v = pickVac(p, -1, 0);
        if (v < 0)
            break;
        setCell(v, x, -2);
        pushSeed(v);
        placed++;
    }
    while (placed < c) {
        int v = nextVac(last < 0 ? 0 : last);
        if (v < 0)
            break;
        setCell(v, x, -2);
        pushSeed(v);
        placed++;
    }
}
