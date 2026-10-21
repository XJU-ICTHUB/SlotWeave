// 必要改动的放置调度。根据当前类型、颗粒数和空位结构选择链 DP、间隔分配或有界回退路径。
// Included in fixed order by solution.cpp.

int zaX = 0;
ull zaB[(MAXN >> 6) + 2];
int zchRec = 0, zchNN = 0;
int zchNL[MAXN + 8];
void placement_dp::zFill(int p) {
    if (zchRec)
        zchNL[zchNN++] = p;
    unlinkCell(p);
    markChange(p);
    slotType[p] = zaX;
    publicGrid[p] = serviceId[zaX];
    if (TBITS)
        TBSET(zaX, p);
    zaB[p >> 6] |= 1ULL << (p & 63);
    pushSeed(p);
    placement_dp::zDone++;
}
void placement_dp::zFree(int p) {
    freeCell(p);
    pushSeed(p);
    placement_dp::zDone++;
}
int zkL[MAXN + 8], zdL[MAXN + 8];
void placement_dp::zFreeBatch(int t, int s) {
    RVEC(int) &P = placement_dp::posX;
    int nk = 0, nd = 0;
    for (int i = 0; i < s; i++) {
        int p = P[i], d = placement_dp::rDeadA[i];
        zkL[nk] = p;
        zdL[nd] = p;
        nk += d ^ 1;
        nd += d;
    }
    if (nk == 0) {
        for (int i = 0; i < nd; i++)
            zFree(zdL[i]);
        return;
    }
    int h = typeHead[t];
    int nh = zkL[0];
    for (int i = 0; i < nk; i++)
        if (zkL[i] >= h) {
            nh = zkL[i];
            break;
        }
    int last = zkL[nk - 1];
    for (int i = 0; i < nk; i++) {
        int p = zkL[i];
        nextSame[last] = p;
        prevSame[p] = last;
        last = p;
    }
    typeHead[t] = nh;
    const int o = operationStamp, xid = serviceId[t];
    for (int i = 0; i < nd; i++) {
        int p = zdL[i];
        if (changeStamp[p] != o) {
            changeStamp[p] = o;
            originalValue[p] = xid;
            XSB(p)
        }
        if (TBITS)
            TBCLR(t, p);
        slotType[p] = 0;
        publicGrid[p] = 0;
        vbSet(p);
        pushSeed(p);
    }
    placement_dp::zDone += nd;
}
void zaRelink(int x) {
    int first = -1, last = -1;
    for (int w = 0; w < NW; w++) {
        ull m = zaB[w];
        if (!m)
            continue;
        zaB[w] = 0;
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
}
#define SP3_ZPS 4
void zaPositions(int x, int s) {
    RVEC(int) &P = placement_dp::posX;
    P.resize(s);
    if (TBITS && s > (N >> SP3_ZPS)) {
        int m = 0;
        for (int w = 0; w < NW; w++) {
            ull b = TBit[(x << 8) + w];
            while (b) {
                P[m++] = (w << 6) + __builtin_ctzll(b);
                b &= b - 1;
            }
        }
        return;
    }
    int cur = typeHead[x], mi = 0;
    for (int k = 0; k < s; k++) {
        P[k] = cur;
        if (cur < P[mi])
            mi = k;
        cur = nextSame[cur];
    }
    if (mi)
        std::rotate(P.begin(), P.begin() + mi, P.end());
}
int xsA[MAXN + 8], glA[MAXN + 8], ciA[MAXN + 8], selA[MAXN + 8];
int nSel = 0, mxGap = 0;
int tq2[MAXN + 8], tr3[MAXN + 8];
void allocGaps(int m, int c, int sN, int maxg) {
    nSel = 0;
    mxGap = 0;
    if (c == m) {
        for (int k = 0; k < m; k++) {
            ciA[k] = 1;
            selA[k] = k;
        }
        nSel = m;
        mxGap = maxg;
        return;
    }
    if (c < m) {
        if (maxg <= (m << 2) + 64) {
            int k = 0;
            for (; k + 3 < m; k += 4) {
                histG4[glA[k] << 2]++;
                histG4[(glA[k + 1] << 2) + 1]++;
                histG4[(glA[k + 2] << 2) + 2]++;
                histG4[(glA[k + 3] << 2) + 3]++;
            }
            for (; k < m; k++)
                histG4[(glA[k] << 2) | (BLF ? (k & 3) : 0)]++;
            int acc = 0, t = maxg, ht = 0;
            for (;;) {
                int b4 = t << 2;
                ht = histG4[b4] + histG4[b4 + 1] + histG4[b4 + 2] + histG4[b4 + 3];
                if (acc + ht >= c)
                    break;
                acc += ht;
                t--;
            }
            int skip = ht - (c - acc);
            int seen = 0;
            if (BLF && maxg >= m) {
                for (k = 0; k < m; k++) {
                    int gk = glA[k];
                    histG4[(gk << 2) | (k & 3)] = 0;
                    int isT = gk == t;
                    int sel = (gk > t) | (isT & (seen >= skip));
                    seen += isT;
                    ciA[k] = sel;
                    selA[nSel] = k;
                    nSel += sel;
                }
            } else {
                for (k = 0; k < m; k++) {
                    int gk = glA[k];
                    int isT = gk == t;
                    int sel = (gk > t) | (isT & (seen >= skip));
                    seen += isT;
                    ciA[k] = sel;
                    selA[nSel] = k;
                    nSel += sel;
                }
                if (maxg < m) {
                    for (int g = 0; g <= (maxg << 2) + 3; g++)
                        histG4[g] = 0;
                } else {
                    for (k = 0; k < m; k++) {
                        int b4 = glA[k] << 2;
                        histG4[b4] = 0;
                        histG4[b4 + 1] = 0;
                        histG4[b4 + 2] = 0;
                        histG4[b4 + 3] = 0;
                    }
                }
            }
        } else {
            gord.resize(m);
            for (int k = 0; k < m; k++) {
                gord[k] = ((ll)glA[k] << 20) | k;
                ciA[k] = 0;
            }
            nth_element(gord.begin(), gord.begin() + (m - c), gord.end());
            for (int k = m - c; k < m; k++)
                ciA[(int)(gord[k] & ((1 << 20) - 1))] = 1;
            for (int k = 0; k < m; k++)
                if (ciA[k])
                    selA[nSel++] = k;
        }
        for (int si = 0; si < nSel; si++)
            if (glA[selA[si]] > mxGap)
                mxGap = glA[selA[si]];
        return;
    }
    {
        int q = 0, r = 0;
        for (int g = 0; g <= maxg; g++) {
            tq2[g] = q;
            tr3[g] = r;
            r += sN;
            if (r >= N) {
                r -= N;
                q++;
            }
        }
    }
    int Q = 0, R = 0, debt = 0, total = 0;
    for (int k = 0; k < m; k++) {
        int g = glA[k];
        int Qp = Q;
        Q += tq2[g];
        R += tr3[g];
        int ov = R >= N;
        R -= ov ? N : 0;
        Q += ov;
        int n = Q - Qp - 1 - debt;
        debt = n < 0 ? -n : 0;
        n = n < 0 ? 0 : n;
        ciA[k] = n;
        total += n;
    }
    while (total > c) {
        int bk = 0;
        for (int k = 1; k < m; k++)
            if (ciA[k] > ciA[bk])
                bk = k;
        ciA[bk]--;
        total--;
    }
    if (total < c) {
        gord.resize(m);
        for (int k = 0; k < m; k++)
            gord[k] = divideNonnegative((ll)glA[k] << 8, ciA[k] + 1);
        while (total < c) {
            int bk = 0;
            ll bv = gord[0];
            for (int k = 1; k < m; k++)
                if (gord[k] > bv) {
                    bv = gord[k];
                    bk = k;
                }
            ciA[bk]++;
            total++;
            gord[bk] = divideNonnegative((ll)glA[bk] << 8, ciA[bk] + 1);
        }
    }
    for (int k = 0; k < m; k++) {
        selA[nSel] = k;
        nSel += ciA[k] > 0;
    }
    for (int si = 0; si < nSel; si++)
        if (glA[selA[si]] > mxGap)
            mxGap = glA[selA[si]];
}
int mX = 0;
__attribute__((noinline)) int gapCold(int x, int p, int prevCell, int span, int dp, int L, int nref,
                                      int d, int &offV) {
    int v;
    if (span <= xcMax) {
        if (d == PKSLOW)
            d = pickSlow(p, dp, span);
        if (d != NOPICK) {
            v = p + d;
            if (v >= N)
                v -= N;
            else if (v < 0)
                v += N;
            offV = -1;
            return v;
        }
        v = nearestVacArc(p, prevCell, span);
    } else
        v = pickVacX(x, p, prevCell, nref);
    if (v >= 0) {
        offV = v - L;
        if (offV <= 0)
            offV += N;
    }
    return v;
}
template <int W> __attribute__((noinline)) int placeGapsN(int x) {
    int placed = 0;
    const int n_ = N, o = operationStamp, xid = serviceId[x], xb = x << 8, xcM = xcMax, mx = mX,
              nsel = nSel, thr = fillThr();
    const ll lb = fillLB;
    const int cap = seedCap;
    int nS = nSeeds;
    for (int si = 0; si < nsel; si++) {
        const int k = selA[si], n = ciA[k], L = xsA[k];
        const int g = glA[k];
        if (n == 1) {
            const int off = g - (g >> 1);
            int p = L + off;
            if (p >= n_)
                p -= n_;
            int v, offV, d = PKSLOW;
            if (__builtin_expect(g <= xcM, 1)) {
                int base = p - 32;
                if (base < 0)
                    base += n_;
                d = pick3<W>(off, g, bitsAtN(base, n_), lb, thr);
            }
            if (__builtin_expect(d < NOPICK, 1)) {
                v = p + d;
                if (v >= n_)
                    v -= n_;
                else if (v < 0)
                    v += n_;
                offV = off + d;
                if (offV > n_)
                    offV -= n_;
                else if (offV <= 0)
                    offV += n_;
            } else {
                int nref = L + g;
                if (nref >= n_)
                    nref -= n_;
                v = gapCold(x, p, L, g, off, L, nref, d, offV);
                if (v < 0) {
                    pendPush(p);
                    continue;
                }
                if (offV < 0) {
                    int dd = v - p;
                    if (dd > (n_ >> 1))
                        dd -= n_;
                    else if (dd < -(n_ >> 1))
                        dd += n_;
                    offV = off + dd;
                    if (offV > n_)
                        offV -= n_;
                    else if (offV <= 0)
                        offV += n_;
                }
            }
            if (__builtin_expect(offV >= g, 0)) {
                pendPush(p);
                continue;
            }
            const int R = xsA[k + 1 < mx ? k + 1 : 0];
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
            nextSame[L] = v;
            prevSame[v] = L;
            nextSame[v] = R;
            prevSame[R] = v;
            if (nS < cap && !inq[v]) {
                inq[v] = 1;
                seedA[nS++] = v;
            }
            placed++;
            continue;
        }
        const int R = xsA[k + 1 < mx ? k + 1 : 0];
        const int n1 = n + 1;
        int st, sr;
        if (n1 == 2) {
            st = g >> 1;
            sr = g & 1;
        } else {
            st = (int)divideNonnegative(g, n1);
            sr = g - (int)multiplyNonnegative(st, n1);
        }
        int off = 0, rem = n1 >> 1, offPrev = 0, prevCell = L;
        for (int j = 1; j <= n; j++) {
            off += st;
            rem += sr;
            if (rem >= n1) {
                rem -= n1;
                off++;
            }
            int offN;
            if (j == n)
                offN = g;
            else {
                offN = off + st;
                if (rem + sr >= n1)
                    offN++;
            }
            int p = L + off;
            if (p >= n_)
                p -= n_;
            int span = offN - offPrev;
            if (span <= 0)
                span += n_;
            int dp = off - offPrev;
            if (dp <= 0)
                dp += n_;
            int v, offV, d = PKSLOW;
            if (__builtin_expect(span <= xcM, 1)) {
                int base = p - 32;
                if (base < 0)
                    base += n_;
                d = pick3<W>(dp, span, bitsAtN(base, n_), lb, thr);
            }
            if (__builtin_expect(d < NOPICK, 1)) {
                v = p + d;
                if (v >= n_)
                    v -= n_;
                else if (v < 0)
                    v += n_;
                offV = off + d;
                if (offV > n_)
                    offV -= n_;
                else if (offV <= 0)
                    offV += n_;
            } else {
                int nref = L + offN;
                if (nref >= n_)
                    nref -= n_;
                v = gapCold(x, p, prevCell, span, dp, L, nref, d, offV);
                if (v < 0) {
                    pendPush(p);
                    continue;
                }
                if (offV < 0) {
                    int dd = v - p;
                    if (dd > (n_ >> 1))
                        dd -= n_;
                    else if (dd < -(n_ >> 1))
                        dd += n_;
                    offV = off + dd;
                    if (offV > n_)
                        offV -= n_;
                    else if (offV <= 0)
                        offV += n_;
                }
            }
            int dv = offV - offPrev;
            if (dv <= 0)
                dv += n_;
            int dR = g - offPrev;
            if (dR <= 0)
                dR += n_;
            if (__builtin_expect(dv >= dR, 0)) {
                pendPush(p);
                continue;
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
            nextSame[prevCell] = v;
            prevSame[v] = prevCell;
            if (nS < cap && !inq[v]) {
                inq[v] = 1;
                seedA[nS++] = v;
            }
            prevCell = v;
            offPrev = offV;
            placed++;
        }
        if (prevCell != L) {
            nextSame[prevCell] = R;
            prevSame[R] = prevCell;
        }
    }
    nSeeds = nS;
    return placed;
}
__attribute__((noinline)) int placeGaps(int x, bool smallW) {
    if (BLF && smallW && ((curWin >= 2 && curWin <= 8) || curWin == 12 || curWin == 16) &&
        !fastPk && TBITS) {
        switch (curWin) {
        case 12:
            return placeGapsN<12>(x);
        case 16:
            return placeGapsN<16>(x);
        case 2:
            return placeGapsN<2>(x);
        case 3:
            return placeGapsN<3>(x);
        case 4:
            return placeGapsN<4>(x);
        case 5:
            return placeGapsN<5>(x);
        case 6:
            return placeGapsN<6>(x);
        case 7:
            return placeGapsN<7>(x);
        default:
            return placeGapsN<8>(x);
        }
    }
    int placed = 0;
    const bool narrow = curWin <= 16;
    const int o = operationStamp, xid = serviceId[x];
    for (int si = 0; si < nSel; si++) {
        int k = selA[si];
        int n = ciA[k];
        int L = xsA[k];
        int R = xsA[k + 1 < mX ? k + 1 : 0];
        int g = glA[k];
        int n1 = n + 1;
        int st, sr;
        if (n1 == 2) {
            st = g >> 1;
            sr = g & 1;
        } else {
            st = (int)divideNonnegative(g, n1);
            sr = g - (int)multiplyNonnegative(st, n1);
        }
        int off = 0, rem = n1 >> 1, offPrev = 0, prevCell = L;
        for (int j = 1; j <= n; j++) {
            off += st;
            rem += sr;
            if (rem >= n1) {
                rem -= n1;
                off++;
            }
            int offN;
            if (j == n)
                offN = g;
            else {
                offN = off + st;
                if (rem + sr >= n1)
                    offN++;
            }
            int p = L + off;
            if (p >= N)
                p -= N;
            int span = offN - offPrev;
            if (span <= 0)
                span += N;
            int v, offV;
            if (fastPk) {
                v = nearestVacArc(p, prevCell, span);
                if (v < 0) {
                    pend.push_back(p);
                    continue;
                }
                offV = dist(L, v);
            } else if (smallW && span <= xcMax) {
                int dp = off - offPrev;
                if (dp <= 0)
                    dp += N;
                int d = narrow ? pickCore2(p, dp, span, true, true) : pickCoreW(p, dp, span);
                if (d != NOPICK) {
                    v = p + d;
                    if (v >= N)
                        v -= N;
                    else if (v < 0)
                        v += N;
                    offV = off + d;
                    if (offV > N)
                        offV -= N;
                    else if (offV <= 0)
                        offV += N;
                } else {
                    v = nearestVacArc(p, prevCell, span);
                    if (v < 0) {
                        pend.push_back(p);
                        continue;
                    }
                    offV = dist(L, v);
                }
            } else {
                int nref = L + offN;
                if (nref >= N)
                    nref -= N;
                v = pickVacX(x, p, prevCell, nref);
                if (v < 0) {
                    pend.push_back(p);
                    continue;
                }
                offV = dist(L, v);
            }
            int dv = offV - offPrev;
            if (dv <= 0)
                dv += N;
            int dR = g - offPrev;
            if (dR <= 0)
                dR += N;
            if (dv >= dR) {
                pend.push_back(p);
                continue;
            }
            FILLV(v);
            nextSame[prevCell] = v;
            prevSame[v] = prevCell;
            pushSeed(v);
            prevCell = v;
            offPrev = offV;
            placed++;
        }
        if (prevCell != L) {
            nextSame[prevCell] = R;
            prevSame[R] = prevCell;
        }
    }
    return placed;
}
#define BLCOLL 48
int collectCirc(int x, int arr[]) {
    const int h = typeHead[x], hw = h >> 6, xb = x << 8, nw = NW;
    int m = 0, w = hw;
    ull b = TBit[xb + hw] & (~0ULL << (h & 63));
    for (;;) {
        const int base = w << 6;
        while (b) {
            arr[m++] = base + __builtin_ctzll(b);
            b &= b - 1;
        }
        w++;
        if (w >= nw)
            w = 0;
        if (w == hw)
            break;
        b = TBit[xb + w];
    }
    b = TBit[xb + hw] & ((1ULL << (h & 63)) - 1);
    const int base = hw << 6;
    while (b) {
        arr[m++] = base + __builtin_ctzll(b);
        b &= b - 1;
    }
    return m;
}
int collectXA(int x, int s) {
    int m = 0;
    if (TBITS && s > (N >> 3)) {
        for (int w = 0; w < NW; w++) {
            ull b = TBit[(x << 8) + w];
            while (b) {
                xsA[m++] = (w << 6) + __builtin_ctzll(b);
                b &= b - 1;
            }
        }
    } else if (s > (N >> 3)) {
        for (int i = 0; i < N; i++) {
            xsA[m] = i;
            m += (slotType[i] == x);
        }
    } else if (BLF && TBITS && s >= BLCOLL)
        m = collectCirc(x, xsA);
    else {
        int cur = typeHead[x];
        for (int k = 0; k < s; k++) {
            xsA[k] = cur;
            cur = nextSame[cur];
        }
        m = s;
    }
    return m;
}
ll ehTypeCost(int t) {
    ll P = 0;
    if (t) {
        int h = typeHead[t];
        if (h < 0 || typeSize[t] < 2)
            return 0;
        int cur = h;
        do {
            int nx = nextSame[cur];
            int g = nx - cur;
            if (g <= 0)
                g += N;
            P += wcst(t, g);
            cur = nx;
        } while (cur != h);
        return P;
    }
    if (typeSize[0] < 2)
        return 0;
    if (SX_VQ > 0 && qv[0] >= 1 && qv[0] <= SX_VQ &&
        multiplyNonnegative(qv[0], NW) <= typeSize[0] && F[0] != 0) {
        int nle, first, last, e;
        ll sle;
        vacShort(qv[0], nle, sle, first, last, e);
        const ll fs = wmt[1], FN = multiplyNonnegative(F[0], N);
        const ll ngt = (ll)(e - 1) - nle, sgt = (ll)(last - first) - sle;
        const ll dn = nle - ngt, ds = sgt - sle;
        P = (dn >= 0 ? multiplyNonnegative(FN, dn) : -multiplyNonnegative(FN, -dn)) +
            (ds >= 0 ? multiplyNonnegative(fs, ds) : -multiplyNonnegative(fs, -ds));
        return P + wcst(0, first + N - last);
    }
    int first = -1, last = -1;
    for (int w = 0; w < NW; w++) {
        ull m = vb[w];
        while (m) {
            int i = (w << 6) + __builtin_ctzll(m);
            m &= m - 1;
            if (last >= 0)
                P += wcst(0, i - last);
            else
                first = i;
            last = i;
        }
    }
    if (first >= 0)
        P += wcst(0, first + N - last);
    return P;
}
int ehCells[MAXN + 8], ehSeeds[(MAXN << 2) + 16];
int ehUndoNew(int x, int n0, bool keep) {
    int h = typeHead[x], k = 0;
    if (h >= 0) {
        int cur = h;
        do {
            int nx = nextSame[cur];
            if (keep)
                ehCells[k] = cur;
            k++;
            if (TBITS)
                TBCLR(x, cur);
            slotType[cur] = 0;
            publicGrid[cur] = 0;
            vbSet(cur);
            cur = nx;
        } while (cur != h);
    }
    typeHead[x] = -1;
    for (int i = n0; i < nSeeds; i++)
        inq[seedA[i]] = 0;
    nSeeds = n0;
    return k;
}
void zaPlaceNew(int x, int c, int E) {
    zaX = x;
    placement_dp::doAdd(x, c, 0, E);
    zaRelink(x);
}
// 增加颗粒的必要放置入口，只从当前空位中选择合法位置。
__attribute__((noinline)) void placeAddedGranules(int x, int c) {
    int s = typeSize[x];
    int sN = s + c;
    if (EH_DUAL && s == 0 && pZAC > 0 && c >= pZAC && c >= EH_DUALC && c < ZAMAX && N > NM &&
        ZASEL == 2 && c < typeSize[0]) {
        const int E = typeSize[0], n0 = nSeeds;
        typeSize[0] -= c;
        setType(0);
        fillLB = cst(0, 2) - (cst(0, 1) << 1);
        placeAddNew(x, c);
        ll pa = ehTypeCost(x) + ehTypeCost(0);
        ll pm = 0;
        {
            ll r = rv[x];
            pm += multiplyNonnegative(multiplyNonnegative(r, sN - r) << 1, F[x]);
            r = rv[0];
            pm += multiplyNonnegative(multiplyNonnegative(r, typeSize[0] - r) << 1, F[0]);
        }
        if (pa - pm > (pm >> EH_DUALS)) {
            const int headA = typeHead[x], nsA = nSeeds;
            for (int i = n0; i < nsA; i++)
                ehSeeds[i - n0] = seedA[i];
            int na = ehUndoNew(x, n0, true);
            zaPlaceNew(x, c, E);
            ll pb = ehTypeCost(x) + ehTypeCost(0);
            if (pb >= pa) {
                ehUndoNew(x, n0, false);
                const int o = operationStamp, xid = serviceId[x];
                for (int k = 0; k < na; k++) {
                    int v = ehCells[k];
                    vbClr(v);
                    if (changeStamp[v] != o) {
                        changeStamp[v] = o;
                        originalValue[v] = 0;
                        XSB(v)
                    }
                    slotType[v] = x;
                    publicGrid[v] = xid;
                    if (TBITS)
                        TBSET(x, v);
                    zaB[v >> 6] |= 1ULL << (v & 63);
                }
                zaRelink(x);
                typeHead[x] = headA;
                for (int i = n0; i < nsA; i++) {
                    int p = ehSeeds[i - n0];
                    inq[p] = 1;
                    seedA[i] = p;
                }
                nSeeds = nsA;
            }
        }
        return;
    }
    if (pZAC > 0 && c >= (s == 0 ? pZAC : pZACX) && c < ZAMAX && N >= 64 &&
        (ZASEL == 0 || (ZASEL == 1) == (s == 0) || N <= NM)) {
        int E = typeSize[0];
        typeSize[0] -= c;
        setType(0);
        typeSize[x] = sN;
        setType(x);
        if (s > 0)
            zaPositions(x, s);
        zaX = x;
        if (TBITS) {
            const int xb = x << 8;
            for (int w = 0; w < NW; w++)
                zaB[w] |= TBit[xb + w];
        } else
            for (int k = 0; k < s; k++) {
                int p = placement_dp::posX[k];
                zaB[p >> 6] |= 1ULL << (p & 63);
            }
        zchNN = 0;
        zchRec = ZCH_P && s > 0 && N > ZCH_NLO && c >= (N >> ZCH_C) && (HVB_VCAP == 0 || hvbX);
        placement_dp::doAdd(x, c, s, E);
        zchRec = 0;
        zaRelink(x);
        return;
    }
    typeSize[0] -= c;
    setType(0);
    fillLB = cst(0, 2) - (cst(0, 1) << 1);
    if (s == 0) {
        placeAddNew(x, c);
        return;
    }
    typeSize[x] = sN;
    setType(x);
    ll pxu = multiplyNonnegative((ll)sN << 1, F[x]);
    pxv = F[0] > 0 ? divideNonnegative(pxu, F[0]) : pxu;
    rxw = F[0] > 0 ? divideNonnegative(F[x] << 10, F[0]) : 1024;
    int m = collectXA(x, s);
    int maxg = 0;
    if (m == 1) {
        glA[0] = N;
        maxg = N;
    } else {
        for (int k = 0; k + 1 < m; k++) {
            int g = xsA[k + 1] - xsA[k];
            if (g <= 0)
                g += N;
            glA[k] = g;
            maxg = g > maxg ? g : maxg;
        }
        int g = xsA[0] - xsA[m - 1];
        if (g <= 0)
            g += N;
        glA[m - 1] = g;
        maxg = g > maxg ? g : maxg;
    }
    allocGaps(m, c, sN, maxg);
    mX = m;
    buildXcT(x, mxGap > 4096 ? 4096 : mxGap);
    pend.clear();
    int placed = placeGaps(x, N >= 192 && curWin <= 63 && xcMax >= mxGap);
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
}
SP2_I ll wremCostX(int x, int p) {
    int L = prevSame[p], R = nextSame[p];
    if (L == p || L == R)
        return 0;
    return wcst(x, dist(L, R)) - wcst(x, dist(L, p)) - wcst(x, dist(p, R));
}
int xsR[MAXN + 8];
void collectX(int x, int s) {
    xs.resize(s);
    if (TBITS && s > (N >> 3)) {
        int k = 0;
        for (int w = 0; w < NW; w++) {
            ull b = TBit[(x << 8) + w];
            while (b) {
                xs[k++] = (w << 6) + __builtin_ctzll(b);
                b &= b - 1;
            }
        }
    } else if (s > (N >> 3)) {
        int k = 0;
        xs.resize(N + 1);
        for (int i = 0; i < N; i++) {
            xs[k] = i;
            k += (slotType[i] == x);
        }
        xs.resize(k);
    } else if (BLF && TBITS && s >= BLCOLL) {
        collectCirc(x, xsR);
        for (int k = 0; k < s; k++)
            xs[k] = xsR[k];
    } else {
        int cur = typeHead[x];
        for (int k = 0; k < s; k++) {
            xs[k] = cur;
            cur = nextSame[cur];
        }
    }
}
// 删除颗粒的必要选择入口，同时评估服务合并和空位拆分代价。
__attribute__((noinline)) void selectRemovedGranules(int x, int c) {
    int s = typeSize[x];
    if (pZACR > 0 && c >= pZACR && c < s && c < ZAMAXR && N >= 64 &&
        (ZARS == 0 || s <= (N >> ZARS) || N <= NM) &&
        (ZABLK || N <= NM || multiplyNonnegative(c, ZREMKL) >= s) &&
        (N <= NM || s - c <= ZAS1MAX)) {
        int E = typeSize[0];
        typeSize[0] += c;
        setType(0);
        typeSize[x] = s - c;
        setType(x);
        zaPositions(x, s);
        zaX = x;
        placement_dp::doRemove(x, c, s, E);
        return;
    }
    typeSize[0] += c;
    setType(0);
    int sN = s - c;
    const int o = operationStamp, xid = serviceId[x];
    if (s > (N >> 3) && (sN == 0 || c > RCBIG || F[0] == 0)) {
        if (sN == 0)
            typeHead[x] = -1;
        typeSize[x] = sN;
        setType(x);
        int acc = s >> 1;
        if (BLF && TBITS) {
            const int xb = x << 8, nw = NW, cap = seedCap;
            int nS = nSeeds, h = typeHead[x];
            for (int w = 0; w < nw; w++) {
                ull m = TBit[xb + w];
                if (!m)
                    continue;
                ull fr;
                if (sN == 0)
                    fr = m;
                else {
                    fr = 0;
                    while (m) {
                        int b = __builtin_ctzll(m);
                        m &= m - 1;
                        acc += c;
                        int f = acc >= s;
                        acc -= f ? s : 0;
                        fr |= (ull)f << b;
                    }
                    if (!fr)
                        continue;
                }
                TBit[xb + w] &= ~fr;
                vb[w] |= fr;
                vs[w >> 6] |= 1ULL << (w & 63);
                const int i0 = w << 6;
                while (fr) {
                    int p = i0 + __builtin_ctzll(fr);
                    fr &= fr - 1;
                    if (sN) {
                        int L = prevSame[p], R = nextSame[p];
                        nextSame[L] = R;
                        prevSame[R] = L;
                        if (h == p)
                            h = R;
                    }
                    changeStamp[p] = o;
                    XSB(p) originalValue[p] = xid;
                    slotType[p] = 0;
                    publicGrid[p] = 0;
                    if (nS < cap && !inq[p]) {
                        inq[p] = 1;
                        seedA[nS++] = p;
                    }
                }
            }
            if (sN)
                typeHead[x] = h;
            nSeeds = nS;
            return;
        }
        for (int w = 0; w < NW; w++) {
            int i0 = w << 6, i1 = i0 + 64;
            if (i1 > N)
                i1 = N;
            ull m = 0;
            if (TBITS)
                m = TBit[(x << 8) + w];
            else
                for (int i = i0; i < i1; i++)
                    m |= (ull)(slotType[i] == x) << (i - i0);
            if (!m)
                continue;
            ull fr = 0;
            if (sN == 0)
                fr = m;
            else {
                while (m) {
                    int b = __builtin_ctzll(m);
                    m &= m - 1;
                    acc += c;
                    if (acc >= s) {
                        acc -= s;
                        fr |= 1ULL << b;
                        int p = i0 + b, L = prevSame[p], R = nextSame[p];
                        nextSame[L] = R;
                        prevSame[R] = L;
                        if (typeHead[x] == p)
                            typeHead[x] = R;
                    }
                }
            }
            if (!fr)
                continue;
            if (TBITS)
                TBit[(x << 8) + w] &= ~fr;
            vb[w] |= fr;
            vs[w >> 6] |= 1ULL << (w & 63);
            while (fr) {
                int b = __builtin_ctzll(fr);
                fr &= fr - 1;
                int p = i0 + b;
                changeStamp[p] = o;
                XSB(p) originalValue[p] = xid;
                slotType[p] = 0;
                publicGrid[p] = 0;
                pushSeed(p);
            }
        }
        return;
    }
    if (BLF && TBITS && s >= BLCOLL && (sN == 0 || c > RCBIG || F[0] == 0)) {
        const int xb = x << 8, nw = NW, cap = seedCap, h0 = typeHead[x], hw = h0 >> 6, hb = h0 & 63;
        int nS = nSeeds, h = h0, acc = s >> 1;
        typeSize[x] = sN;
        setType(x);
        for (int it = 0; it <= nw; it++) {
            int w = hw + it;
            if (w >= nw)
                w -= nw;
            ull part = it == 0 ? (~0ULL << hb) : (it == nw ? ((1ULL << hb) - 1) : ~0ULL);
            ull m = TBit[xb + w] & part;
            if (!m)
                continue;
            ull fr;
            if (sN == 0)
                fr = m;
            else {
                fr = 0;
                while (m) {
                    int b = __builtin_ctzll(m);
                    m &= m - 1;
                    acc += c;
                    int f = acc >= s;
                    acc -= f ? s : 0;
                    fr |= (ull)f << b;
                }
                if (!fr)
                    continue;
            }
            TBit[xb + w] &= ~fr;
            vb[w] |= fr;
            vs[w >> 6] |= 1ULL << (w & 63);
            const int i0 = w << 6;
            while (fr) {
                int p = i0 + __builtin_ctzll(fr);
                fr &= fr - 1;
                if (sN) {
                    int L = prevSame[p], R = nextSame[p];
                    nextSame[L] = R;
                    prevSame[R] = L;
                    if (h == p)
                        h = R;
                }
                changeStamp[p] = o;
                XSB(p) originalValue[p] = xid;
                slotType[p] = 0;
                publicGrid[p] = 0;
                if (nS < cap && !inq[p]) {
                    inq[p] = 1;
                    seedA[nS++] = p;
                }
            }
        }
        typeHead[x] = sN ? h : -1;
        nSeeds = nS;
        return;
    }
    if (sN == 0) {
        collectX(x, s);
        for (int p : xs) {
            changeStamp[p] = o;
            XSB(p) originalValue[p] = xid;
            slotType[p] = 0;
            publicGrid[p] = 0;
            vbSet(p);
            pushSeed(p);
        }
        if (TBITS)
            for (int w = 0; w < NW; w++)
                TBit[(x << 8) + w] = 0;
        typeHead[x] = -1;
        typeSize[x] = 0;
        setType(x);
        return;
    }
    typeSize[x] = sN;
    setType(x);
    collectX(x, s);
    if (c > RCBIG || F[0] == 0) {
        int acc = s >> 1;
        for (int k = 0; k < s; k++) {
            acc += c;
            if (acc >= s) {
                acc -= s;
                freeCell(xs[k]);
                pushSeed(xs[k]);
            }
        }
        return;
    }
    picks.clear();
    {
        int acc = s >> 1;
        for (int k = 0; k < s; k++) {
            acc += c;
            if (acc >= s) {
                acc -= s;
                picks.push_back(k);
            }
        }
    }
    int np = (int)picks.size();
    int prevK = -1;
    const int rw = c > CBIG ? RWB : RW;
    for (int j = 0; j < np; j++) {
        int k0 = picks[j];
        int lo = k0 - rw;
        if (lo <= prevK)
            lo = prevK + 1;
        int hi = k0 + rw;
        int nxt = j + 1 < np ? picks[j + 1] - 1 : s - 1;
        if (hi > nxt)
            hi = nxt;
        if (lo > hi) {
            lo = hi = k0 > prevK ? k0 : prevK + 1;
        }
        int bk = -1;
        ll bv = 0;
        int vL = -1, vR = -1, pPrev = -1;
        for (int k = lo; k <= hi; k++) {
            int p = xs[k];
            if (pPrev < 0 || (vL >= 0 && dist(pPrev, vR) < dist(pPrev, p))) {
                vL = prevVac(p);
                vR = vL >= 0 ? nextVac(vL) : -1;
            }
            pPrev = p;
            ll ins =
                vL < 0 ? 0 : wcst(0, dist(vL, p)) + wcst(0, dist(p, vR)) - wcst(0, dist(vL, vR));
            ll v = wremCostX(x, p) + ins;
            if (bk < 0 || v < bv) {
                bv = v;
                bk = k;
            }
        }
        freeCell(xs[bk]);
        pushSeed(xs[bk]);
        prevK = bk;
    }
}
