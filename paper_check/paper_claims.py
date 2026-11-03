"""Line-by-line audit of the LaTeX source, keyed to the paper's own statement labels.

Every claim is checked exactly (Fractions) at every admissible parameter value.
Range: K = 3..40 (exhaustive) unless a claim's own scope is narrower.
"""
from fractions import Fraction as F

FAILS = []
NCHECK = 0


def ck(cond, label, detail=''):
    global NCHECK
    NCHECK += 1
    if not cond:
        FAILS.append((label, detail))


# ---------------------------------------------------------------- notation (§4)
def r_(K): return K // 2
def e_(K): return K % 2
def s_(K, k): return K // 2 - k + 1 + K % 2
def t_(K, k): return K - k
def bd(K, k): return e_(K) == 1 and s_(K, k) == 1


def M(K, k, l):
    """M_{eps,s}(l) of §5.1."""
    s, m = s_(K, k), l // 2
    if bd(K, k):                      # eps=1, s=1
        return F(m * m) if l % 2 == 0 else F(m * (m + 1))
    return F(m * (s - 1 + m)) if l % 2 == 0 else F(m * (m + s)) + F(s, 2)


def qstar(K, k): return 1 - F(s_(K, k), 2 * t_(K, k))
def ql(K, k, l): return 1 - M(K, k, l) / F(l * t_(K, k))
def q0(K, k): return F(3 * K - 2 * k - 2, 4 * (K - k))
def q1(K, k): return q0(K, k) / k + F(k - 1, k)


KS = range(3, 41)

# ------------------------------------------------- Lemma 2 / Remark 1 (§3)
for K in KS:
    for k in range(1, r_(K) + 1):
        ck(t_(K, k) == r_(K) + s_(K, k) - 1, 'Remark 1: t = r+s-1', f'K={K} k={k}')
        ck(s_(K, k) >= 1, 'Remark 1: s >= 1', f'K={K} k={k}')
        if e_(K) == 1:
            ck(s_(K, k) >= 2, 'Remark 1: odd K, k<=r => s>=2', f'K={K} k={k}')

# Lemma 2 itself: for a ballot, count the nonmembers preceding a below/on-line member.
# (enumerated exhaustively over all ballots for small K)
import itertools
for K in range(3, 6):
    r, eps = r_(K), e_(K)
    for k in range(1, r + 1):
        s = s_(K, k)
        C = set(range(k))
        for kk in range(k):
            a = kk
            D = [d for d in range(K) if d not in C]
            for perm in itertools.permutations(range(K)):
                rank = perm.index(a) + 1          # 1-based
                # t - w_i(a) = #nonmembers that BEAT a in this ballot
                tw = sum(1 for d in D if perm.index(d) < perm.index(a))
                if rank > K - r:                  # below the line
                    ck(tw >= s, 'Lemma 2: below => t-w >= s',
                       f'K={K} k={k} a={a} rank={rank} t-w={tw} s={s}')
                elif rank == r + 1:               # on the line (odd K only)
                    ck(eps == 1, 'Lemma 2: on-line only if eps=1', f'K={K}')
                    ck(tw >= s - 1, 'Lemma 2: on-line => t-w >= s-1',
                       f'K={K} k={k} a={a} t-w={tw} s={s}')
                else:
                    ck(tw >= 0, 'Lemma 2: above => t-w >= 0', f'K={K}')

# ------------------------------------------------- §4: q* and its bounds
for K in KS:
    for k in range(1, r_(K) + 1):
        eps = e_(K)
        ck(2 * (2 * t_(K, k) - s_(K, k)) == 3 * K - 2 * k - 2 - eps,
           '§4: 2t-s / 2t = (3K-2k-2-eps)/(4t)', f'K={K} k={k}')
        ck(qstar(K, k) == F(3 * K - 2 * k - 2 - eps, 4 * (K - k)),
           '§4: closed form of q*', f'K={K} k={k}')
        ck(1 <= s_(K, k) <= t_(K, k), '§4: 1 <= s <= t', f'K={K} k={k}')
        if K >= 4:
            ck(s_(K, k) < t_(K, k), '§4: K>=4 => s<t', f'K={K} k={k}')
            ck(F(1, 2) < qstar(K, k) < 1, '§4: 1/2 < q* < 1', f'K={K} k={k}')
ck((s_(3, 1), t_(3, 1)) == (2, 2) and qstar(3, 1) == F(1, 2),
   '§4: K=3,k=1 => s=t=2, q*=1/2')

# ------------------------------------------------- §5.1: M <= l t/2, q_l in [1/2,1]
for K in KS:
    for k in range(1, K // 2 + e_(K) + 1):
        for l in range(1, k + 1):
            ck(M(K, k, l) <= F(l * t_(K, k), 2), '§5.1: M <= l t/2', f'K={K} k={k} l={l}')
            ck(F(1, 2) <= ql(K, k, l) <= 1, '§5.1: q_l* in [1/2,1]', f'K={K} k={k} l={l}')

# §5.1 note: 2 M_{1,1}(l) - l s = 2m^2 - 1 at the boundary, odd l
for K in range(3, 40, 2):
    k = r_(K) + 1
    for m in range(0, 8):
        l = 2 * m + 1
        if l > k:
            break
        ck(2 * M(K, k, l) - l * s_(K, k) == 2 * m * m - 1,
           '§5.1 note: boundary 2M-ls = 2m^2-1', f'K={K} l={l}')

# ------------------------------------------------- Corollary 1
for K in KS:
    for k in range(2, r_(K) + 1):
        ck(ql(K, k, 1) == qstar(K, k) and ql(K, k, 2) == qstar(K, k),
           'Cor 1(a): q_1* = q_2* = q*', f'K={K} k={k}')
        for l in range(1, k + 1):
            ck(2 * M(K, k, l) - l * s_(K, k) == 2 * (((l - 1) ** 2) // 4),
               'Cor 1(b): 2M - l s = 2 floor((l-1)^2/4)', f'K={K} k={k} l={l}')
            if l >= 3:
                ck(ql(K, k, l) == qstar(K, k) - F(((l - 1) ** 2) // 4, l * t_(K, k)),
                   'Cor 1(b): q_l* = q* - floor/l t', f'K={K} k={k} l={l}')
                ck(ql(K, k, l) < qstar(K, k), 'Cor 1(b): q_l* < q* for l>=3',
                   f'K={K} k={k} l={l}')
        ck(ql(K, k, k) == qstar(K, k) - F(((k - 1) ** 2) // 4, k * t_(K, k)),
           'Cor 1(c): q_comp* formula', f'K={K} k={k}')
        if k == 2:
            if e_(K) == 0:
                ck(ql(K, k, k) == q0(K, k), 'Cor 1(c): even K, k=2 => q_comp*=q_0',
                   f'K={K}')
            else:
                ck(ql(K, k, k) < q0(K, k), 'Cor 1(c): odd K, k=2 => q_comp*<q_0',
                   f'K={K}')
        if k >= 3:
            ck(ql(K, k, k) < q0(K, k), 'Cor 1(c): k>=3 => q_comp*<q_0', f'K={K} k={k}')
            if e_(K) == 0:
                ck(qstar(K, k) == q0(K, k), 'Cor 1(c): even K => q*=q_0', f'K={K} k={k}')
            else:
                ck(qstar(K, k) < q0(K, k), 'Cor 1(c): odd K => q*<q_0', f'K={K} k={k}')
# Cor 1(d): odd boundary
for K in range(3, 40, 2):
    k = r_(K) + 1
    ck(ql(K, k, 1) == 1, 'Cor 1(d): boundary q_1* = 1', f'K={K}')
    if k >= 2:
        ck(ql(K, k, 2) < 1, 'Cor 1(d): boundary q_2* < 1', f'K={K}')

# ------------------------------------------------- Corollary 2 + Example 1
for K in range(3, 40, 2):
    k, rr = r_(K) + 1, r_(K)
    ck(q0(K, k) == 1 - F(1, 4 * rr), 'Cor 2: q_0 = 1 - 1/(4r)', f'K={K}')
    if k >= 2:
        ck(M(K, k, k) * 4 > k, 'Cor 2: M_{1,1}(k)/k > 1/4', f'K={K} k={k}')
        ck(ql(K, k, k) < q0(K, k), 'Cor 2: q_k* < q_0 at the boundary', f'K={K}')
        m = (k - 2) // 2 if k % 2 == 0 else 0
        if k % 2 == 0:
            ck(F(M(K, k, k), k) == F(k // 2, 2), 'Cor 2: k=2m => M/k = m/2', f'K={K}')
        else:
            mm = (k - 1) // 2
            ck(F(M(K, k, k), k) == F(mm * (mm + 1), 2 * mm + 1),
               'Cor 2: k=2m+1 => M/k = m(m+1)/(2m+1)', f'K={K}')
ck(ql(3, 2, 2) == F(1, 2) and q0(3, 2) == F(3, 4), 'Cor 2: K=3,k=2 => q_k*=1/2<3/4')

ck((ql(5, 3, 1), ql(5, 3, 2), ql(5, 3, 3)) == (F(1), F(3, 4), F(2, 3)),
   'Ex 1: q_1*, q_2*, q_comp* = 1, 3/4, 2/3')
ck(q0(5, 3) == F(7, 8) and q1(5, 3) == F(23, 24), 'Ex 1: q_0=7/8, q_1=23/24')
ck((M(5, 3, 1), M(5, 3, 2), M(5, 3, 3)) == (0, 1, 2), 'Ex 1: M_{1,1} = 0,1,2')

# ------------------------------------------------- §7.1 comparison
for K in KS:
    for k in range(1, K // 2 + e_(K) + 1):
        ck(q1(K, k) - q0(K, k) == F(k - 1, k) * (1 - q0(K, k)),
           '§7.1: q_1-q_0 = (k-1)(1-q_0)/k', f'K={K} k={k}')
        ck((q0(K, k) < 1) == (2 * k < K + 2), '§5.1: q_0<1 iff 2k<K+2', f'K={K} k={k}')
        ck((q1(K, k) >= q0(K, k)) == (q0(K, k) <= 1),
           '§7.1: q_0<=q_1 iff q_0<=1', f'K={K} k={k}')
        if k > 1 and q0(K, k) < 1:
            ck(q1(K, k) > q0(K, k), '§7.1: q_1>q_0 for k>1, q_0<1', f'K={K} k={k}')
        if 2 * k == K + 2:
            ck(q0(K, k) == 1 and q1(K, k) == 1, '§7.1: k=(K+2)/2 => q_0=q_1=1',
               f'K={K} k={k}')
        if e_(K) == 0 and k <= r_(K):
            ck(qstar(K, k) == q0(K, k), '§7.1: even K => q*=q_0', f'K={K} k={k}')
        if e_(K) == 1 and k <= r_(K):
            ck(qstar(K, k) == q0(K, k) - F(1, 4 * t_(K, k)),
               '§7.1: odd K => q*=q_0-1/(4t)', f'K={K} k={k}')
            ck(qstar(K, k) < q0(K, k) <= q1(K, k), '§7.1: q*<q_0<=q_1 (odd K)',
               f'K={K} k={k}')

# §7.3 Mahajne-Volij recovery
for K in KS:
    want = F(3 * K - 4, 4 * K - 4) if e_(K) == 0 else F(3 * K - 5, 4 * K - 4)
    ck(qstar(K, 1) == want, '§7.3: k=1 recovers Mahajne-Volij', f'K={K}')

# ------------------------------------------------- the "sharp only at even K, k=2" claim
sharp = [(K, k) for K in KS for k in range(1, r_(K) + 1) if ql(K, k, k) == q0(K, k)]
ck(all(e_(K) == 0 for K, k in sharp), 'abstract: sharpness only for even K')
ck(all(k <= 2 for K, k in sharp),
   'abstract: sharpness only for k=2  <-- fails iff k=1 also occurs')
print('pairs where q_comp* = q_0 (i.e. q_0 is sharp):', sorted(set(k for K, k in sharp)))
print('  e.g.', sharp[:6])

# ---------------- the revised (v2) statements about the degenerate k=1 case -------------
# abstract: sharp, on 2<=k<=r, only for even K and k=2
restricted = [(K, k) for (K, k) in sharp if 2 <= k <= r_(K)]
ck(all(e_(K) == 0 and k == 2 for K, k in restricted),
   'v2 abstract: on 2<=k<=r, q_0 sharp only for even K, k=2')
ck(all(ql(K, k, k) < q0(K, k) for K in KS for k in range(3, r_(K) + 1)),
   'v2 abstract: 3<=k<=r => q_comp* < q_0')
# abstract/intro/conclusion: at k=1, q_0 = q* is sharp for even K as well
for K in KS:
    if e_(K) == 0:
        ck(ql(K, 1, 1) == q0(K, 1) and qstar(K, 1) == q0(K, 1),
           'v2: k=1, even K => q_comp* = q* = q_0 (sharp)', f'K={K}')
    else:
        ck(ql(K, 1, 1) == qstar(K, 1) < q0(K, 1),
           'v2: k=1, odd K => q_comp* = q* < q_0 (not sharp)', f'K={K}')
# §7.1: at k=1, q_1 = q_0 and q* = q_0 - 1/(4(K-1)) for odd K
for K in range(3, 40, 2):
    ck(q1(K, 1) == q0(K, 1), 'v2 §7.1: k=1 => q_1 = q_0', f'K={K}')
    ck(qstar(K, 1) == q0(K, 1) - F(1, 4 * (K - 1)),
       'v2 §7.1: odd K, k=1 => q* = q_0 - 1/(4(K-1))', f'K={K}')
# abstract: "already loose at the odd boundary k=2" (the minimal odd boundary, K=3)
ck(ql(3, 2, 2) < q0(3, 2), 'v2 abstract: K=3,k=2 (odd boundary) => q_comp* < q_0')
# and, in range, odd K with k=2 is loose as well
for K in range(5, 40, 2):
    ck(ql(K, 2, 2) < q0(K, 2), 'v2: odd K >= 5, k=2 in range => q_comp* < q_0', f'K={K}')
# Corollary 1(c) v2 wording: "for 3<=k<=r" (odd K: q_comp*<q*<q_0; even: <q* = q_0)
for K in KS:
    for k in range(3, r_(K) + 1):
        if e_(K) == 1:
            ck(ql(K, k, k) < qstar(K, k) < q0(K, k), 'v2 Cor 1(c) odd K', f'K={K} k={k}')
        else:
            ck(ql(K, k, k) < qstar(K, k) == q0(K, k), 'v2 Cor 1(c) even K', f'K={K} k={k}')

# §7.2 the K=4,k=2 Diss-Mahajne family, re-derived symbolically
for m in (1, 2, 3, 10):
    n = 12 * m + 1
    ck(F(9 * m) < F(3 * n, 4), '§7.2: 9m < 3n/4 (so NOT 3/4-Condorcet)', f'm={m}')
    ck(9 * m > 0 and F(9 * m, n) < F(3, 4), '§7.2 margin ratio < 3/4', f'm={m}')

# ============ v3: the Remark 2 clarification and the restated 7.1 range ============
# Remark 2: retaining s/2 gives nt - W > ns/2  <=>  W < n(3K-2k-3)/4   (odd K),
# and relaxing to the parity-free bound gives nt - W > n(s/2 - eps/4).
for K in KS:
    for k in range(1, r_(K) + 1):
        A = 3 * K - 2 * k - 2
        # 4t - A = 2s - eps   (so (4t-A)/4 = s/2 - eps/4)
        ck(4 * t_(K, k) - A == 2 * s_(K, k) - e_(K),
           'v3 Remark 2: 4t-(3K-2k-2) = 2s-eps', f'K={K} k={k}')
        # q_0 - q* = eps/(4t)
        ck(q0(K, k) - qstar(K, k) == F(e_(K), 4 * t_(K, k)),
           'v3 Remark 2: q_0-q* = eps/(4t)', f'K={K} k={k}')
        if e_(K) == 1:
            # t - s/2 = (3K-2k-3)/4, i.e. the sharp odd-K bound
            ck(4 * t_(K, k) - 2 * s_(K, k) == 3 * K - 2 * k - 3,
               'v3 Remark 2: 4(t-s/2) = 3K-2k-3 (odd K)', f'K={K} k={k}')

# v3 Remark 2, closing link: the two bounds give exactly q* and q_0 as thresholds.
# Retaining s/2 -> threshold 1 - (s/2)/t = q*;  relaxing to s/2 - eps/4 -> threshold 1 - (s/2-eps/4)/t = q_0.
for K in KS:
    for k in range(1, r_(K) + 1):
        ck(1 - F(s_(K, k), 2 * t_(K, k)) == qstar(K, k),
           'v3 Remark 2: retained bound yields q*', f'K={K} k={k}')
        if e_(K) == 1:
            ck(1 - (F(s_(K, k), 2) - F(1, 4)) / t_(K, k) == q0(K, k),
               'v3 Remark 2: relaxed bound yields q_0 (odd K)', f'K={K} k={k}')

# v3 7.1: for odd K, q_0 is loose for complete unacceptability for ALL 2 <= k <= r
for K in range(5, 40, 2):
    for k in range(2, r_(K) + 1):
        ck(ql(K, k, k) < q0(K, k), 'v3 7.1: odd K, 2<=k<=r => q_comp* < q_0', f'K={K} k={k}')
# both k=2 cases named in the abstract / 7.1
ck(ql(3, 2, 2) < q0(3, 2), 'v3: boundary K=3, k=2=r+1 => loose')
for K in range(5, 40, 2):
    ck(ql(K, 2, 2) < q0(K, 2), 'v3: in-range odd K>=5, k=2<=r => loose', f'K={K}')

# Lemma 2, exact per-ballot deficits (not just inequalities): the bounds are attained
for K in (5, 7):
    r, eps = r_(K), e_(K)
    for k in range(1, r + 1):
        s = s_(K, k)
        D = [d for d in range(K) if d >= k]
        seen_below = seen_on = False
        for perm in itertools.permutations(range(K)):
            rank = perm.index(0) + 1
            tw = sum(1 for d in D if perm.index(d) < perm.index(0))
            if rank > K - r and tw == s:
                seen_below = True
            if rank == r + 1 and tw == s - 1:
                seen_on = True
        ck(seen_below, 'v3 Lemma 2: below-line bound s is attained', f'K={K} k={k}')
        if eps == 1:
            ck(seen_on, 'v3 Lemma 2: on-line bound s-1 is attained', f'K={K} k={k}')

print()
print('assertions checked:', NCHECK)
print('failures:', len(FAILS))
for lab, det in FAILS[:20]:
    print('  FAIL', lab, det)
print('OK' if not FAILS else 'FAILURES ABOVE')
