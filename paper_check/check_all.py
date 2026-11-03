"""Exhaustive audit of every displayed numerical assertion in the paper
(all K from 3 to 40, all k, all l).  Exits non-zero on the first failure."""
from fractions import Fraction as F
from math import comb

bad = []


def chk(cond, msg):
    if not cond:
        bad.append(msg)


def r_(K): return K // 2
def eps(K): return K % 2
def s_(K, k): return K // 2 - k + 1 + K % 2
def t_(K, k): return K - k
def bd(K, k): return eps(K) == 1 and s_(K, k) == 1


def M(K, k, l):
    s = s_(K, k)
    m = l // 2
    if not bd(K, k):
        return F(m * (s - 1 + m)) if l % 2 == 0 else F(m * (m + s)) + F(s, 2)
    return F(m * m) if l % 2 == 0 else F(m * (m + 1))


def qstar(K, k): return 1 - F(s_(K, k), 2 * t_(K, k))
def ql(K, k, l): return 1 - M(K, k, l) / (l * t_(K, k))
def q0(K, k): return F(3 * K - 2 * k - 2, 4 * (K - k))
def q1(K, k): return q0(K, k) / k + F(k - 1, k)


for K in range(3, 41):
    r, e = r_(K), eps(K)
    for k in range(1, K):
        # Remark 1
        if k <= r or (e == 1 and k == r + 1):
            chk(t_(K, k) == r + s_(K, k) - 1, f't=r+s-1 K={K} k={k}')
        # (2.1) the two forms of q*
        if k <= r:
            chk(2 * (2 * t_(K, k) - s_(K, k)) == 3 * K - 2 * k - 2 - e,
                f'q* numerator K={K} k={k}')
            chk(qstar(K, k) == F(3 * K - 2 * k - 2 - e, 4 * (K - k)),
                f'q* closed form K={K} k={k}')
            chk(s_(K, k) >= (2 if e == 1 else 1), f's bound K={K} k={k}')
            chk(1 <= s_(K, k) <= t_(K, k), f'1<=s<=t K={K} k={k}')
            if K >= 4:
                chk(F(1, 2) < qstar(K, k) < 1, f'q* in (1/2,1) K={K} k={k}')
        # q_0 properties
        chk((q0(K, k) < 1) == (k < F(K + 2, 2)), f'q0<1 iff k<(K+2)/2 K={K} k={k}')
        if k > 1:
            # q1 - q0 = (k-1)(1-q0)/k, so the comparison is exactly q0 <= 1
            chk((q1(K, k) >= q0(K, k)) == (q0(K, k) <= 1), f'q1>=q0 iff q0<=1 K={K} k={k}')
            if q0(K, k) <= 1:
                chk(q1(K, k) >= q0(K, k), f'q1>=q0 K={K} k={k}')
            else:
                chk(q1(K, k) > 1, f'q0>1 => q1>1 K={K} k={k}')
        else:
            chk(q1(K, k) == q0(K, k), f'q1=q0 at k=1 K={K} k={k}')
        # even K: q* = q_0
        if k <= r:
            if e == 0:
                chk(qstar(K, k) == q0(K, k), f'even q*=q0 K={K} k={k}')
                if k > 1:
                    chk(q1(K, k) > qstar(K, k), f'q1>q* even k>1 K={K} k={k}')
            else:
                chk(qstar(K, k) == q0(K, k) - F(1, 4 * (K - k)),
                    f'odd q*=q0-1/(4t) K={K} k={k}')
                chk(q0(K, k) <= q1(K, k), f'odd q0<=q1 K={K} k={k}')
        # the hierarchy
        if k <= r + e:
            for l in range(1, k + 1):
                Mv = M(K, k, l)
                # M <= l t / 2
                chk(Mv <= F(l * t_(K, k), 2), f'M<=lt/2 K={K} k={k} l={l}')
                chk(F(1, 2) <= ql(K, k, l) <= 1, f'q_l in [1/2,1] K={K} k={k} l={l}')
                # the floor identity, only in the regular regime (as the paper uses it)
                if not bd(K, k):
                    chk(2 * Mv - l * s_(K, k) == F(2 * ((l - 1) ** 2 // 4)),
                        f'floor identity K={K} k={k} l={l}')
                    if 2 <= k <= r:
                        chk(ql(K, k, l) == qstar(K, k) - F((l - 1) ** 2 // 4, l * t_(K, k)),
                            f'Cor 1(b) K={K} k={k} l={l}')
                # monotone in l
                if l > 1:
                    chk(ql(K, k, l) <= ql(K, k, l - 1), f'monotone in l K={K} k={k} l={l}')
            # Corollary 1(a)
            if not bd(K, k):
                chk(ql(K, k, 1) == qstar(K, k), f'q1*=q* K={K} k={k}')
                chk(ql(K, k, 2) == qstar(K, k), f'q2*=q* K={K} k={k}')
            else:
                chk(ql(K, k, 1) == 1, f'boundary q1*=1 K={K} k={k}')
                chk(M(K, k, 1) == 0 and M(K, k, 2) == 1, f'boundary M K={K} k={k}')

# Corollary 1(c): complete-unacceptability threshold vs q_0
for K in range(4, 41):
    r, e = r_(K), eps(K)
    for k in range(2, r + 1):
        qc = ql(K, k, k)
        if e == 0 and k == 2:
            chk(qc == q0(K, k), f'comp=q0 even k=2 K={K}')
        else:
            chk(qc < q0(K, k) if not (e == 0) else qc < q0(K, k),
                f'comp<q0 K={K} k={k}')

# Corollary 1(d) and Corollary 2 at the odd boundary
for K in range(3, 41, 2):
    r = K // 2
    k = r + 1
    chk(ql(K, k, 1) == 1, f'bd q1*=1 K={K}')
    chk(ql(K, k, 2) < 1, f'bd q2*<1 K={K}')
    if k >= 2:
        chk(ql(K, k, k) < q0(K, k), f'Cor2 q_k*<q0 K={K}')

# Example 1
chk((ql(5, 3, 1), ql(5, 3, 2), ql(5, 3, 3)) == (F(1), F(3, 4), F(2, 3)),
    'Example 1 thresholds')
chk(q0(5, 3) == F(7, 8) and q1(5, 3) == F(23, 24), 'Example 1 q0,q1')

# Mahajne-Volij recovery at k = 1
for K in range(3, 41):
    want = F(3 * K - 4, 4 * K - 4) if eps(K) == 0 else F(3 * K - 5, 4 * K - 4)
    chk(qstar(K, 1) == want, f'MV k=1 K={K}')

# K = 3, k = 1 : q* = 1/2
chk(qstar(3, 1) == F(1, 2), 'K=3 k=1 q*=1/2')

print('number of failed assertions:', len(bad))
for b in bad[:40]:
    print('  FAIL:', b)
print('OK' if not bad else 'FAILURES ABOVE')
