"""Exact rational LP (two-phase simplex, Bland's rule) for the social-choice model
of Gogoi, "Sharp Qualified-Majority Thresholds for Social Acceptability of
q-Condorcet Committees".

Model.  Let A be a K-element set of alternatives, C a k-element committee,
D = A \\ C, r = floor(K/2), eps = K mod 2, t = K - k.
For a ranking (0-indexed rank 0 = best):
    a is ABOVE the line  iff rank a <= r-1
    a is ON    the line  iff eps = 1 and rank a = r
    a is BELOW the line  iff rank a >= r+eps
beta_a = (#below) - (#above)          (a is "unacceptable" iff beta_a > 0)
m_{a,d} = fraction of voters with a above d.

LP for a fixed U (|U| = ell, U subset C):
    maximise t  subject to
        beta_a(x) - t >= 0            (a in U)
        m_{a,d}(x) - q*sum(x) >= 0    ((a,d) in C x D)
        sum(x) = 1 ,  x >= 0,  t free
The optimum is >0  iff there is a (fractional, hence after scaling rational, hence
realisable by a finite profile) weak q-Condorcet committee of size k having at least
ell socially unacceptable members.  So sufficiency of q holds iff the optimum is <=0
for every U.
"""
from fractions import Fraction as F
from itertools import permutations, combinations


# --------------------------------------------------------------- exact simplex
def simplex_max(c, A, b):
    """maximise c.x subject to A x = b, x >= 0 (b >= 0).
    Returns (status, value, x)."""
    m = len(A)
    n = len(c)
    T = [[F(A[i][j]) for j in range(n)] + [F(1) if j == i else F(0) for j in range(m)] + [F(b[i])]
         for i in range(m)]
    basis = [n + i for i in range(m)]
    N = n + m

    def pivot(r, j):
        pv = T[r][j]
        if pv != 1:
            T[r] = [v / pv for v in T[r]]
        Tr = T[r]
        for i in range(m):
            if i != r:
                f = T[i][j]
                if f:
                    Ti = T[i]
                    T[i] = [Ti[k] - f * Tr[k] for k in range(N + 1)]
        basis[r] = j

    def run(cost, allowed):
        while True:
            enter = -1
            for j in range(N):
                if j not in allowed or j in basis:
                    continue
                rc = cost[j] if j < len(cost) else F(0)
                for i in range(m):
                    rc -= cost[basis[i]] * T[i][j]
                if rc > 0:          # maximise: enter on positive reduced cost
                    enter = j
                    break
            if enter < 0:
                return
            leave = -1
            best = None
            for i in range(m):
                aij = T[i][enter]
                if aij > 0:
                    ratio = T[i][N] / aij
                    if best is None or ratio < best or (ratio == best and basis[i] < basis[leave]):
                        best = ratio
                        leave = i
            if leave < 0:
                return 'unbounded'
            pivot(leave, enter)

    cost1 = [F(0)] * n + [F(-1)] * m
    run(cost1, set(range(N)))
    art = sum(T[i][N] for i in range(m) if basis[i] >= n)
    if art != 0:
        return ('infeasible', None, None)
    for i in range(m):
        if basis[i] >= n:
            for j in range(n):
                if j not in basis and T[i][j] != 0:
                    pivot(i, j)
                    break
    cost2 = [F(v) for v in c] + [F(0)] * m
    run(cost2, set(range(n)))
    val = sum(cost2[basis[i]] * T[i][N] for i in range(m))
    x = [F(0)] * N
    for i in range(m):
        x[basis[i]] = T[i][N]
    return ('optimal', val, x[:n])


# ------------------------------------------------------------------ the model
_cache = {}


def model(K):
    if K not in _cache:
        perms = list(permutations(range(K)))
        rank = [[0] * K for _ in perms]
        for ti, p in enumerate(perms):
            for i, a in enumerate(p):
                rank[ti][a] = i
        _cache[K] = (perms, rank)
    return _cache[K]


def lp_value(K, k, ell, q, U=None):
    """max over all U of size ell inside C={0..k-1} of the LP value (or just for U)."""
    perms, rank = model(K)
    r = K // 2
    eps = K % 2
    C = list(range(k))
    D = list(range(k, K))
    pairs = [(a, d) for a in C for d in D]
    Us = [list(U)] if U is not None else [list(u) for u in combinations(C, ell)]
    best = None
    bestU = None
    for U in Us:
        sigs = {}
        for ti in range(len(perms)):
            rk = rank[ti]
            s = tuple((1 if rk[a] >= r + eps else 0) - (1 if rk[a] <= r - 1 else 0) for a in U) \
                + tuple(1 if rk[a] < rk[d] else 0 for (a, d) in pairs)
            sigs.setdefault(s, []).append(ti)
        keys = list(sigs)
        n = len(keys)
        nrows = len(U) + len(pairs)
        ncol = n + 2 + nrows          # x, t+, t-, one surplus per '>=' row
        A = []
        b = []
        for ui in range(len(U)):
            row = [F(s[ui]) for s in keys] + [F(-1), F(1)] + [F(0)] * nrows
            row[n + 2 + ui] = F(-1)
            A.append(row)
            b.append(F(0))
        for pi in range(len(pairs)):
            row = [F(s[len(U) + pi]) - F(q) for s in keys] + [F(0), F(0)] + [F(0)] * nrows
            row[n + 2 + len(U) + pi] = F(-1)
            A.append(row)
            b.append(F(0))
        A.append([F(1)] * n + [F(0)] * (2 + nrows))
        b.append(F(1))
        c = [F(0)] * n + [F(1), F(-1)] + [F(0)] * nrows
        assert all(len(r) == ncol for r in A)
        st, val, _ = simplex_max(c, A, b)
        if st == 'infeasible':
            val = None
        if val is not None and (best is None or val > best):
            best = val
            bestU = U
    return best, bestU


# ------------------------------------------------------- paper's closed formula
def r_(K):
    return K // 2


def s_(K, k):
    return K // 2 - k + 1 + (K % 2)


def Mfun(K, k, ell):
    r, eps, s = K // 2, K % 2, s_(K, k)
    if not (eps == 1 and s == 1):
        if ell % 2 == 0:
            m = ell // 2
            return F(m * (s - 1 + m))
        else:
            m = ell // 2
            return F(m * (m + s)) + F(s, 2)
    else:
        if ell % 2 == 0:
            m = ell // 2
            return F(m * m)
        else:
            m = ell // 2
            return F(m * (m + 1))


def qstar(K, k, ell):
    t = K - k
    return 1 - Mfun(K, k, ell) / (ell * t)
