"""Exact verification of the explicit profiles appearing in the paper.

A profile is a dict  ballot (tuple, 0-indexed rank order) -> positive rational multiplicity.
All checks are exact (integer / Fraction arithmetic).
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, lcm


# ------------------------------------------------------------------ core utilities
def counts(profile, K, C):
    """Return (n, n_ab, A, B, O) where A[a], B[a], O[a] are above/on/below counts."""
    n = sum(profile.values())
    D = [x for x in range(K) if x not in C]
    nab = {(a, b): F(0) for a in C for b in D}
    A = {a: F(0) for a in C}
    B = {a: F(0) for a in C}
    O = {a: F(0) for a in C}
    r = K // 2
    eps = K % 2
    for ballot, w in profile.items():
        assert len(ballot) == K and sorted(ballot) == list(range(K)), f"not a permutation: {ballot}"
        pos = {a: i for i, a in enumerate(ballot)}
        for a in C:
            for b in D:
                if pos[a] < pos[b]:
                    nab[(a, b)] += w
            if pos[a] <= r - 1:
                A[a] += w
            elif pos[a] >= r + eps:
                B[a] += w
            else:
                O[a] += w
    return n, nab, A, B, O


def check(profile, K, k, q, mode='strict', verbose=True, label=''):
    C = list(range(k))
    n, nab, A, B, O = counts(profile, K, C)
    worst = None
    okq = True
    for key, v in nab.items():
        ok = (v > q * n) if mode == 'strict' else (v >= q * n)
        if not ok:
            okq = False
            if worst is None or v - q * n < worst[1]:
                worst = (key, v - q * n)
    unacc = [a for a in C if B[a] > A[a]]
    if verbose:
        print(f'  [{label}] n={n}  q-Condorcet({mode}) = {okq}'
              f'{"  worst margin " + str(worst) if worst else ""}')
        print(f'     A={A}  B={B}  O={O}   unacceptable = {unacc}')
    return okq, unacc, (n, nab, A, B, O)


def perm_from_order(blocks):
    out = []
    for b in blocks:
        out.extend(b)
    return tuple(out)


def scale_int(profile):
    """scale so all weights become positive integers"""
    den = 1
    for w in profile.values():
        den = den * w.denominator // gcd(den, w.denominator)
    out = {}
    for k_, v in profile.items():
        iv = int(v * den)
        if iv:
            out[k_] = out.get(k_, 0) + iv
    g = 0
    for w in out.values():
        g = gcd(g, w)
    if g > 1:
        out = {k_: v // g for k_, v in out.items()}
    return out


def merge(*profs):
    out = {}
    for p in profs:
        for k_, v in p.items():
            out[k_] = out.get(k_, F(0)) + v
    return out


# ------------------------------------------------------------ Theorem 2 (l = 1)
def thm2_profile(K, k, rho):
    """Theorem 2's construction.  The bad blocks carry total mass rho, the good blocks
    total mass 1 - rho, uniformly over all choices (so that the fraction of ballots in
    which a fixed pair (a_1,d) is a defeat is exactly rho * s / t)."""
    r = K // 2
    eps = K % 2
    s = r - k + 1 + eps
    t = K - k
    C = list(range(k))
    D = list(range(k, K))
    a1 = C[0]
    rest = C[1:]
    prof = {}
    nS = len(list(combinations(D, s)))
    if eps == 0:
        wbad = rho / nS
    else:
        wbad = rho / (nS * s)
    wgood = (1 - rho) / nS
    for S in combinations(D, s):
        S = list(S)
        comp = [d for d in D if d not in S]
        if eps == 0:
            bal = perm_from_order([rest, S, [a1], comp])
            prof[bal] = prof.get(bal, F(0)) + wbad
        else:
            for dO in S:
                SA = [d for d in S if d != dO]
                bal = perm_from_order([rest, SA, [dO], [a1], comp])
                prof[bal] = prof.get(bal, F(0)) + wbad
        bal = perm_from_order([rest, [a1], D])
        prof[bal] = prof.get(bal, F(0)) + wgood
    return prof


# ------------------------------------------------- Theorem 3(b), eps=0 or s >= 2
def thm3_profile(K, k, ell, lam):
    """Theorem 3(b) for eps = 0 or s >= 2.  lam = (weight of state p, weight of state p+1);
    the *total* mass of state b is lam[b-p]."""
    r = K // 2
    eps = K % 2
    s = r - k + 1 + eps
    t = K - k
    C = list(range(k))
    D = list(range(k, K))
    U = C[:ell]
    rest = C[ell:]
    p = ell // 2
    prof = {}
    for idx, b in enumerate([p, p + 1]):
        mass = lam[idx]
        if mass == 0:
            continue
        shat = s - 1 + b
        nB = len(list(combinations(U, b)))
        nS = len(list(combinations(D, shat)))
        nO = shat if eps == 1 else 1
        w = mass / (nB * nS * nO)
        for Bset in combinations(U, b):
            for Shat in combinations(D, shat):
                Bset = list(Bset)
                Shat = list(Shat)
                comp = [d for d in D if d not in Shat]
                UB = [u for u in U if u not in Bset]
                if eps == 1:
                    for dO in Shat:
                        SA = [d for d in Shat if d != dO]
                        bal = perm_from_order([rest, UB, SA, [dO], Bset, comp])
                        prof[bal] = prof.get(bal, F(0)) + w
                else:
                    bal = perm_from_order([rest, UB, Shat, Bset, comp])
                    prof[bal] = prof.get(bal, F(0)) + w
    return prof


# --------------------------------- Theorem 3(b), odd boundary eps=1, s=1, k=r+1
def thm3_boundary_state(K, k, ell, which, mass):
    """One state family with the given total mass.  which = ('A', b) or ('B', b)."""
    r = K // 2
    t = K - k
    C = list(range(k))
    D = list(range(k, K))
    U = C[:ell]
    rest = C[ell:]
    kind, b = which
    prof = {}
    if kind == 'A':
        nB = len(list(combinations(U, b)))
        nS = len(list(combinations(D, b)))
        nO = b if b >= 1 else 1
        w = mass / (nB * nS * nO)
        for Bset in combinations(U, b):
            Bset = list(Bset)
            comp_users = [u for u in U if u not in Bset]
            for Shat in combinations(D, b):
                Shat = list(Shat)
                comp = [d for d in D if d not in Shat]
                if b >= 1:
                    for dO in Shat:
                        SA = [d for d in Shat if d != dO]
                        bal = perm_from_order([rest, comp_users, SA, [dO], Bset, comp])
                        prof[bal] = prof.get(bal, F(0)) + w
                else:
                    assert len(rest) >= 1, 'the A_0 state needs C\\U nonempty'
                    bal = perm_from_order([[rest[0]], rest[1:], comp_users, [],
                                           Bset, D])
                    prof[bal] = prof.get(bal, F(0)) + w
    else:
        nB = len(list(combinations(U, b)))
        nS = len(list(combinations(D, b)))
        nO = len(U) - b
        assert nO >= 1
        w = mass / (nB * nS * nO)
        for Bset in combinations(U, b):
            Bset = list(Bset)
            Urest = [u for u in U if u not in Bset]
            for u0 in Urest:
                for Shat in combinations(D, b):
                    Shat = list(Shat)
                    comp = [d for d in D if d not in Shat]
                    bal = perm_from_order([rest, [u for u in Urest if u != u0],
                                           Shat, [u0], Bset, comp])
                    prof[bal] = prof.get(bal, F(0)) + w
    return prof
