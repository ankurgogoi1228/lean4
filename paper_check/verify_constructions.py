"""Verify every explicit profile constructed in the paper (exact arithmetic)."""
from fractions import Fraction as F
from itertools import combinations
from math import comb, gcd
from construct import (counts, check, thm2_profile, thm3_profile,
                       thm3_boundary_state, merge, scale_int, perm_from_order)


def qstar(K, k):
    r, eps = K // 2, K % 2
    s = r - k + 1 + eps
    return 1 - F(s, 2 * (K - k))


def s_(K, k):
    return K // 2 - k + 1 + (K % 2)


def Mfun(K, k, ell):
    r, eps, s = K // 2, K % 2, s_(K, k)
    if not (eps == 1 and s == 1):
        m = ell // 2
        return F(m * (s - 1 + m)) if ell % 2 == 0 else F(m * (m + s)) + F(s, 2)
    m = ell // 2
    return F(m * m) if ell % 2 == 0 else F(m * (m + 1))


def qstar_l(K, k, ell):
    return 1 - Mfun(K, k, ell) / (ell * (K - k))


# ------------------------------------------------------------------ tests
def test_thm2(K, k, quiet=False):
    q0 = qstar(K, k)
    if q0 <= F(1, 2):
        if not quiet:
            print(f'   K={K} k={k}: q*={q0} -> sharpness statement is vacuous')
        return True
    best = None
    for drop in [F(1, 100), F(1, 1000), F(1, 10000)]:
        q = q0 - drop
        if q < F(1, 2):
            continue
        for L in range(2, 400):
            for M in range(L // 2 + 1, L):
                prof = scale_int(thm2_profile(K, k, F(M, L)))
                n, nab, A, B, O = counts(prof, K, list(range(k)))
                if not all(v > q * n for v in nab.values()):
                    continue
                if B[0] > A[0]:
                    best = (q, F(M, L), n, A[0], B[0])
                    break
            if best:
                break
        if best:
            break
    if best and not quiet:
        q, rho, n, A0, B0 = best
        print(f'   K={K} k={k}: q={q} (< q*={q0}), rho={rho}, n={n}, '
              f'A(a1)={A0} B(a1)={B0}  -> strict q-Condorcet, a1 unacceptable  OK')
    elif not best:
        print(f'   *** K={K} k={k}: Theorem 2 construction NOT found ***')
    return best is not None


def test_thm3(K, k, ell, quiet=False):
    q0 = qstar_l(K, k, ell)
    if q0 <= F(1, 2):
        if not quiet:
            print(f'   K={K} k={k} ell={ell}: q*={q0} -> sharpness statement is vacuous')
        return True
    r, eps = K // 2, K % 2
    s, t = s_(K, k), K - k
    best = None
    for drop in [F(1, 100), F(1, 1000), F(1, 10000)]:
        q = q0 - drop
        if q < F(1, 2):
            continue
        if not (eps == 1 and s == 1):
            m = ell // 2
            for den in range(2, 400):
                for num in range(1, den):
                    d = F(num, den)
                    lam = (1 - d, d) if ell % 2 == 0 else (F(1, 2) - d, F(1, 2) + d)
                    if min(lam) <= 0:
                        continue
                    prof = scale_int(thm3_profile(K, k, ell, lam))
                    n, nab, A, B, O = counts(prof, K, list(range(k)))
                    if not all(v > q * n for v in nab.values()):
                        continue
                    if all(B[a] > A[a] for a in range(ell)):
                        best = (q, lam, n)
                        break
                if best:
                    break
        else:
            m = ell // 2
            for den in range(2, 400):
                for num in range(1, den):
                    d = F(num, den)
                    parts = [(('A', m), 1 - d), (('B', m), d)] if ell % 2 == 0 \
                        else [(('B', m), 1 - d), (('A', m + 1), d)]
                    if min(w for _, w in parts) <= 0:
                        continue
                    if any(kind == 'A' and b == 0 and len(range(k)) - ell < 1
                           for (kind, b), w in parts):
                        continue
                    prof = {}
                    for (kind, b), w in parts:
                        prof = merge(prof, thm3_boundary_state(K, k, ell, (kind, b), w))
                    prof = scale_int(prof)
                    n, nab, A, B, O = counts(prof, K, list(range(k)))
                    if not all(v > q * n for v in nab.values()):
                        continue
                    if all(B[a] > A[a] for a in range(ell)):
                        best = (q, d, n)
                        break
                if best:
                    break
        if best:
            break
    if best and not quiet:
        print(f'   K={K} k={k} ell={ell}: q={best[0]} (< q*={q0}), '
              f'param={best[1]}, n={best[2]}  -> OK')
    elif not best:
        print(f'   *** K={K} k={k} ell={ell}: Theorem 3 construction NOT found ***')
    return best is not None


# ------------------------------------------------------------------ examples
def example2():
    print('\nExample 2 (K=5,k=3,n=26,q=24/25):')
    prof = {(1, 2, 3, 0, 4): 1, (1, 2, 0, 3, 4): 25}
    ok, unacc, data = check(prof, 5, 3, F(24, 25), 'strict', label='Example 2')
    print(f'     q=24/25 > q1=23/24 : {F(24,25) > F(23,24)}')
    print(f'     q1 fails as a guarantee of full acceptability: {unacc == [0]}')
    return ok and unacc == [0]


def example1():
    print('\nExample 1 (K=5,k=3):')
    print('     ' + '  '.join(f'q_{e}^*={qstar_l(5,3,e)}' for e in (1, 2, 3)))
    q0 = F(3 * 5 - 2 * 3 - 2, 4 * (5 - 3))
    q1 = q0 / 3 + F(2, 3)
    print(f'     q0={q0} (7/8: {q0 == F(7,8)}), q1={q1} (23/24: {q1 == F(23,24)})')


def diss_mahajne_example():
    print('\nSection 7.2 quoted K=4,k=2 profile (n = 12m+1) from Diss-Mahajne:')
    for m in (1, 2.5):
        pass
    for m in (1, 2, 3, 10):
        prof = {(0, 3, 1, 2): 3 * m, (0, 2, 1, 3): 3 * m,
                (1, 2, 0, 3): 3 * m, (1, 3, 0, 2): 3 * m,
                (2, 3, 0, 1): 1}
        C = [0, 1]
        n, nab, A, B, O = counts(prof, 4, C)
        qn = F(3, 4) * n
        print(f'  m={m:2d}: n={n}  margins={ {k_: int(v) for k_, v in nab.items()} }'
              f'  weak 3/4-Condorcet={all(v >= qn for v in nab.values())}'
              f'  (need >= {float(qn):.3f})')
        print(f'         A={ {a:int(v) for a,v in A.items()} }'
              f' B={ {a:int(v) for a,v in B.items()} }'
              f'  completely unacceptable={all(B[a] > A[a] for a in C)}'
              f'   profile is q-Condorcet only for q <= {F(min(nab.values()), n)}')


def theorem4a_sharpness():
    print('\nTheorem 4(a) sharpness (K=5,k=3,r=2, n=3):')
    for q, nn in ((F(99, 100), 101), (F(999, 1000), 1001), (F(1), 3)):
        prof = {(1, 2, 3, 0, 4): 1, (1, 2, 0, 3, 4): nn - 1}
        ok, unacc, data = check(prof, 5, 3, q, 'strict' if q < 1 else 'weak',
                                verbose=False)
        print(f'     q={q}: strict q-Condorcet={ok}, unacceptable={unacc},'
              f' A={ {a:int(v) for a,v in data[2].items()} }'
              f' B={ {a:int(v) for a,v in data[3].items()} }'
              f' O={ {a:int(v) for a,v in data[4].items()} }')


def theorem4b():
    print('\nTheorem 4(b) profiles (top-k block, a1 first below the line):')
    prof = {(1, 2, 3, 0, 4): 3}          # K=5,k=4,r=2,eps=1,m=1
    ok, unacc, _ = check(prof, 5, 4, F(1), 'weak', verbose=False)
    print(f'     K=5 k=4: weak 1-Condorcet={ok}, unacceptable={unacc}')
    prof = {(1, 2, 3, 0, 4, 5): 3}       # K=6,k=4,r=3,eps=0,m=1
    ok, unacc, _ = check(prof, 6, 4, F(1), 'weak', verbose=False)
    print(f'     K=6 k=4: weak 1-Condorcet={ok}, unacceptable={unacc}')


if __name__ == '__main__':
    print('==== Theorem 2 (sharpness, ell = 1) ====')
    a = all(test_thm2(K, k) for K in range(4, 10) for k in range(1, K // 2 + 1)
            if qstar(K, k) > F(1, 2))
    print('Theorem 2 constructions all verified:', a)

    print('\n==== Theorem 3(b) constructions ====')
    b = True
    for K in range(3, 9):
        r, eps = K // 2, K % 2
        for k in range(1, r + eps + 1):
            for ell in range(1, k + 1):
                b &= test_thm3(K, k, ell)
    print('Theorem 3 constructions all verified:', b)

    example1(); example2(); diss_mahajne_example(); theorem4a_sharpness(); theorem4b()
