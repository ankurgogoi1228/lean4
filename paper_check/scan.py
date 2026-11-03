"""Brute-force exact determination of the qualified-majority frontier by linear
programming over all profile types, compared with the closed formulas of the paper."""
from fractions import Fraction as F
from lp import lp_value, qstar, Mfun, s_, r_


def threshold(K, k, ell, iters=26, lo=F(1, 2), hi=F(1)):
    """sup{q : LP value > 0}, by exact bisection.  Returns (lo, hi) bracketing."""
    v_lo = lp_value(K, k, ell, lo)[0]
    v_hi = lp_value(K, k, ell, hi)[0]
    if v_lo is None or v_lo <= 0:
        return ('<= 1/2', None, None)
    if v_hi is not None and v_hi > 0:
        return ('> 1', lo, hi)
    for _ in range(iters):
        mid = (lo + hi) / 2
        v = lp_value(K, k, ell, mid)[0]
        if v is not None and v > 0:
            lo = mid
        else:
            hi = mid
    return ('ok', lo, hi)


def main():
    for K in range(3, 7):
        r = K // 2
        print(f'================ K = {K}  (r = {r}, eps = {K % 2}) ================')
        for k in range(1, K):
            for ell in range(1, k + 1):
                # paper's claim only covers k <= ceil(K/2)
                claim = qstar(K, k, ell) if k <= r + (K % 2) else None
                st, lo, hi = threshold(K, k, ell)
                if st == '<= 1/2':
                    print(f'  k={k:2d} ell={ell:2d}   threshold <= 1/2       claim={claim}')
                    continue
                if st == '> 1':
                    print(f'  k={k:2d} ell={ell:2d}   threshold >  1         claim={claim}')
                    continue
                info = ''
                if claim is not None:
                    ok = (lo <= claim <= hi) or (abs(float(lo) - float(claim)) < 1e-7)
                    info = f'  claim={claim}  {"MATCH" if ok else "*** MISMATCH ***"}'
                print(f'  k={k:2d} ell={ell:2d}   threshold in [{float(lo):.9f},{float(hi):.9f}]'
                      f'  (lo={lo}, hi={hi}){info}')


if __name__ == '__main__':
    main()
