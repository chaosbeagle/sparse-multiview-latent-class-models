#!/usr/bin/env python3
"""Exact arithmetic for separation certificates and statistical examples.

Run: python3 -I verify_examples.py
Only Python standard-library arithmetic is used. Rational assertions certify
finite calculations; displayed decimals are rounded illustrations. The volume
argument and statistical implications are proved in the manuscript. This script
does not compile Lean, search for an interval cover, or implement an estimator.
"""
if not __debug__:
    raise SystemExit("Run without -O or -OO: the mathematical checks require assertions.")

from fractions import Fraction as F
from math import isqrt
from itertools import product
from decimal import Decimal, localcontext


def sqrt_bracket(x, places=40):
    x = F(x)
    scale = 10**places
    n = isqrt((x.numerator * scale**2) // x.denominator)
    lo, hi = F(n, scale), F(n+1, scale)
    assert lo*lo <= x < hi*hi
    return lo, hi


def arctan_partial(x, n):
    return sum(((-1)**k * x**(2*k+1) / (2*k+1) for k in range(n)), F(0))


# Machin's identity pi = 16 atan(1/5) - 4 atan(1/239), with alternating-series bounds.
pi_lo = 16*arctan_partial(F(1,5), 40) - 4*arctan_partial(F(1,239), 11)
pi_hi = 16*arctan_partial(F(1,5), 41) - 4*arctan_partial(F(1,239), 10)
sqrt2_lo, sqrt2_hi = sqrt_bracket(2)
sqrt56_lo, _ = sqrt_bracket(56)


def dec(x, digits=15):
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def leaf_lower(w, sigma_hi):
    # All positive. B decreases with sigma, so sigma_hi gives a lower B.
    a_lo = (1+sqrt2_lo)/(w*sigma_hi**2)
    b_lo = 1/sigma_hi**3 + 3*a_lo/sigma_hi
    B_lo, _ = sqrt_bracket(b_lo*b_lo + 3*a_lo*a_lo)
    V_lo = (1-2*w)*(pi_lo*(1-sigma_hi)**2/4)**3
    # rho = 1/(12 sqrt(8) B), so sqrt(7)/(2 rho) = 6 sqrt(56) B.
    lower = V_lo*(6*sqrt56_lo*B_lo)**7
    return V_lo, lower


rows = [(F(1,10),F(1,10)), (F(1,5),F(1,5)), (F(3,10),F(3,10)),
        (F(2,5),F(1,2)), (F(9,20),F(7,10)), (F(49,100),F(9,10))]
print('Certificate size: rational lower enclosures (decimal displays rounded):')
for w,s in rows:
    v,n = leaf_lower(w,s)
    print(f'w={w}, sigma={s}: volume lower enclosure ~ {dec(v)}, leaf lower enclosure ~ {dec(n)}')
sig_lo, sig_hi = sqrt_bracket(F(1,2))
v,n = leaf_lower(F(1,4),sig_hi)
assert n > 29369 * 10**17   # 2.9369e21, conservative exact assertion.
print('margins (1/4, 1/sqrt(2)):', dec(v), dec(n), '; verified leaves > 2.9369e21')


def kernel(a,b):
    return ((a,b),(1-a,1-b))


def gram_minus_margin(L, sigma):
    return tuple(tuple(sum(L[y][i]*L[y][j] for y in range(2))
                       - (sigma*sigma if i==j else 0)
                       for j in range(2)) for i in range(2))


def check_K(w,Ls):
    assert sum(w)==1 and min(w)>=F(1,5)
    for L in Ls:
        assert all(x>=0 for row in L for x in row)
        assert all(sum(L[y][z] for y in range(2))==1 for z in range(2))
        G = gram_minus_margin(L,F(1,5))
        assert G[0][0]>0 and G[1][1]>0
        assert G[0][0]*G[1][1]-G[0][1]*G[1][0]>0


def squared_distance(w,Ls,w1,Ls1,swap=False):
    p=lambda z:1-z if swap else z
    return sum((w[z]-w1[p(z)])**2 for z in range(2)) + sum(
        (Ls[g][y][z]-Ls1[g][y][p(z)])**2
        for g in range(3) for y in range(2) for z in range(2))


def observations(w,Ls):
    def cell(ys):
        return sum(w[z]*Ls[0][ys[0]][z]*Ls[1][ys[1]][z]*Ls[2][ys[2]][z]
                   for z in range(2))
    return [cell(ys) for ys in product(range(2),repeat=3)]


t=F(1,250000)
w=(F(1,2),F(1,2)); Ls=(kernel(F(5,8),F(3,8)),)*3
w1=(F(1,2)+t,F(1,2)-t)
Ls1=(kernel(F(5,8)-t/4,F(3,8)-t/4),)*3
check_K(w,Ls); check_K(w1,Ls1)
d0=squared_distance(w,Ls,w1,Ls1)
d1=squared_distance(w,Ls,w1,Ls1,True)
assert d0==F(11,4)*t*t and d1==F(3,4)+d0
# Exact rho^2 = 1/[1152 (11171875 + 7593750 sqrt(2))].
# sqrt(2)>7/5 gives a rational upper bound on rho^2.
assert F(7,5)**2 < 2
rho2_upper=1/(1152*(F(11171875)+F(7593750)*F(7,5)))
assert d0>rho2_upper and d1>rho2_upper
O=observations(w,Ls); O1=observations(w1,Ls1)
H=sum((x-y)**2 for x,y in zip(O,O1))
assert H==t*t/2048+5*t**4/256+t**6/128
assert H < F(9,10**8)**2
assert F(9,10**8) < F(1,2**23)
N_dyadic=20480*2**48
assert N_dyadic==5764607523034234880
print('\nExact rational far-pair checks: all passed')
print('direct distance squared =',d0,'=',dec(d0))
print('swap distance squared =',d1)
print('H =',H,'=',dec(H))
print('observation gap < 9e-8; sample-count lower expression (rounded) =',dec(F(20480,1)/F(9,10**8)**2))
print('dyadic-returned-Delta prescribed per-edge count >=',N_dyadic)

# Boundary control ceiling certified without floating point.
Nlo=F(40960,7)*(157+108*sqrt2_lo)
Nhi=F(40960,7)*(157+108*sqrt2_hi)
assert 1812392<Nlo<=Nhi<1812393
print('\nBoundary prescribed count = 1812393, certified by rational sqrt(2) brackets.')

# Distinct complementary-pair orbit supports are disjoint and at d_W=2.
bits=list(product(range(2),repeat=3))
supports={tuple(sorted((b,tuple(1-x for x in b)))) for b in bits}
assert len(supports)==4
support_sets=[set(x) for x in supports]
for i,S in enumerate(support_sets):
    for T in support_sets[i+1:]:
        assert S.isdisjoint(T)
        b=next(iter(S)); c=next(iter(T)); h=sum(x!=y for x,y in zip(b,c))
        assert min(4*h,4*(3-h))==4
print('Boundary: 8 parameters; 4 orbits; pairwise-disjoint observation supports; distinct orbit distance 2.')

print("All exact arithmetic checks passed.")
