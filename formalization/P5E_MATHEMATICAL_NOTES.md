# Actual central rates and entry into the certificate layer

This note separates proved analytic limits from numerical and height
obligations still needed for the complete irrationality-exponent theorem.

## A quantitative Riemann estimate

For continuous f with |f(x)-f(y)|<=K|x-y|, K>=0, grid step delta>=0,
and integers l<=u, GridIntegralBound proves

    |delta*sum_(r in Ico(l,u)) f(r*delta+s)
       - integral_(l*delta+s)^(u*delta+s) f(x) dx|
      <= K*delta^2*(u-l).

On each cell, write the discrepancy as the integral of f(left)-f(x).
Its integrand is at most K*delta in norm; the cell has length delta.
Add the finitely many integrals using adjacent-interval additivity and
the finite-sum triangle inequality. No qualitative Riemann integrability
interface, sample convergence claim or unproved interchange of limits occurs.

For positive integers L and fixed a<=b, use delta=1/(L*N),
l=a*N and u=b*N. The error is K*(b-a)/(L^2*N), which tends to zero.
The Icc sum has one additional endpoint f(b/L+s)/(L*N), also tending to
zero. This explicitly includes zero-width intervals in the grid theorem.

## The actual logarithmic integrand

For fixed Y>0 put f_Y(u)=log(sqrt(u^2+Y^2)). Its derivative is
u/(u^2+Y^2). The elementary inequality

    Y*|u| <= u^2+Y^2

gives |f_Y'(u)|<=1/Y. The real mean value theorem proves the global
Lipschitz inequality with K=1/Y. Thus the preceding mesh bound applies
to the entire actual scaled interval, including its center and endpoints.

## Factorial logarithms

The needed Stirling input is only that

    a_n = n! / (sqrt(2*n)*(n/exp(1))^n)

has a finite positive limit. Its exact value sqrt(pi) is unnecessary.
The current pinned Mathlib source proves this in Stirling Part 1.
StirlingLogCore preserves that proof subset and its copyright header;
the missing Wallis import is replaced by its already cached Integrals.Basic
import. No original dependency source, toolchain, manifest or cache is edited.
The copied declarations are relocated into OddPiPowers.StirlingLogCore,
avoiding collisions with the full Mathlib Stirling namespace.
The source and adapted SHA-256 hashes, Apache-2.0 provenance and a deterministic
reproducer are recorded with the acceptance evidence.

Taking logarithms yields

    (log(n!)-n*log n)/n
      = log(a_n)/n + log(2*n)/(2*n) - 1 -> -1.

For fixed positive integers L,k, composition along k*N and elementary
logarithm identities then give

    (log((k*N)!)-k*N*log(L*N))/(L*N)
      -> (k/L)*log(k/L)-k/L.

All statements use totalized expressions at N=0. Their eventual identities
are proved only after N>0 is available, so no illegal cancellation occurs.

## One interval and a finite actual family

Let 2*a<L and c=(L-2*a)/L. The actual interval is
Icc(a*N,(L-a)*N), of integer length (L-2*a)*N. Combining the factorial
limit, the Icc Riemann limit and the extra log(L*N)/(L*N) term proves

    (log(((L-2*a)*N)!)-((L-2*a)*N+1)*log(L*N)
       -sum_r f_Y(r/(L*N)-1/2))/(L*N) -> -F_c(Y),

with F_c exactly the accepted P5-D closed formula. In particular, the extra
endpoint logarithm is retained at finite scale and then proved negligible.

The actual construction's center logarithm is proved to be the finite sum
of these expressions. Consequently any actual family with n=L*N and
left_a=A_a*N, 2*A_a<L, satisfies

    centralLogRatio(Y)/(L*N) -> -sum_a F_(c_a)(Y).

No limiting formula is supplied as an input hypothesis.

## From the exact finite bound to all rows

For S=(M-1)!*lcm(1,...,n)^(M-1), the accepted log-lcm limit proves
log S/n -> M-1. The new center limit and P5-D's exact positive central
majorant then prove

    log(centralRemainderBound(m,h,theta,Y))/n
      -> M-1+|theta|*Y-sum_a F_(c_a)(Y).

The log of the fixed majorant constant and the fixed powers of n have
normalized limits zero. With m=M-1 and the actual degree condition, the
same scalar majorizes every actual row simultaneously. Thus, for every
eta>0, eventually all rows satisfy

    |sum_j A_hj(i)*lambda^j| <= exp((-D0(Y)+eta)*n),
    D0(Y)=sum_a F_(c_a)(Y)-(pi/2)*Y-(M-1).

The concrete seventeen-row family n=69*N is instantiated. Its actual
Gaussian quotient U_h is divided by the positive actual divisor D_n.
Every certified lower divisor rate gamma gives the uniform exponent

    |U_h(lambda)| <= exp((-(D0(Y)+gamma)+eta)*n).

There is an unconditional instance gamma=2/69 from P4. This is only the
weak calibration rate; it is not the sharp twelve-layer arithmetic rate
needed to recover the planned numerical targets. A generic divisor-rate
interface permits replacement by sharper accepted finite-window results.
All these theorems hold at every fixed Y>1/2. Optimal-height existence or
uniqueness is not needed to choose a fixed rational Y in later certificates.

## P6-A: soundness of one-sided rational certificates

If d<=D, 0<=G<=g and d-(k-1)g>0, the actual denominator is positive and

    m(D+G)/(D-(k-1)G) <= m(d+g)/(d-(k-1)g).

The cross-product difference equals

    m*k*(D*g-d*G) >= 0

for k>=1. The formal lemma uses the nonnegative factor ((k-1)+1), so it
also handles k=0 without assuming the natural subtraction identity there.
For rational d,g,target, checking

    m(d+g) < target*(d-(k-1)g)

therefore proves the actual exponent expression is strictly below target.
RationalRateCertificate connects this comparison to P1 and returns an
ExponentUpperBound B with B<target, retaining the full AuxiliaryFamily
as an explicit hypothesis. This is certificate soundness infrastructure;
it does not provide a concrete AuxiliaryFamily or assert a numerical pi^3 bound.

## Remaining route

The central asymptotic-rate obligation is closed by P5-E. The outstanding
analytic bottleneck is the uniform coefficient height, including evaluation
and divided differences on the whole disk. P5_HEIGHT_PROOF_PLAN.md lists
the exact existing local-factor APIs and a safe polynomial-loss bound.
Then assemble the actual Gaussian polynomial family, improve gamma as
required, and produce kernel-checked pi/log/atan rational certificates.
P6-A has begun the numeric certificate layer; full P6 and P7 remain open.

The manuscript's pi^3 twelve-layer target uses s=11, hence M=187 and
m=186, with multiplicities (66,11,...,11). It is not the seventeen-row
s=1 calibration family. Applying the generic central-rate theorem there
requires an explicit scaled actual family and arithmetic grouping. Those
constructors and the uniform height are the next concrete assembly tasks;
the s=1 instantiation must not be advertised as the full pi^3 target.

A faster route to the first completely closed instance is the balanced
family: all intervals are [0,n], and use the unreduced coefficients.
Its constructor has constant left endpoint zero, needs no carry grouping
or improved gamma, and every local interval factor at ell<=n is a pole
factor. Thus a balanced-only height proof avoids the regular-factor bound.
The newly proved generic central rate already applies with L=1 and A=0.
After that first coarse instance, extend the height proof to regular factors
and assemble s=11 for the intended improved target. No new numeric bound is
asserted by this suggested proof order.
