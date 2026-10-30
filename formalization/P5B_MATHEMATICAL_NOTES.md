# Actual finite contours and fixed-scale vertical tails

This note describes the P5-B mathematics. Acceptance is determined separately
by P5B_REVIEW_2026-10-29.md and the executed build/audit evidence.

## Exact normalization and the algebra-to-integral bridge

For the actual intervals P, write

    F = product_a length_a!,
    S = (M-1)! * lcm(1,...,n)^(M-1),
    Q(z) = product_a product_{r in interval_a}(z+r),
    mu_l = number of intervals containing l,
    E_lambda(z) = exp(lambda*(z+n)).

P2 already proves a polynomial numerator identity whose right side is
F*X^h. P5-B evaluates it at a nonpole and divides by Q(z), obtaining the
actual partial fractions

    F*z^h/Q(z) = sum_l sum_{q<mu_l} a_(l,q)/(z+l)^(mu_l-q).

Here a_(l,q) is a coefficient of the existing localExpansion. That expansion
already includes F through its local interval factors. The derivative-order
coefficient c_(l,j)=a_(l,mu_l-1-j) is exactly localCoefficient; it is zero
when j>=mu_l. No extra interval factorial is inserted in c or in S.

The actual auxiliary polynomials were independently defined algebraically by

    A_(h,j)(x) = (S/j!) * sum_l c_(l,j)*x^(n-l).

Define their actual exponential remainder

    R_h(lambda) = sum_{j<M} A_(h,j)(exp(lambda))*lambda^j.

The finite expansion, natural-subtraction cast and interchange of these sums
are all proved. At a pole, E_lambda(-l)=exp(lambda*(n-l)). Thus

    R_h(lambda) = S * sum_l sum_{j<M} c_(l,j)*E_lambda(-l)*lambda^j/j!.

## A genuine finite contour

For every integer pole location l=0,...,n, take the positively oriented
circle centered at -l with radius 1/4. Distinct integer poles are separated
by distance at least 1. Each such circle encloses its own pole and no other
integer pole. Locations of multiplicity zero contribute zero and cause no
exception. Repeated intervals remain represented through mu_l.

Let

    K_h(lambda,z) = F*z^h*E_lambda(z)/Q(z).

On each circle the actual denominator is nonzero and K_h is circle
integrable. The evaluated partial fractions hold at every point of the
circle. Every principal summand is circle integrable, so finite sums can
be exchanged with the integral.

For a term with pole r different from the circle center -l, the denominator
is nonzero on the entire closed disk. Cauchy-Goursat makes its integral zero.
For the central term, the pinned Mathlib higher Cauchy formula gives

    integral_C(-l,1/4) E_lambda(z)/(z+l)^(j+1) dz
        = (2*pi*i/j!)*lambda^j*E_lambda(-l).

The derivative formula is proved from the entire exponential, rather than
introduced as an assumption. Reflecting q to j=mu_l-1-q and extending by
the proved zero coefficients to all j<M gives the exact theorem

    R_h(lambda) = S/(2*pi*i) * sum_{l=0}^n integral_C(-l,1/4) K_h(lambda,z) dz.

Equivalently the scalar outside the integral of z^h*E_lambda(z)/Q(z) is
C_n=S*F, as in the manuscript. The displayed contour is a finite sum of
genuine complex line integrals, not a renamed residue sum.

For the transfer theorem's lambda=i*pi/2, exp(lambda)=i is checked explicitly.
The left side therefore becomes the actual row sum

    sum_{j<M} A_(h,j)(i)*lambda^j.

Using exp(lambda*(z+n)) specifies the branch directly and avoids an unnecessary
general complex-logarithm construction. The chosen lambda is exactly the
branch value needed at i.

## Weighted horizontal integrability

For lambda=i*theta with theta real,

    |E_lambda(z)| = exp(-theta*Im(z)).

On z=n*(t-1/2 +/- iY), its norm is independent of t and bounded by
exp(|theta|*n*|Y|). Multiplying the accepted P5-A bound gives, for h<=m and
degree Q>=2(m+2),

    |K_h(lambda,z(t,Y))|
      <= |F|*exp(|theta|*n*|Y|)*n^h/|Q(z(0,Y))| * g_(m,Y)(t).

P5-A proves g_(m,Y) integrable on all of R. P5-B proves continuity/measurability
and domination for the weighted kernel itself, on both horizontal lines;
the full factorial kernel is then obtained by multiplication by F. These
are actual Bochner integrability statements, including both infinite tails.
The real-coordinate integral norm estimate is also proved. A later contour
parameterization must still include the Jacobian dz=n*dt.

## Explicit vertical-side bounds with n fixed

Fix n, H>=0, theta and h, and assume d=degree Q>=h+2. For

    R >= max(2,2*n,H), Re(z)=+R or -R, |Im(z)|<=H,

each actual pole factor has norm at least R/2. Therefore

    |Q(z)| >= (R/2)^d >= (R/2)^(h+2),
    |z| <= 2*R,
    |z^h/Q(z)| <= 2^h*2^(h+2)/R^2.

The exponential norm on the strip is at most exp(|theta|*H). Parameterize
each vertical side by z=x+i*y, y from -H to H, with derivative i. For the
kernel without F the actual integral is bounded by

    2*H*exp(|theta|*H)*2^h*2^(h+2)/R^2.

Multiplication by |F| gives the full-kernel estimate. The integrands are
continuous and interval integrable: real-part separation excludes every pole
on the whole vertical line. Since R^(-2) tends to zero, both left and right
vertical-side integrals tend to zero. The proofs quantify fixed P, H, theta,
h before R tends to infinity. Taking H=nY later is valid only with n fixed
during this limit; no joint limit is asserted.

## Instantiated base family and remaining contour gap

The actual 17-row family at n=69N has degree at least 69N+1. For every N>=1
this meets both the horizontal and vertical degree conditions for all h<17.
The finite contour identity, weighted horizontal integrability and both
vertical limits are instantiated for that family.

P5-B does not prove that the finite pole-circle contour equals the boundary
of a large rectangle. That comparison, followed by horizontal truncation
limits, is still needed to identify the remainder with two infinite horizontal
integrals. The new vanishing and integrability statements prepare that step;
they do not imply it without an explicit contour-deformation argument.
The remaining P5 work also includes coefficient heights and central
Stirling/Riemann rates. Sharp gamma and final pi-power numerical bounds
remain outside the present results.
