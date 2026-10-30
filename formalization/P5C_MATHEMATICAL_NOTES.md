# From finite pole circles to the full horizontal contour

The compilation and acceptance record is separate: see P5C_REVIEW_2026-10-29.md
and the final machine-readable verification record. This note explains the
mathematical bridge and the order of limits.

## The actual kernel and the required comparison

Keep the accepted actual intervals, denominator Q, interval-factorial product
F, common scale S and exponential E_lambda(z)=exp(lambda*(z+n)). Write

    K_h(lambda,z) = F*z^h*E_lambda(z)/Q(z).

P5-B already identifies the actual auxiliary row with

    S/(2*pi*i) * sum_{r=0}^n integral_C(-r,1/4) K_h(lambda,z) dz.

The missing equality was between this finite sum of genuine circle integrals
and the boundary of a rectangle containing all poles. Vertical-side decay and
horizontal integrability by themselves do not establish that equality.

For real a<b and c<d, P5-C uses positive boundary orientation

    Rect(f) = integral_a^b f(x+ic) dx - integral_a^b f(x+id) dx
              + i*integral_c^d f(b+iy) dy - i*integral_c^d f(a+iy) dy.

The sign is lower minus upper, with right upward and left downward.

## Simple poles: the logarithm jump is proved explicitly

Take a real pole p strictly inside the rectangle: a<p<b and c<0<d.
The primitive log(z-p) is differentiable on both horizontal lines and the
right vertical line. On the left vertical line use log(-(z-p)) instead;
its argument has positive real part, so it avoids the logarithm cut.
Both primitives have derivative 1/(z-p) on their respective sides.

The fundamental theorem of calculus converts each side integral to endpoint
differences. At the left upper endpoint u=a+id-p, Im(u)>0 and

    log(-u) = log(u)-pi*i.

At the left lower endpoint v=a+ic-p, Im(v)<0 and

    log(-v) = log(v)+pi*i.

These follow from the pinned library's argument formulas and the definition
of complex log. All other endpoint terms telescope. Thus

    Rect(1/(z-p)) = 2*pi*i.

This computes the exact orientation and normalization, rather than assuming
a winding number or a rectangular residue theorem.

## Higher powers and an entire divided-difference induction

For j>=0, the function

    -(z-p)^(-(j+1))/(j+1)

has derivative (z-p)^(-(j+2)) away from p. Although the primitive has a pole
inside the rectangle, it is differentiable along every boundary side. The
real-parameter chain rule and fundamental theorem of calculus therefore make
the rectangular integral of each higher inverse power zero. The corresponding
circle integral is also zero by the proved integral formula for integer powers.

For an entire function f, the divided difference

    g(z) = (f(z)-f(p))/(z-p), with g(p)=f'(p),

is entire. The library establishes this using its proved removable-singularity
theorem. At every nonpole,

    f(z)/(z-p)^(j+1) = g(z)/(z-p)^j + f(p)/(z-p)^(j+1).

This is an exact identity. On both the rectangle and the centered circle,
integrability and finite linearity are proved before splitting the integral.
For j=0, the g term is holomorphic and has zero integral; the remaining simple
pole has the same 2*pi*i integral on both contours. For j+1, the last term is
a higher inverse power and has zero integral; apply induction to g.
Consequently, for every entire f and every pole order j+1,

    Rect(f(z)/(z-p)^(j+1))
      = integral_C(p,1/4) f(z)/(z-p)^(j+1) dz.

This general comparison is proved without postulating any residue theorem.
The circle need not fit inside the rectangle: the numerator is entire, and
the argument compares the two integrals directly. The actual pole circles
remain mutually disjoint by the accepted integer-pole geometry.

## Application to the actual finite principal parts

The accepted polynomial numerator identity supplies the actual partial
fractions of F*z^h/Q(z). Multiplication by E_lambda gives finitely many terms
with entire numerator and poles at -r. For q<mu_r, the pole order is mu_r-q,
which is positive. The generic comparison therefore applies to every term.

If a<-n, b>0, c<0 and d>0, every actual pole is strictly inside. All boundary
pole factors are nonzero. Finite sum interchange and the already accepted
individual pole-circle formulas give

    Rect(K_h(lambda,...)) = finitePoleContour_h(lambda).

The full factorial product and S are tracked in the same places as in P5-B.
No new scale, surrogate polynomial, or unproved contour assumption is introduced.

## Fix scale, then send the real truncation to infinity

Now lambda=i*theta, theta real; n>0 and Y>1/2 are fixed. Put H=nY and choose
a=-R,b=R,c=-H,d=H. Every R>n satisfies the finite comparison. Hence the
rectangular integral is eventually constant, equal to the fixed finite contour.

P5-B proves that both full-kernel vertical-side integrals tend to zero as
R tends to infinity, with n,H,theta,h fixed. It also proves integrability on
both full horizontal lines under the explicit degree condition

    h<=m, degree Q>=2(m+2).

For an integrable function, the symmetric truncations from -R to R tend to
the whole-line Bochner integral. Combining the four limits, and using uniqueness
of limits, identifies the finite contour with lower minus upper horizontal
integrals. This is a fixed-scale statement; no joint limit in n and R occurs.

## The Jacobian and the actual row at i

The accepted normalized horizontal parameter is

    z(t,+/-Y)=n*(t-1/2 +/- iY).

The real coordinate is x=n*(t-1/2), so t=x/n+1/2 and dx=n*dt. The affine
integrability transfer and whole-line change-of-variable formula are proved;
the resulting multiplier is n, not its reciprocal. Thus

    finitePoleContour_h(i*theta)
      = n*(integral_R K_h(i*theta,z(t,-Y)) dt
            - integral_R K_h(i*theta,z(t,Y)) dt).

At lambda=i*pi/2, exp(lambda)=i, giving the actual auxiliary row identity

    sum_j A_(h,j)(i)*lambda^j
      = S*n/(2*pi*i) *
          (integral_R K_h(lambda,z(t,-Y)) dt
             - integral_R K_h(lambda,z(t,Y)) dt).

The corresponding norm inequality follows by the triangle inequality. Together
with P5-B's full-line majorant it is the contour foundation for the subsequent
central exponential-rate estimate.

The actual seventeen-row family has n=69N and degree at least 69N+1, so every
positive N satisfies the stated degree threshold for all h<17. The final
representation is instantiated for every one of those rows.

## What remains outside P5-C

This closes the finite-to-infinite contour bridge. It does not evaluate the
growth of the central denominator or factorial product, prove the uniform
coefficient heights, optimize/sharpen arithmetic gamma, or instantiate the
final irrationality-measure transfer for odd powers. Those require additional
analytic rates, arithmetic certificates and parameter comparisons.
