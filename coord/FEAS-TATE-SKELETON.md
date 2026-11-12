# FEAS-TATE-SKELETON — Tate uniformization, p-adic theta, Berkovich skeleton measures vs q-pilot volume

Status: READ-ONLY feasibility, 2026-11-12. No compile.
Target: V + gap >= (sF - 1) * A, M = A - R >= 0,
A = qPilot.absLogQ, V = theta-hull log-volume, gap = rhs + sF A - V.
Judgments: A = direct instance of an already-proved theorem; B = conditional
with a new Berkovich/skeleton model; C = only analogy/restatement.

VERDICT: A-full = NO. A-local = possible only for the q-pilot local skeleton
factor under an exact measure/region identification. B = full target only after
a large new model. C = current unconditional status.

## 1. Tate uniformization and p-adic theta (standard theory)

Let K be a nonarchimedean field, q in K^*, |q| < 1. Tate's uniformization:
  E_q(Kbar) = Kbar^* / q^Z,
with Tate parameter q, and the rigid-analytic quotient map
  u in Kbar^* |-> (X(u), Y(u)) in E_q(Kbar),
  X(u) = sum_{n in Z} q^n u / (1 - q^n u)^2 - 2 sum_{n>=1} n q^n/(1-q^n),
  Y(u) = sum_{n in Z} q^n u^2/(1-q^n u)^3 + ... .
The Tate theta function
  theta_q(u) = sum_{n in Z} q^{n(n-1)/2} u^n
is convergent for |q|<1; its zeros are u in q^Z, and it satisfies the
quasi-periodicity theta_q(q u) = -u^{-1} theta_q(u) (up to the standard
normalization). Equivalently, the product form
  theta_q(u) = prod_{n>=0} (1 - q^n u) prod_{n>=1} (1 - q^n/u) (1 - q^n)
is the standard p-adic theta function. The Tate parameter q is recovered from
the theta divisor; log|q| is the period/length of the skeleton.

Relevance: at a bad place, our q-pilot parameter is exactly a Tate parameter
q_v, and gaussExponent j encodes q_v^{j^2} (the theta-value scaling
qroot^{j^2}). The classical theta formula makes the j^2 exponents explicit.

## 2. Berkovich skeleton and Chambert-Loir measure (standard theory)

For E_q over K, the Berkovich analytification E_q^an has a canonical skeleton
  Sigma_q = R / v(q) Z  (a circle of length -v(q) = -log|q|, up to normalization),
and a continuous retraction tau : E_q^an -> Sigma_q. For a divisor D on E_q and
a continuous metric on O(D), the Chambert-Loir measure is
  mu_D = c_1(O(D), ||.||)
on E_q^an; it is supported on the skeleton when the metric is invariant under
the torus action. On the circle Sigma_q, with a coordinate t:
- a continuous piecewise affine potential phi has
    mu = dd^c phi = (Lebesgue part from the slope) + atomic masses at kinks;
- the total mass is deg(D), and for a principal divisor/Green function the
  measure is normalized accordingly;
- the theta/Green function g_q(x,y) = -log|theta_q(u_x/u_y)| (with the standard
  q-normalization) is piecewise affine on the skeleton away from the diagonal;
  its dd^c gives the Chambert-Loir measure of [x]-[y].
This is the explicit skeleton integration theory (Chambert-Loir; Berkovich;
Gubler; tropical skeleton literature).

## 3. Mapping to our q-pilot/theta-hull volumes

Local q-pilot factor:
- at a bad place v with Tate parameter q_v, the skeleton length is
  -log|q_v| = qOrder_v/(2l) (in the paper normalization, up to the usual
  factors). This is exactly the q-pilot absolute log magnitude A_v, up to the
  normalization by 2l.
- theta scaling q_v^{j^2} retracts to the point j^2 * (period) on Sigma_q;
  summing over j gives sum_j j^2 = nC * sF entries. Thus the q-side weighted
  coefficient sF * A may be expressible as an integral/sum over the skeleton of
  the theta divisor or of the piecewise linear theta potential. This is the
  strongest positive point of the analogy.
Theta-hull factor:
- the holomorphic theta hull is a product of log-shell/annulus regions; its
  retraction to the product of skeletons is a polytope/box. Haar log-volume of
  the hull can be written as an integral of a piecewise affine function over
  the skeleton product (Chambert-Loir measures of the boundary divisors), at
  least locally.
- The gap/rhs comparison would then become a comparison of two explicit
  skeleton integrals plus the archimedean term. This is a genuine B route, not
  a direct theorem.

Global issue:
- our determinant/theta-hull object is a product over places and tensor
  factors with weights and an archimedean correction; the skeleton measure is
  local at one nonarchimedean place. A global formula requires a product of
  local skeleton integrals and an archimedean normalization, which is exactly
  the missing global assembly.

## 4. A/B/C verdict

A-full (direct instance of a proved theorem): NO.
  There is no theorem in the current tree identifying the actual C3 theta-hull
  region with a Berkovich skeleton region or the Haar log-volume with a
  Chambert-Loir measure. The full target includes detBundle/arch/gap/global
  weights, which are outside the local Tate skeleton model.

A-local: POSSIBLE (conditional but genuinely explicit).
  If one constructs, at each bad place, the Tate curve E_{q_v}, the skeleton
  Sigma_q, and proves:
    (i) the q-pilot local region is the retraction of a skeleton interval/circle,
    (ii) the local Haar log-volume equals the Chambert-Loir/theta integral,
    (iii) the theta exponents are j^2,
  then the local q-side coefficient sF * A_v becomes an explicit skeleton
  integral. This is an A-type instance for the local factor only, using
  standard Tate/Chambert-Loir formulas. It does not by itself prove M >= 0.

B (full target): YES, only after:
  1. a Berkovich/rigid model of the local theta hull at every relevant place;
  2. a proof that the actual Haar log-volume equals the skeleton integral
     (measure compatibility), including the normalization of q;
  3. a global product formula and the archimedean term identification;
  4. a comparison of the resulting explicit integrals with the q-pilot term.
  This is a large new program; no such model exists in the tree.

C (current unconditional route): YES. Without the model, the skeleton picture
  is an analogy. It cannot prove the target and does not supply the missing
  qPilotHaarRegion/theta subset/arch assembly.

## 5. Required new definitions for even the local A route

- Tate curve E_q over a nonarchimedean field, with q parameter and |q|<1.
- p-adic theta function theta_q and its divisor/quasi-periodicity.
- Berkovich analytification E_q^an, skeleton Sigma_q, retraction tau.
- Chambert-Loir measure c_1(O(D), ||.||) on E_q^an and its restriction to
  Sigma_q; piecewise affine potential/dd^c formula.
- Identification of the actual local q-pilot region with a skeleton region.
- Haar-to-skeleton measure compatibility and normalization of q.
- Product/global assembly and archimedean comparison.
None of these are currently in our Lean tree; they would be substantial ports
from Berkovich/Arakelov literature, not a one-line instantiation.

## 6. Conclusion

The Tate/theta/Berkovich skeleton route is the most promising external route for
the LOCAL q-pilot factor: it can turn sF * A_v into an explicit skeleton
integral via theta exponents j^2 and Chambert-Loir measure. It is NOT a direct
proof of the global target; it is B for the full target, A-local only after a
new model. Current status is C. Our target remains the weaker variant
V + gap - (sF-1)A >= 0, not lana SSIneq.

No Lean file written; no compile claimed.
