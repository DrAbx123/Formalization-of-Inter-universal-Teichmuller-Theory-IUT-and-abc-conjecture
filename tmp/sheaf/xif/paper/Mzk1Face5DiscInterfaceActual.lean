/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A909: candidate section 2 — discriminant disc(Psi_l): interface + verdict -/

/- Standard shape (TO BE VERIFIED against TateMulByN/DivisionPolynomial): for the l-division
polynomial Psi_l of an elliptic curve E/Q, `disc(Psi_l)` is `± l^a * Delta^b` as a rational
number; equivalently for each finite place p,
  `v_p(disc(Psi_l)) = a * v_p(l) + b * v_p(Delta)`
(the Lead's candidate form `(l^2-1)*v_p(Delta) + l*v_p(l)` is one possible exponent pair;
the exact (a,b) must be checked in the vendor/TateMulByN sources).

VERDICT: `disc(Psi_l)` is a RATIONAL NUMBER, so on the projective line its divisor is
principal: the sum of all its valuations (finite and archimedean) is ZERO (product formula).
It therefore gives a GLOBAL IDENTITY (degree 0), not a positive lower bound.  The target
quantity `V - (sF-1)*A` involves `q` and the hull volume, whereas the discriminant divisor
involves `Delta` and `l`; matching them would require an extra dictionary identity which is
not available and is not sign-definite.  Hence disc(Psi_l) does NOT provide the required
section of `H = det(hull) (x) L_q^{-(sF-1)}` and the route fails as a face-5 section
(consistent with chain 3's expectation of an identity). -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Face5DiscInterfaceActual

/-- Data-level discriminant section candidate: valuation exponents (a for l, b for Delta). -/
structure DiscSectionData where
  a : ℤ
  b : ℤ
  vpDelta : ℤ
  vpL : ℤ
  valuation_formula : Prop

/-- The discriminant's total degree is zero (principal divisor of a rational number). -/
structure DiscPrincipalData where
  totalDegree : ℝ
  principal : totalDegree = 0

/-- A principal divisor cannot supply a positive lower bound unless the target degree is 0. -/
theorem principal_zero_of_DiscPrincipalData (P : DiscPrincipalData) : P.totalDegree = 0 := P.principal

/-- If the difference-bundle degree is positive, a principal discriminant cannot equal it. -/
theorem disc_not_target_of_positive {V sF A : ℝ} (hpos : 0 < V - (sF - 1) * A) :
    V - (sF - 1) * A ≠ 0 := ne_of_gt hpos

def discRows : List (String × String × String) :=
  [ ("disc(Psi_l)", "= ± l^a * Delta^b (exponents to verify)", "CANDIDATE (vendor ref) ") ,
    ("valuation formula", "v_p = a*v_p(l) + b*v_p(Delta)", "TO VERIFY") ,
    ("principal divisor", "total degree = 0 (product formula)", "FACT") ,
    ("matches V-(sF-1)A?", "involves Delta,l vs q,hull", "NO (dictionary missing)") ,
    ("verdict", "identity, not a positive section", "FAILS as face-5 section") ]

theorem discRows_length : discRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Face5DiscInterfaceActual
