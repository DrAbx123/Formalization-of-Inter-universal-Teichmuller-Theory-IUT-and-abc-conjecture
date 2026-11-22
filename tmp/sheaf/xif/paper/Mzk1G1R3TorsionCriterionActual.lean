/- R3 / torsion criterion: M1 (n=2), M3-first-half (n=5 x-coordinate), M5 (Legendre).

  MILESTONES (Lead plan):
  M1  `2 • P = 0 ↔ evalDivisionPolynomialAtPoint 2 P = 0`  (Mathlib donor) -- done here;
  M2  n = 4: needs the doubling chain (identity `ψ₂([2]P) = ψ₄(P)/ψ₂(P)^3` or the `y([2]P)=0`
      computation, in the style of S1373's n=3 proof); NOT in Mathlib/tree => OPEN.
  M3  n = 5 x-coordinate formula: first half done here (odd n: ψ₅(x,y) = preΨ₅(x));
      second half `x([5]P) = Φ₅(P)/ΨSq₅(P)` is henry's G1.
  M4  `5 • P = 0 ↔ evalDivisionPolynomial 5 = 0`: waits on G1/G2 (henry).
  M5  Legendre instantiation: done here (ψ₅ = legendreΨ₅(x)).
  `torsionCoords` is NOT closed (route ②-⑤: ② done, ③④⑤ open). No sorry/axiom. -/
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaTorsionFiveActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3TorsionCriterionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTorsionFiveActual

/-- **M1**：`n = 2` criterion（Mathlib donor re-export）。 -/
theorem two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (P : W.toAffine.Point) :
    (2 : ℕ) • P = 0 ↔ W.evalDivisionPolynomialAtPoint 2 P = 0 :=
  W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero P

/-- **M3（前半）**：n=5 时 `ψ₅(x,y)` 只看 x 且等于 `preΨ₅(x)`。 -/
theorem five_evalDivisionPolynomial_eq_preΨ {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) :
    W.evalDivisionPolynomial x y 5 = (W.preΨ 5).eval x :=
  W.evalDivisionPolynomial_eq_eval_preΨ_of_odd h (by decide : ¬ Even (5 : ℤ))

/-- **M5（前半）**：Legendre 曲线上 `ψ₅(x,y) = legendreΨ₅(x)`。 -/
theorem legendre_five_evalDivisionPolynomial_eq {x y : ℂ}
    (h : (legendreWeierstrassCurve lam).toAffine.Equation x y) :
    (legendreWeierstrassCurve lam).evalDivisionPolynomial x y 5 = (legendreΨ₅ lam).eval x := by
  rw [five_evalDivisionPolynomial_eq_preΨ (W := legendreWeierstrassCurve lam) h]
  rfl

/-- **M5（根形式）**：`ψ₅(x,y) = 0 ↔ Ψ₅(x) = 0`。 -/
theorem legendre_five_root_iff {x y : ℂ}
    (h : (legendreWeierstrassCurve lam).toAffine.Equation x y) :
    (legendreWeierstrassCurve lam).evalDivisionPolynomial x y 5 = 0 ↔
      (legendreΨ₅ lam).eval x = 0 := by
  constructor
  · intro hzero
    rwa [legendre_five_evalDivisionPolynomial_eq (lam := lam) h] at hzero
  · intro hzero
    rwa [← legendre_five_evalDivisionPolynomial_eq (lam := lam) h] at hzero

/-- **M5b**：Legendre 曲线 n=2 criterion（点级，donor）。 -/
theorem legendre_two_nsmul_some_iff_evalDivisionPolynomial_two {x y : ℂ}
    (hns : (legendreWeierstrassCurve lam).toAffine.Nonsingular x y) :
    (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hns = 0 ↔
      (legendreWeierstrassCurve lam).evalDivisionPolynomial x y 2 = 0 :=
  (legendreWeierstrassCurve lam).two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero hns

#print axioms two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero
#print axioms five_evalDivisionPolynomial_eq_preΨ
#print axioms legendre_five_evalDivisionPolynomial_eq
#print axioms legendre_five_root_iff

#print axioms legendre_two_nsmul_some_iff_evalDivisionPolynomial_two

end LeanFormal.IUT.XiFPaper.Mzk1G1R3TorsionCriterionActual