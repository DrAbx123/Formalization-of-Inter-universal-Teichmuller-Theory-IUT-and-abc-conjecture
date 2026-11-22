/- B1/O3 helper for emmy's `hout`: which primes contain `hPolyLam h`.

  `hPolyLam h = X ^ h.natDegree * invSelf (hRev h)` in `Localization.Away (hRev h)`
  (Mzk1G1PsiHPolyActual). Since `invSelf` is a unit, a prime contains `hPolyLam h` iff it
  contains `X ^ h.natDegree`, hence (prime, natDegree > 0) iff it contains `X`, i.e. iff the
  lambda-coordinate point is `p1Zero`. This is the `p1Zero` part of `hout`. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1ZeroJudgeActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyLamZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

variable (h : Polynomial ℚ)

/-- **`hPolyLam h` 的素点判定**：`hPolyLam h ∈ p ↔ X ∈ p`（`natDegree > 0`）。 -/
theorem hPolyLam_mem_iff (hdeg : 0 < h.natDegree)
    (p : PrimeSpectrum (Localization.Away (hRev h))) :
    hPolyLam h ∈ p.asIdeal ↔
      algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X ∈ p.asIdeal := by
  have hu : IsUnit (IsLocalization.Away.invSelf (x := hRev h)) :=
    IsUnit.of_mul_eq_one (algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) (hRev h))
      (by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf (x := hRev h))
  rw [hPolyLam, mul_comm, Ideal.unit_mul_mem_iff_mem _ hu]
  constructor
  · intro hp
    exact (inferInstance : p.asIdeal.IsPrime).mem_of_pow_mem h.natDegree hp
  · intro hp
    exact (p.asIdeal).pow_mem_of_mem hp h.natDegree hdeg

#print axioms hPolyLam_mem_iff
/-- **`hout` 的 p1Zero 合成版**：`chartMorphism0 (hPolyLam h)` 打到 `p1Zero` 当且仅当该点含 `X`。 -/
theorem chartMorphism0_hPolyLam_mem_p1Zero_iff (hdeg : 0 < h.natDegree)
    (p : PrimeSpectrum (Localization.Away (hRev h))) :
    chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h) p ∈ p1Zero ↔
      algebraMap (Polynomial ℚ) (Localization.Away (hRev h)) Polynomial.X ∈ p.asIdeal := by
  rw [chartMorphism0_mem_p1Zero_iff, hPolyLam_mem_iff h hdeg p]

#print axioms chartMorphism0_hPolyLam_mem_p1Zero_iff


end LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyLamZeroActual