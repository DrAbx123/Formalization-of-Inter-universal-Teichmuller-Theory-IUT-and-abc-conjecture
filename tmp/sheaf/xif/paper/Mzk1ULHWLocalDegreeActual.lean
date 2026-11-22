/- hW (outer weight) at the actual local degree, and the exact mismatch with thetaLamWeight.

  `nativeBadLocalWeight T b = localNormalizedWeight T.arithmetic (nativeBadToKPlace T b)
    = ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)^{-1}`
  (already `nativeBadLocalWeight_eq_inv`).  Here the exact multiplicative form
    `nativeBadLocalWeight * localCompletionDegree = 1`
  is recorded, together with `thetaLamWeight = lamWeight/dModF`
  (`lamWeight = [Fmod_v:Qp]`, `dModF = [Fmod:Q]`).
  MISMATCH: `nativeBadLocalWeight = thetaLamWeight/(2l)` is NOT derivable: it would force
  `2l * [Fmod:Q] = [Fmod_v:Qp] * [K_w:(Fmod)_v]`, i.e. total ramification 2l, which is
  false in general (K/F is not 2l).  Thus the paper Theta route must use `rootNormHull`
  with the spectral c_P/(2l) coefficient, not this identity.
  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHWLocalDegreeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- hW 的等价逆形式（来自 DONE 的 `nativeBadLocalWeight_eq_inv`）。 -/
theorem hW_eq_inv (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : ℕ) : ℝ)⁻¹ :=
  nativeBadLocalWeight_eq_inv (l := l) T b

/-- **hW 乘实际局部次数 = 1**（局部次数非零时）。 -/
theorem hW_mul_localCompletionDegree (b : Bad (nativePlaceSelection T))
    (hdeg : localCompletionDegree T.arithmetic (nativeBadToKPlace T b) ≠ 0) :
    nativeBadLocalWeight T b *
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : ℕ) : ℝ) = 1 := by
  rw [hW_eq_inv (l := l) T b]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hdeg)

/-- thetaLamWeight 的定义展开：`[Fmod_v:Qp]/[Fmod:Q]`。 -/
theorem thetaLamWeight_eq (b : Bad (nativePlaceSelection T)) :
    thetaLamWeight (l := l) T b = lamWeight (l := l) T b / dModF (l := l) T := rfl

#print axioms hW_eq_inv
#print axioms hW_mul_localCompletionDegree
#print axioms thetaLamWeight_eq

end LeanFormal.IUT.XiFPaper.Mzk1ULHWLocalDegreeActual
