/- R1 brick (hW reduction): the native bad local weight `nativeBadLocalWeight` is `(2l)⁻¹`
as soon as the relative completion degree at the native bad K-place equals the full
root-extension degree `2l`. Definitions reused:
- `VbadPlaceIndexingActual.nativeBadLocalWeight` / `nativeBadLocalWeight_eq_inv`
  (`= (localCompletionDegree T.arithmetic (nativeBadToKPlace T b))⁻¹`),
- `ProcessionNormalizationWeightsActual.localCompletionDegree`
  (`Module.finrank` of `K_w` over `Fmod_v`).
EXACT MISSING LEMMA (not asserted here): the local-global tower identity
  `Module.finrank ℚ_[p] K_w = localCompletionDegree T w * Module.finrank ℚ_[p] (Fmod_v)`
plus `localCompletionDegree T (nativeBadToKPlace T b) = 2 * l.value` (inertness/degree of
the Kummer root extension at the bad place). With those, hW reduces to the
`[F_P:Q_p] = dModF * e_abs / lamWeight_b` form used in the paper. -/
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R1INativeBadWeightDegreeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- **hW reduction**: if the relative completion degree at the native bad `K`-place is the
full root-extension degree `2l`, then the actual normalized local weight is `(2l)⁻¹`. -/
theorem nativeBadLocalWeight_eq_inv_two_l
    (hdeg : localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 2 * l.value) :
    nativeBadLocalWeight T b = ((2 * (l.value : ℝ)) : ℝ)⁻¹ := by
  rw [nativeBadLocalWeight_eq_inv, hdeg]
  push_cast
  ring

#print axioms nativeBadLocalWeight_eq_inv_two_l
end LeanFormal.IUT.XiFPaper.Mzk1G1R1INativeBadWeightDegreeActual