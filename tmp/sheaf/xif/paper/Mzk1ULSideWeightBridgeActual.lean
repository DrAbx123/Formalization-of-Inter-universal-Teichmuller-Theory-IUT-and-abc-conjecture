/- U-C weight bridge: bad-place set and its inclusion into differentPlaces.

STATUS: this file currently contains ONLY the hole-free part (RamifiedBad /
ramifiedBad / badPlaceSet / badPlaceSet_subset_differentPlaces).  The conditional
helper (hram/hdelta -> sum inequality) is deliberately NOT added yet:
  TEMPORARY HOLES (do not enter hstepVIII/hii consumption, not a final theorem):
   - hram  <- alan p-adic donors (localDifferentIdeal_eq_top_of_unramified,
              localDifferentOrder_eq_zero_of_localDifferentIdeal_eq_top)
              + kurt count bridge;
   - hdelta <- kurt localDifferentPaperOrder = differentExponent
              + ksP_eq_qVFamTensorP.
Once the donors land, the UNCONDITIONAL bad_weighted_sum_le_logDifferentK is
proved in this same file from david's
paperWeightedDeltaSum_subset_le_logDifferentK' (19:49:17); the conditional
helper is only an intermediate and will be removed.
Provenance: paper IUT IV L1236-1251 (normalized degree), L1420-1433; david
differentPlaces/paperDifferentWeight; sophie ksD/ksP (19:47:13).
-/
import tmp.sheaf.xif.paper.Mzk1ULKSideLettersActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1G1LocalDifferentOrderZeroActual
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSideWeightBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- bad places whose K-side local different order is nonzero (i.e. ramified). -/
def RamifiedBad (b : Bad (nativePlaceSelection T)) : Prop := ksD T b ≠ 0

/-- the finite set of ramified bad places. -/
noncomputable def ramifiedBad : Finset (Bad (nativePlaceSelection T)) := by
  classical exact Finset.univ.filter (fun b => ksD T b ≠ 0)

/-- membership in the ramified bad subset. -/
theorem mem_ramifiedBad_iff (b : Bad (nativePlaceSelection T)) :
    b ∈ ramifiedBad T ↔ ksD T b ≠ 0 := by
  classical simp [ramifiedBad]

/-- the corresponding set of K-side primes (ideals of O_K). -/
noncomputable def badPlaceSet : Finset (Ideal (NumberField.RingOfIntegers T.arithmetic.K)) :=
  (ramifiedBad T).image (fun b => (nativeBadToKPlace T b).maximalIdeal.asIdeal)

/-- CONDITIONALLY (on hram) the bad-place set lies in differentPlaces; the
unconditional version needs alan's p-adic donors and kurt's count bridge. -/
theorem badPlaceSet_subset_differentPlaces
    (hram : ∀ b : Bad (nativePlaceSelection T), ksD T b ≠ 0 →
      (nativeBadToKPlace T b).maximalIdeal.asIdeal
        ∈ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces
            T.arithmetic.K) :
    badPlaceSet T ⊆ LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual.differentPlaces
      T.arithmetic.K := by
  intro P hP
  classical
  rcases Finset.mem_image.mp hP with ⟨b, hb, rfl⟩
  exact hram b ((mem_ramifiedBad_iff T b).mp hb)




/-- PROVED: ksD = localDifferentPaperOrder * ksLogP (the paper delta/e slot),
using the paper-order identity for the different generator. -/
theorem ksD_eq_paperOrder_mul_ksLogP (b : Bad (nativePlaceSelection T)) :
    ksD T b = LeanFormal.IUT.IntegralTraceDualTensorInclusion.localDifferentPaperOrder
      (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
      (L := CommonPrimeCompletion (ksPlace T b)) * ksLogP T b := by
  unfold ksD ksLogP
  rw [LeanFormal.IUT.LocalDifferentNormOrder.localNormOrder_differentGenerator_eq_paperOrder
    (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
    (K := CommonPrimeCompletion (ksPlace T b))]
  simp only [ksP]

end LeanFormal.IUT.XiFPaper.Mzk1ULSideWeightBridgeActual
end