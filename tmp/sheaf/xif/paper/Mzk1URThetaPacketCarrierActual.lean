/- U-R C2 theta side (B): actual T-side packet carrier (route §5.3 J1).

Lead split: sophie owns (A) the hull log-volume monotonicity / weighted H_pkt form;
this file owns (B): `p6Phi` / `p6PacketHull` instantiated directly on the actual
**T-side** places/tuple (`qVFamTensorPlaces T b` / `qVFamTensorTuple`), so the theta
region and the packet hull live on the **same carrier** (`qVFamTensorBlock T b`).
The field decomposition `e` is an explicit argument: consumers instantiate it with the
actual tensor-core witness (`tensorCoreWitness`) or any actual decomposition; the
containment theorem is then the actual-data form of the packet-hull donor.  This
avoids the unproved `p6P = qVFamTensorP` choice-equality entirely. -/
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaPacketCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual T-side action family `p6Phi` on the qVFamily tensor block. -/
noncomputable abbrev urThetaPhi :
    Set (qVFamTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] qVFamTensorBlock T b) :=
  p6Phi (qVFamTensorPlaces T b) qVFamTensorTuple

/-- The actual T-side theta possible images for a genuine Kummer element `varpi`. -/
noncomputable abbrev urThetaPossibleImages
    (varpi : CommonPrimeCompletion ((qVFamTensorPlaces T b) () ())) :
    Set (qVFamTensorBlock T b) :=
  arithmeticTupleStepVPossibleImages (qVFamTensorPlaces T b) qVFamTensorTuple
    () varpi (urThetaPhi T b)

/-- The actual T-side packet hull, in a field decomposition `e` of the same
carrier (same carrier as the theta region). -/
noncomputable abbrev urThetaPacketHull
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[qVFamTensorP T b] (E j)]
    [∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (E j)] [∀ j, ProperSpace (E j)]
    (e : qVFamTensorBlock T b ≃ₐ[ℚ_[qVFamTensorP T b]] ((j : J) → E j))
    (varpi : CommonPrimeCompletion ((qVFamTensorPlaces T b) () ())) :
    Set (qVFamTensorBlock T b) :=
  p6PacketHull (qVFamTensorPlaces T b) qVFamTensorTuple e () varpi

/-- **Same-carrier theta containment** (route §5.3 J1): the actual T-side theta
possible images are contained in the actual T-side packet hull, for the same
actual places/tuple and any actual field decomposition `e` of the carrier. -/
theorem urThetaPossibleImages_subset_packetHull
    [MeasurableSpace (ArithmeticTensorTupleBlock
      (qVFamTensorPlaces T b) qVFamTensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock
      (qVFamTensorPlaces T b) qVFamTensorTuple)]
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[qVFamTensorP T b] (E j)]
    [∀ j, FiniteDimensional ℚ_[qVFamTensorP T b] (E j)] [∀ j, ProperSpace (E j)]
    (e : qVFamTensorBlock T b ≃ₐ[ℚ_[qVFamTensorP T b]] ((j : J) → E j))
    (varpi : CommonPrimeCompletion ((qVFamTensorPlaces T b) () ())) :
    urThetaPossibleImages T b varpi ⊆ urThetaPacketHull T b e varpi :=
  p6_possibleImages_subset_packetHull (p := qVFamTensorP T b)
    (qVFamTensorPlaces T b) qVFamTensorTuple e () varpi

#print axioms urThetaPossibleImages_subset_packetHull

end LeanFormal.IUT.XiFPaper.Mzk1URThetaPacketCarrierActual
end