/- U-R C2 (P): K-side theta packet carrier (kurt).

Same shape as the old F-side Mzk1URThetaPacketCarrierActual, re-instantiated on the
K-completion carrier (ksPlaces/ksTuple, raw rational prime of sophie's R1 syntax).
The field decomposition e is an explicit argument (consumers pass the actual
tensor-core witness).  Containment theorem is the p6 packet-hull donor shape.

Default heartbeats (heartbeat-cleanup batch). -/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKPacketActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The K-side actual action family p6Phi on the K tensor block. -/
noncomputable abbrev ksThetaPhi :
    Set (ksBlock T b ≃ₗ[ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]]
      ksBlock T b) :=
  p6Phi (ksPlaces T b) ksTuple

/-- The K-side theta possible images for a genuine Kummer element varpi. -/
noncomputable abbrev ksThetaPossibleImages
    (varpi : CommonPrimeCompletion (ksPlace T b)) : Set (ksBlock T b) :=
  arithmeticTupleStepVPossibleImages (ksPlaces T b) ksTuple () varpi
    (ksThetaPhi (l := l) T b)

/-- The K-side packet hull in a field decomposition e of the same carrier. -/
noncomputable abbrev ksThetaPacketHull
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)]
    [∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)]
    [∀ j, ProperSpace (E j)]
    (e : ksBlock T b ≃ₐ[ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]]
      ((j : J) → E j))
    (varpi : CommonPrimeCompletion (ksPlace T b)) : Set (ksBlock T b) :=
  p6PacketHull (ksPlaces T b) ksTuple e () varpi

/-- **Same-carrier K-side theta containment**: the K-side theta possible images are
contained in the K-side packet hull, for the same actual places/tuple and any actual
field decomposition e of the carrier. -/
theorem ksThetaPossibleImages_subset_packetHull
    [MeasurableSpace (ksBlock T b)] [BorelSpace (ksBlock T b)]
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)]
    [∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)]
    [∀ j, ProperSpace (E j)]
    (e : ksBlock T b ≃ₐ[ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]]
      ((j : J) → E j))
    (varpi : CommonPrimeCompletion (ksPlace T b)) :
    ksThetaPossibleImages (l := l) T b varpi ⊆
      ksThetaPacketHull (l := l) T b e varpi :=
  p6_possibleImages_subset_packetHull
    (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
    (ksPlaces T b) ksTuple e () varpi

#print axioms ksThetaPhi
#print axioms ksThetaPossibleImages
#print axioms ksThetaPossibleImages_subset_packetHull

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKPacketActual
end