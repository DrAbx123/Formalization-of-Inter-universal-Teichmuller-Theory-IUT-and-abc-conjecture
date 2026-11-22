/- U-R C2 J1 support (kurt): decomposition and membership lemmas for the K-side
possible images, for the same-q bridge and the packet-hull containment.

Contents:
* membership characterization of ksThetaPossibleImages;
* the identity automorphism is in the action family, so the pure-generator
  translate of the unit reference lies in the possible images;
* re-export of the possible-images/packet-hull containment.

Default heartbeats (no maxHeartbeats in this file).
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKPacketActual
import tmp.sheaf.xif.paper.Mzk1URThetaKCarrierActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Pointwise Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKJ1SupportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock (ksPlaces T b) ksTuple)]

/-- Membership characterization of the K-side possible images. -/
theorem mem_ksThetaPossibleImages_iff
    (varpi : CommonPrimeCompletion (ksPlace T b)) {s : ksBlock T b} :
    s ∈ ksThetaPossibleImages (l := l) T b varpi ↔
      ∃ φ : ksBlock T b ≃ₗ[ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]]
          ksBlock T b, φ ∈ ksThetaPhi (l := l) T b ∧
        ∃ x ∈ arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple,
          s = φ (arithmeticTupleTprod (ksPlaces T b) ksTuple
            (Function.update 1 ()
              varpi) * x) := by
  unfold ksThetaPossibleImages
  rfl

/-- The identity automorphism belongs to the K-side action family. -/
theorem ksThetaPhi_id_mem :
    (LinearEquiv.refl ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]
      (ksBlock T b)) ∈ ksThetaPhi (l := l) T b :=
  Mzk1URThetaKCarrierActual.urP6Phi_id_mem (ksPlaces T b) ksTuple

/-- The pure-generator translate of the unit reference lies in the possible images
(the identity automorphism witness). -/
theorem pureGenerator_smul_subset_possibleImages
    (varpi : CommonPrimeCompletion (ksPlace T b)) :
    (arithmeticTupleTprod (ksPlaces T b) ksTuple
        (Function.update 1 ()
          varpi)) • arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple ⊆
      ksThetaPossibleImages (l := l) T b varpi := by
  intro s hs
  obtain ⟨x, hx, rfl⟩ := hs
  rw [mem_ksThetaPossibleImages_iff]
  refine ⟨LinearEquiv.refl _ _, ksThetaPhi_id_mem (l := l) T b, x, hx, ?_⟩
  simp [LinearEquiv.refl_apply]

/-- Re-export: the K-side possible images are contained in the packet hull. -/
theorem possibleImages_subset_packetHull
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
  ksThetaPossibleImages_subset_packetHull (l := l) T b e varpi


/-- The pure-generator translate of the unit reference lies in the packet hull. -/
theorem pureGenerator_smul_subset_packetHull
    [MeasurableSpace (ksBlock T b)] [BorelSpace (ksBlock T b)]
    {J : Type} [Finite J] {E : J → Type}
    [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)]
    [∀ j, FiniteDimensional ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (E j)]
    [∀ j, ProperSpace (E j)]
    (e : ksBlock T b ≃ₐ[ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]]
      ((j : J) → E j))
    (varpi : CommonPrimeCompletion (ksPlace T b)) :
    (arithmeticTupleTprod (ksPlaces T b) ksTuple
        (Function.update 1 ()
          varpi)) • arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple ⊆
      ksThetaPacketHull (l := l) T b e varpi :=
  (pureGenerator_smul_subset_possibleImages (l := l) T b varpi).trans
    (ksThetaPossibleImages_subset_packetHull (l := l) T b e varpi)


/-- Set decomposition of the K-side possible images as a union over the action
family and the unit reference. -/
theorem ksThetaPossibleImages_eq_iUnion
    (varpi : CommonPrimeCompletion (ksPlace T b)) :
    ksThetaPossibleImages (l := l) T b varpi =
      ⋃ (φ : ksBlock T b ≃ₗ[ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]]
            ksBlock T b) (_ : φ ∈ ksThetaPhi (l := l) T b),
        ⋃ x ∈ arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple,
          {φ (arithmeticTupleTprod (ksPlaces T b) ksTuple
            (Function.update (1 : (i : QVFamTensorCoefficientActual.qVFamTensorV) →
              CommonPrimeCompletion ((ksPlaces T b) i (ksTuple i))) () varpi) * x)} := by
  ext s
  rw [mem_ksThetaPossibleImages_iff]
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_and_left, exists_prop]

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKJ1SupportActual
end