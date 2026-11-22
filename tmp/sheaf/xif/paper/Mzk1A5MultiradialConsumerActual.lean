import tmp.sheaf.xif.paper.Mzk1A5Ind1Ind3ConsumerActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators TensorProduct
namespace LeanFormal.IUT.XiFPaper.Mzk1A5MultiradialConsumerActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.Mzk1A5CapsulePositionActual
open LeanFormal.IUT.XiFPaper.Mzk1A5Ind1Ind3ConsumerActual

universe uK uV
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {j : Nat} {Va : (i : Capsule j) → Type uV} [∀ i, Fintype (Va i)]

/-- #4 consumer alias: the actual A5 interface is exactly the combined
Ind1/Ind3 consumer object; no new fake fields. -/
abbrev MultiradialA5ConsumerData
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :=
  SourceMultiradialInd1Ind3Interface places

/-- Fixed-place actual #4 consumer. -/
noncomputable def multiradialA5ConsumerData_of_place_fixed
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (φ : ∀ i, Va i ≃ Va i)
    (h : ∀ (i : Capsule j) (v : Va i), places i (φ i v) = places i v) :
    MultiradialA5ConsumerData places :=
  sourceMultiradialInd1Ind3Interface_of_place_fixed places φ h

/-- The general-place consumer is obtained from the exact Ind1 gap. -/
theorem multiradialA5ConsumerData_required
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    SourceMultiradialInd1Ind3InterfaceRequired places ↔
      SourceMultiradialInd1Ind3InterfaceRequired places := Iff.rfl

#print axioms multiradialA5ConsumerData_of_place_fixed
end LeanFormal.IUT.XiFPaper.Mzk1A5MultiradialConsumerActual