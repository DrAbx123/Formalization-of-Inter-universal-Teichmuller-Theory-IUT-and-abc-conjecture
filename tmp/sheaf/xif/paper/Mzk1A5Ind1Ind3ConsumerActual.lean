import tmp.sheaf.xif.paper.Mzk1A5CapsulePositionActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators TensorProduct
namespace LeanFormal.IUT.XiFPaper.Mzk1A5Ind1Ind3ConsumerActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.Mzk1A5CapsulePositionActual

universe uK uV uVA
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {j : Nat} {Va : (i : Capsule j) → Type uV} [∀ i, Fintype (Va i)]

/-- Combined Ind1/Ind3 consumer interface at one p, one level j: an actual
Ind1 shell transport plus the Ind3 tensor log-region inclusion. -/
structure SourceMultiradialInd1Ind3Interface
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) where
  ind1Transport : Ind1ShellTransport places
  ind3LogLink :
    arithmeticDependentTensorLogRegion (p := p) places ⊆
      arithmeticTensorLogRegion (p := p) places

def SourceMultiradialInd1Ind3InterfaceRequired
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) : Prop :=
  Nonempty (SourceMultiradialInd1Ind3Interface places)

/-- Fixed-place case: an actual combined Ind1/Ind3 consumer interface. -/
def sourceMultiradialInd1Ind3Interface_of_place_fixed
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (φ : ∀ i, Va i ≃ Va i)
    (h : ∀ (i : Capsule j) (v : Va i), places i (φ i v) = places i v) :
    SourceMultiradialInd1Ind3Interface places where
  ind1Transport := ind1ShellTransport_of_place_fixed places φ h
  ind3LogLink := capsuleTensorLogLink_subset places

#print axioms sourceMultiradialInd1Ind3Interface_of_place_fixed

/-- Consumer interface for a *specified* nontrivial label/place permutation.
This is the form that must be used for a real procession automorphism;
consumers must supply the actual `e, φ`, not the identity-only bare gap. -/
structure SourceMultiradialInd1Ind3InterfaceFor
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (e : Capsule j ≃ Capsule j)
    (φ : ∀ i, Va i ≃ Va (e i)) where
  ind1Transport : Ind1ShellTransportFor places e φ
  ind3LogLink :
    arithmeticDependentTensorLogRegion (p := p) places ⊆
      arithmeticTensorLogRegion (p := p) places

def SourceMultiradialInd1Ind3InterfaceForRequired
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (e : Capsule j ≃ Capsule j)
    (φ : ∀ i, Va i ≃ Va (e i)) : Prop :=
  Nonempty (SourceMultiradialInd1Ind3InterfaceFor places e φ)

/-- From an actual specified Ind1 transport, build the combined interface. -/
def sourceMultiradialInd1Ind3InterfaceFor_of_transport
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (e : Capsule j ≃ Capsule j)
    (φ : ∀ i, Va i ≃ Va (e i))
    (h : Ind1ShellTransportFor places e φ) :
    SourceMultiradialInd1Ind3InterfaceFor places e φ where
  ind1Transport := h
  ind3LogLink := capsuleTensorLogLink_subset places

end LeanFormal.IUT.XiFPaper.Mzk1A5Ind1Ind3ConsumerActual