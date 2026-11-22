import LeanFormal.IUT.IUTIII.Theorem311.SourceLogShellFamilyDependent
import Mathlib.Tactic

noncomputable section
open scoped BigOperators TensorProduct
namespace LeanFormal.IUT.XiFPaper.Mzk1A5CapsulePositionActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

universe uK uV
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {j : Nat} {Va : (i : Capsule j) → Type uV} [∀ i, Fintype (Va i)]

/-- A5 capsule position at one rational prime p and level j: a label i in
`Capsule j` together with an actual place over p in its fiber `Va i`.  This is
the dependent-sum procession index, not a global Cartesian product. -/
abbrev CapsulePosition (Va : (i : Capsule j) → Type uV) : Type (max 0 uV) :=
  Sigma Va

theorem capsulePosition_mk (i : Capsule j) (v : Va i) :
    (⟨i, v⟩ : CapsulePosition Va) = ⟨i, v⟩ := rfl

/-- The adjacent-level label inclusion `Capsule j -> Capsule (j+1)`. -/
def capsuleLabelSucc : Capsule j → Capsule (j + 1) :=
  Fin.castLE (by omega)

theorem capsuleLabelSucc_val (i : Capsule j) :
    (capsuleLabelSucc i : Nat) = i.val := rfl

/-- The actual dependent log-shell family at p, level j, and places Va. -/
abbrev actualCapsuleLogShellFamily
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :=
  arithmeticLogShellFamilyDependent (p := p) places

/-- Its actual tensor packet is the arithmetic packet tensor. -/
theorem actualCapsuleTensorPacket_eq_arithmetic
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    arithmeticDependentTensorPacket (p := p) places =
      ArithmeticPacketTensor (p := p) places := rfl

#print axioms actualCapsuleTensorPacket_eq_arithmetic

/-- Ind1 index action: a permutation of capsule labels together with a
compatible permutation of the actual places in the dependent fibers. -/
def capsulePositionEquiv (e : Capsule j ≃ Capsule j)
    (φ : ∀ i, Va i ≃ Va (e i)) :
    CapsulePosition Va ≃ CapsulePosition Va :=
  Equiv.sigmaCongr e φ

@[simp] theorem capsulePositionEquiv_apply
    (e : Capsule j ≃ Capsule j) (φ : ∀ i, Va i ≃ Va (e i))
    (i : Capsule j) (v : Va i) :
    capsulePositionEquiv e φ ⟨i, v⟩ = ⟨e i, φ i v⟩ := rfl

/-- Exact missing datum for the tensor-packet Ind1 square: a compatible
transport of the actual local log-shell modules along the place permutation. -/
structure Ind1ShellTransport
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) where
  labelPerm : Capsule j ≃ Capsule j
  placeEquiv : ∀ i, Va i ≃ Va (labelPerm i)
  shellEquiv : ∀ i (v : Va i),
    CommonPrimeCompletion (places i v) ≃ₗ[ℚ_[p]]
      CommonPrimeCompletion (places (labelPerm i) (placeEquiv i v))

def Ind1ShellTransportGap
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) : Prop :=
  Nonempty (Ind1ShellTransport places)


/-- Ind3 local log-link inclusion at one p, one capsule label i: the actual
source datum region is contained in the arithmetic completion packet region. -/
theorem capsuleFactorLogLink_subset
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (i : Capsule j) :
    arithmeticLogShellFactorRegion (p := p) places i ⊆
      completionPacketLogRegion (p := p) (places i) := by
  rw [arithmeticLogShellFactorRegion_eq_completionPacketLogRegion]


/-- The label component of the Ind1 dependent-sum action is the label
permutation `e`. -/
@[simp] theorem capsulePositionEquiv_fst
    (e : Capsule j ≃ Capsule j) (φ : ∀ i, Va i ≃ Va (e i))
    (x : CapsulePosition Va) :
    (capsulePositionEquiv e φ x).1 = e x.1 := rfl

/-- The adjacent-level label inclusion is injective. -/
theorem capsuleLabelSucc_injective :
    Function.Injective (capsuleLabelSucc (j := j)) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [capsuleLabelSucc] using hv

/-- Ind3 at one tensor packet: the dependent actual tensor log region is
contained in the arithmetic tensor log region. -/
theorem capsuleTensorLogLink_subset
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    arithmeticDependentTensorLogRegion (p := p) places ⊆
      arithmeticTensorLogRegion (p := p) places := by
  rw [arithmeticDependentTensorLogRegion_eq_arithmeticTensorLogRegion]


/-- Conditional Ind1 shell transport: if a place permutation fixes the actual
place value in every fiber, the local completion transport is the identity
after rewriting along that equality. -/
def ind1ShellTransport_of_place_fixed
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (φ : ∀ i, Va i ≃ Va i)
    (h : ∀ (i : Capsule j) (v : Va i), places i (φ i v) = places i v) :
    Ind1ShellTransport places where
  labelPerm := Equiv.refl (Capsule j)
  placeEquiv := φ
  shellEquiv := fun i v => by
    change CommonPrimeCompletion (places i v) ≃ₗ[ℚ_[p]]
      CommonPrimeCompletion (places i (φ i v))
    rw [h i v]


/-- The fixed-place case supplies an actual inhabitant of the Ind1 shell
transport gap. -/
theorem ind1ShellTransportGap_holds_of_place_fixed
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (φ : ∀ i, Va i ≃ Va i)
    (h : ∀ (i : Capsule j) (v : Va i), places i (φ i v) = places i v) :
    Ind1ShellTransportGap places :=
  ⟨ind1ShellTransport_of_place_fixed places φ h⟩



/-- Variant of Ind1 transport for a *specified* label/place permutation.  This
is the nontrivial form needed for #4; the bare `Ind1ShellTransportGap` is
trivially inhabited by the identity permutation and is not enough for a
nontrivial procession automorphism. -/
structure Ind1ShellTransportFor
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (e : Capsule j ≃ Capsule j)
    (φ : ∀ i, Va i ≃ Va (e i)) where
  shellEquiv : ∀ i (v : Va i),
    CommonPrimeCompletion (places i v) ≃ₗ[ℚ_[p]]
      CommonPrimeCompletion (places (e i) (φ i v))

def Ind1ShellTransportForRequired
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (e : Capsule j ≃ Capsule j)
    (φ : ∀ i, Va i ≃ Va (e i)) : Prop :=
  Nonempty (Ind1ShellTransportFor places e φ)

/-- Identity permutation: the specified-transport structure is inhabited by
the identity linear equivalence (definitional equality only in this case). -/
def ind1ShellTransportFor_refl
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    Ind1ShellTransportFor places (Equiv.refl (Capsule j))
      (fun i => Equiv.refl (Va i)) where
  shellEquiv := fun i v => by
    change CommonPrimeCompletion (places i v) ≃ₗ[ℚ_[p]]
      CommonPrimeCompletion (places i v)
    exact LinearEquiv.refl ℚ_[p] _

end LeanFormal.IUT.XiFPaper.Mzk1A5CapsulePositionActual