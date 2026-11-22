import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Dependent log-shell families and the actual multi-place packet

This file supplies the carrier-level alignment recorded as the second item of
the N4--N7 gap card.  The place type of a log-shell family may depend on the
capsule label, which is necessary for the actual arithmetic family
`i |-> (v : Va i) |-> CommonPrimeCompletion (places i v)`.

Main results:

* `LogShellFamilyDependent` and `TensorPacketDependent` are the dependent
  analogues of `LogShellFamily` and `TensorPacket`;
* `arithmeticLogShellFamilyDependent` is the actual arithmetic family;
* `arithmeticDependentTensorPacket_eq_arithmeticPacketTensor` identifies its
  tensor packet definitionally with `ArithmeticPacketTensor`;
* `arithmeticLogShellFactorRegion_eq_completionPacketLogRegion` and
  `arithmeticDependentTensorLogRegion_eq_arithmeticTensorLogRegion` show how
  the per-place `logShell = integralLogShell` equality enters the tensor
  packet.

The index type is the source capsule `Capsule j = Fin (j + 1)`.  For a general
index type `iota` one needs an equivalence `Capsule j ~= iota` and the induced
reindexing of the tensor packet; this is not needed for the capsule-indexed
arithmetic packet used here.

This is a multi-place carrier alignment only.  It does not construct the
source theta-pilot possible image, does not define a comparison map from that
image to the arithmetic integral tensor lattice, and does not prove
`possibleThetaPilotImageSet` is contained in `I_tensor`.  The region
equalities below are identifications of actual arithmetic carriers, not a
source-image inclusion.
-/

namespace LeanFormal.IUT

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

open scoped TensorProduct BigOperators

noncomputable section

universe uR uVQ uPlace uShell uK uV

/-- A log-shell family whose place type may depend on the capsule label.
For each capsule label `i`, valuation `vQ`, and place `v : Place i vQ`, the
field `Shell i vQ v` records the actual log-shell module.  The additive and
scalar structures are per-point fields, not global assumptions. -/
structure LogShellFamilyDependent (R : Type uR) [CommSemiring R]
    {VQ : Type uVQ} (j : Nat)
    (Place : (i : Capsule j) → VQ → Type uPlace) where
  Shell : (i : Capsule j) → (vQ : VQ) → Place i vQ → Type uShell
  [addCommMonoid : ∀ i vQ v, AddCommMonoid (Shell i vQ v)]
  [module : ∀ i vQ v, Module R (Shell i vQ v)]

attribute [instance] LogShellFamilyDependent.addCommMonoid LogShellFamilyDependent.module

variable {R : Type uR} [CommSemiring R] {VQ : Type uVQ} {j : Nat}
variable {Place : (i : Capsule j) → VQ → Type uPlace}

/-- The dependent tensor packet: tensor over the capsule of the pointwise
product over the places over `vQ`.  When `Place i` does not depend on `i`,
this is the tensor packet of the original `LogShellFamily`. -/
abbrev TensorPacketDependent
    (L : LogShellFamilyDependent R j Place) (vQ : VQ) :=
  ⨂[R] i : Capsule j, ((v : Place i vQ) → L.Shell i vQ v)

section Arithmetic

variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {j : Nat} {Va : (i : Capsule j) → Type uV} [∀ i, Fintype (Va i)]

/-- The actual arithmetic dependent family.  The valuation type is `Unit`
(for the fixed rational prime `p`), the place type at capsule label `i` is
`Va i`, and the shell at a place `v` is the actual common-prime completion. -/
def arithmeticLogShellFamilyDependent
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    LogShellFamilyDependent ℚ_[p] j (fun i (_ : Unit) => Va i) where
  Shell := fun i _ v => CommonPrimeCompletion (places i v)
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

omit [∀ i, Fintype (Va i)] in
/-- The shell type of the actual arithmetic family is the common-prime
completion at the corresponding place. -/
@[simp] theorem arithmeticLogShellFamilyDependent_Shell
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (i : Capsule j) (vQ : Unit) (v : Va i) :
    (arithmeticLogShellFamilyDependent (p := p) places).Shell i vQ v =
      CommonPrimeCompletion (places i v) := rfl

/-- The dependent tensor packet of the actual arithmetic family, at the
unique rational valuation. -/
abbrev arithmeticDependentTensorPacket
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :=
  TensorPacketDependent (arithmeticLogShellFamilyDependent (p := p) places) ()

/-- The actual arithmetic dependent tensor packet is definitionally the
existing `ArithmeticPacketTensor`. -/
theorem arithmeticDependentTensorPacket_eq_arithmeticPacketTensor
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    arithmeticDependentTensorPacket (p := p) places =
      ArithmeticPacketTensor (p := p) places := by
  rfl

/-- The identity linear equivalence witnessing the carrier alignment. -/
def arithmeticDependentTensorPacketLinearEquiv
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    arithmeticDependentTensorPacket (p := p) places ≃ₗ[ℚ_[p]]
      ArithmeticPacketTensor (p := p) places :=
  LinearEquiv.refl ℚ_[p] _

/-- The per-place actual source log-shell datum family. -/
def arithmeticLocalLogShellDatumFamily
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    (i : Capsule j) → (v : Va i) → SourceLogShellDatum :=
  fun i v => sourceLocalLogShellDatum (p := p) (places i v)

omit [∀ i, Fintype (Va i)] in
/-- Each member of the family has the actual integral log-shell of its
common-prime completion. -/
theorem arithmeticLocalLogShellDatumFamily_logShell_eq_integralLogShell
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (i : Capsule j) (v : Va i) :
    (arithmeticLocalLogShellDatumFamily (p := p) places i v).logShell =
      (integralLogShell (K := CommonPrimeCompletion (places i v)) (p := p) :
        Set (CommonPrimeCompletion (places i v))) :=
  sourceLocalLogShellDatum_logShell_eq_integralLogShell (p := p) (places i v)

/-- The datum-defined log region in the direct-sum factor at capsule label
`i`. -/
def arithmeticLogShellFactorRegion
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (i : Capsule j) :
    Set ((v : Va i) → CommonPrimeCompletion (places i v)) :=
  Set.pi Set.univ (fun v =>
    (arithmeticLocalLogShellDatumFamily (p := p) places i v).logShell)

omit [∀ i, Fintype (Va i)] in
/-- The datum-defined factor region is the actual completion packet log
region; this is where the per-place bridge enters the tensor factor. -/
theorem arithmeticLogShellFactorRegion_eq_completionPacketLogRegion
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (i : Capsule j) :
    arithmeticLogShellFactorRegion (p := p) places i =
      completionPacketLogRegion (p := p) (places i) := by
  unfold arithmeticLogShellFactorRegion completionPacketLogRegion
  exact congrArg (Set.pi Set.univ)
    (funext fun v =>
      arithmeticLocalLogShellDatumFamily_logShell_eq_integralLogShell
        (p := p) places i v)

/-- The actual tensor log region carried by the dependent packet. -/
def arithmeticDependentTensorLogRegion
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    Set (arithmeticDependentTensorPacket (p := p) places) :=
  tensorIntegralRegion (p := p) (M := fun i => CompletionPacket (places i))
    (fun i => completionPacketLogRegion (p := p) (places i))

/-- The dependent tensor log region is exactly the existing actual
arithmetic tensor log region. -/
theorem arithmeticDependentTensorLogRegion_eq_arithmeticTensorLogRegion
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p) :
    arithmeticDependentTensorLogRegion (p := p) places =
      arithmeticTensorLogRegion (p := p) places := by
  rfl

end Arithmetic

/-! ## Axiom probe -/

#print axioms LogShellFamilyDependent
#print axioms TensorPacketDependent
#print axioms arithmeticLogShellFamilyDependent
#print axioms arithmeticLogShellFamilyDependent_Shell
#print axioms arithmeticDependentTensorPacket
#print axioms arithmeticDependentTensorPacket_eq_arithmeticPacketTensor
#print axioms arithmeticDependentTensorPacketLinearEquiv
#print axioms arithmeticLocalLogShellDatumFamily
#print axioms arithmeticLocalLogShellDatumFamily_logShell_eq_integralLogShell
#print axioms arithmeticLogShellFactorRegion
#print axioms arithmeticLogShellFactorRegion_eq_completionPacketLogRegion
#print axioms arithmeticDependentTensorLogRegion
#print axioms arithmeticDependentTensorLogRegion_eq_arithmeticTensorLogRegion

end

end LeanFormal.IUT
