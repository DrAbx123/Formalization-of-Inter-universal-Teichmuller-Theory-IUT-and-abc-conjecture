import tmp.sheaf.xif.paper.S1338C3LDonorFieldsActual
import tmp.sheaf.xif.paper.ConcreteC3DonorActual
import tmp.sheaf.xif.paper.ConcreteC3DonorCompletionActual
/-! # S1354: L-side C3 donor restructure
Carrier is the algebraic closure L, not the completion.  Roots/kummerClass/
rootChange come from S1338 actual L fields.  The old SourcePilotRegionData
completion-valued roots/kummerClass remain a type mismatch; no completion root.
Tensor fields are the actual concrete tensor data. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.Theorem311Source.S1354C3LDonorRestructureActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorCompletionActual
open LeanFormal.IUT.Theorem311Source.S1338C3LDonorFieldsActual
open LeanFormal.IUT.XiFPaper.S1314C3GaloisRootActionActual
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
structure C3LDonor (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  q : FinitePlaceQCandidate place.val
  thetaPacket : FiniteThetaPacket l
  lFields : ConcreteC3DonorLFields (I := I) place
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
attribute [instance] C3LDonor.hp C3LDonor.tensorFintype
noncomputable def actualC3LDonor : C3LDonor I place where
  p := p
  hp := inferInstance
  place := place
  q := concreteQCandidate (I := I) place
  thetaPacket := concreteThetaPacket (I := I)
  lFields := actualConcreteC3DonorLFields (I := I) place
  tensorIndex := ConcreteTensorIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcreteTensorPlaceIndex
  tensorPlaces := concreteTensorPlaces (I := I) place
  tensorTuple := concreteTensorTuple
  tensorUnit := concreteTensorUnit (I := I) place
theorem actualC3LDonor_roots_eq :
    (actualC3LDonor I place).lFields.roots =
      concreteRootsAlgebraicClosure (I := I) place :=
  rfl
theorem actualC3LDonor_rootChange_eq
    (σ : ConcreteQAlgebraicClosure (I := I) place ≃ₐ[
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place]
      ConcreteQAlgebraicClosure (I := I) place) :
    (actualC3LDonor I place).lFields.rootChange σ =
      actualC3RootChange (I := I) place σ :=
  rfl
/-- Exact obstruction: the old completion-valued SourcePilotRegionData roots
carrier is NatRootSystem of a completion unit, while the actual L-side donor
carrier is NatRootSystem of an algebraic-closure unit.  No adapter is asserted. -/
def completionValuedRootsObstruction : Prop :=
  Nonempty (NatRootSystem (concreteC3QUnit (I := I) place))
end LeanFormal.IUT.Theorem311Source.S1354C3LDonorRestructureActual
