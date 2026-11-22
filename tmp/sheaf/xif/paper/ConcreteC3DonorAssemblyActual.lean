import tmp.sheaf.xif.paper.ConcreteC3RootCompletionActual
import tmp.sheaf.xif.paper.ConcreteC3DonorCompletionActual
import tmp.sheaf.n8.closure.C3Actual

/-!
# Assembly of the concrete C3 donor fields

This file assembles the actual constructible part of
SourcePilotRegionDonors from

* ConcreteC3DonorActual: p, place, q, qUnit, thetaPacket;
* ConcreteC3RootCompletionActual: roots, roots' and rootChange in the
  algebraic closure of the concrete completion;
* ConcreteC3DonorCompletionActual: tensorIndex, tensorPlaces, tensorTuple,
  tensorUnit (the actual tensor block of the concrete finite-place data).

The completion-root systems, the Kummer class tower and the tensor landing map
are not supplied by the concrete source.  They are recorded as exact obstruction
propositions and as explicit fields of the conditional full assembly; no root in
the completion and no tensor landing is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.Theorem311Source.ConcreteC3DonorAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootCompletionActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorCompletionActual

universe upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Actual constructible part of the C3 donor fields. -/
structure ConcreteC3DonorAssemblyActual where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  q : FinitePlaceQCandidate place.val
  q_eq : q = Classical.choice (finitePlaceQCandidate_nonempty place.val)
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  qUnit_eq : qUnit = candidateUnits (K := I.initial.arithmetic.Fmod) place q
  thetaPacket : FiniteThetaPacket l
  qUnitAlgClosure : (ConcreteQAlgebraicClosure (I := I) place)ˣ
  qUnitAlgClosure_eq : qUnitAlgClosure = Units.map
    (algebraMap (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
      (ConcreteQAlgebraicClosure (I := I) place)).toMonoidHom qUnit
  rootsAlgClosure : NatRootSystem
    (concreteQUnitAlgebraicClosure (I := I) place)
  rootsAlgClosure_eq : rootsAlgClosure =
    concreteRootsAlgebraicClosure (I := I) place
  rootsPrimeAlgClosure : NatRootSystem
    (concreteQUnitAlgebraicClosure (I := I) place)
  rootsPrimeAlgClosure_eq : rootsPrimeAlgClosure =
    concreteRootsPrimeAlgebraicClosure (I := I) place
  rootChangeAlgClosure : CyclotomicTower
    (ConcreteQAlgebraicClosure (I := I) place)
  rootChangeAlgClosure_eq : rootChangeAlgClosure =
    KummerClass.rootSystemDiff rootsAlgClosure rootsPrimeAlgClosure
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ

attribute [instance] ConcreteC3DonorAssemblyActual.hp

/-- Actual assembly from the concrete donor, root-completion and tensor data. -/
noncomputable def actualConcreteC3DonorAssembly :
    ConcreteC3DonorAssemblyActual (I := I) where
  p := p
  hp := inferInstance
  place := place
  q := concreteQCandidate (I := I) place
  q_eq := rfl
  qUnit := concreteQUnit (I := I) place
  qUnit_eq := rfl
  thetaPacket := concreteThetaPacket (I := I)
  qUnitAlgClosure := concreteQUnitAlgebraicClosure (I := I) place
  qUnitAlgClosure_eq := rfl
  rootsAlgClosure := concreteRootsAlgebraicClosure (I := I) place
  rootsAlgClosure_eq := rfl
  rootsPrimeAlgClosure := concreteRootsPrimeAlgebraicClosure (I := I) place
  rootsPrimeAlgClosure_eq := rfl
  rootChangeAlgClosure := KummerClass.rootSystemDiff
    (concreteRootsAlgebraicClosure (I := I) place)
    (concreteRootsPrimeAlgebraicClosure (I := I) place)
  rootChangeAlgClosure_eq := rfl
  tensorIndex := ConcreteTensorIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcreteTensorPlaceIndex
  tensorPlaces := concreteTensorPlaces (I := I) place
  tensorTuple := concreteTensorTuple
  tensorUnit := concreteTensorUnit (I := I) place

/-- Exact completion-root obstruction for the first root system. -/
def rootsCompletionObstruction : Prop :=
  Nonempty (NatRootSystem (concreteQUnit (I := I) place))

/-- Exact completion-root obstruction for the second root system. -/
def rootsPrimeCompletionObstruction : Prop :=
  Nonempty (NatRootSystem (concreteQUnit (I := I) place))

/-- Exact tensor-landing obstruction: the concrete donor has no completion to
tensor-block landing taking q to the tensor unit. -/
def tensorLandingObstruction : Prop :=
  Nonempty (ConcreteTensorLandingTarget (I := I) place)

/-- Exact remaining fields needed to produce a full SourcePilotRegionDonors from
the actual assembly. -/
structure ConcreteC3DonorMissingFields
    (A : ConcreteC3DonorAssemblyActual (I := I)) where
  roots : NatRootSystem A.qUnit
  roots' : NatRootSystem A.qUnit
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) A.place)
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) A.place)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
  tensorLanding : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) A.place →
    ArithmeticTensorTupleBlock A.tensorPlaces A.tensorTuple
  tensorLanding_q : tensorLanding
    (A.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) A.place) =
    (A.tensorUnit : ArithmeticTensorTupleBlock A.tensorPlaces A.tensorTuple)

/-- The actual assembly's p is the supplied concrete prime. -/
theorem actualConcreteC3DonorAssembly_p :
    (actualConcreteC3DonorAssembly (I := I) place).p = p := rfl

/-- The actual assembly's q unit is the concrete completion q unit. -/
theorem actualConcreteC3DonorAssembly_qUnit :
    (actualConcreteC3DonorAssembly (I := I) place).qUnit =
      concreteQUnit (I := I) place := rfl

/-- The actual assembly's algebraic-closure roots are the concrete roots. -/
theorem actualConcreteC3DonorAssembly_roots :
    (actualConcreteC3DonorAssembly (I := I) place).rootsAlgClosure =
      concreteRootsAlgebraicClosure (I := I) place := rfl

/-- The actual assembly's tensor unit is the concrete tensor unit. -/
theorem actualConcreteC3DonorAssembly_tensorUnit :
    (actualConcreteC3DonorAssembly (I := I) place).tensorUnit =
      concreteTensorUnit (I := I) place := rfl

end LeanFormal.IUT.Theorem311Source.ConcreteC3DonorAssemblyActual

end