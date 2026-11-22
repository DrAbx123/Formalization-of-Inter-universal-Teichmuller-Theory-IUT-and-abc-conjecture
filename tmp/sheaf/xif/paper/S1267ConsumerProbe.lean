import tmp.sheaf.xif.paper.S1267DonorFixProbe
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem

/-!
# Concrete C3 roots / root change / tensor landing

The concrete C3 fields supply the actual place, q candidate and q unit

  qUnit : (CommonPrimeCompletion K place)^x.

The completion K is not algebraically closed, so the exact NatRootSystem qUnit
carrier (roots living in K-units) is not constructed by the concrete source.
What is actual is the algebraic-closure root system: map qUnit into
AlgebraicClosure K and build the compatible n-th root system there using the
actual factorial-chain construction AlgebraicClosureRootSystem.rootSystemOfAlgClosed.

This file constructs that actual algebraic-closure root system (roots and
roots'), and records the exact completion-root obstruction and the exact tensor
landing obstruction.  No root or tensor landing is fabricated in K.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1267ConsumerProbe

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The actual q unit of the concrete C3 fields. -/
noncomputable def concreteC3QUnit :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ :=
  (concreteC3ActualFields (I := I) place).qUnit

/-- The actual algebraic closure of the completion at the concrete place. -/
abbrev ConcreteQAlgebraicClosure : Type :=
  AlgebraicClosure (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)

/-- The actual q unit after mapping to the algebraic closure. -/
noncomputable def concreteQUnitAlgebraicClosure :
    (ConcreteQAlgebraicClosure (I := I) place)ˣ :=
  Units.map
    (algebraMap (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
      (ConcreteQAlgebraicClosure (I := I) place)).toMonoidHom
    (concreteC3QUnit (I := I) place)

/-- Actual compatible root system of the q unit in the algebraic closure. -/
noncomputable def concreteRootsAlgebraicClosure :
    NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place) :=
  AlgebraicClosureRootSystem.rootSystemOfAlgClosed
    (concreteQUnitAlgebraicClosure (I := I) place)

/-- A second actual root system, obtained by the same algebraic-closure
construction; it is an actual NatRootSystem of the same algebraic-closure unit. -/
noncomputable def concreteRootsPrimeAlgebraicClosure :
    NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place) :=
  AlgebraicClosureRootSystem.rootSystemOfAlgClosed
    (concreteQUnitAlgebraicClosure (I := I) place)

/-- The actual roots in the algebraic closure satisfy the power law. -/
theorem concreteRootsAlgebraicClosure_pow (n : Nat) (hn : n ≠ 0) :
    (concreteRootsAlgebraicClosure (I := I) place).root n ^ n =
      concreteQUnitAlgebraicClosure (I := I) place :=
  NatRootSystem.pow_self
    (concreteRootsAlgebraicClosure (I := I) place) n hn

/-- Exact obstruction: a NatRootSystem in the completion itself is not supplied
by the concrete C3 fields.  The completion is not algebraically closed, and no
compatible root family in completion units is constructed. -/
def ConcreteCompletionRootObstruction : Prop :=
  Nonempty (NatRootSystem (concreteC3QUnit (I := I) place))

/-- The root obstruction is exactly the missing completion-unit root system. -/
theorem concreteCompletionRootObstruction_iff :
    ConcreteCompletionRootObstruction (I := I) place ↔
      Nonempty (NatRootSystem (concreteC3QUnit (I := I) place)) :=
  Iff.rfl

/-- Exact tensor-landing data required by SourcePilotRegionData.  The concrete
C3 fields supply no finite tensor index, tensor places, tensor unit or landing
map, so this is the exact missing structure, not a fabricated landing. -/
structure ConcreteTensorLandingData where
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex → Type
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place →
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding
    ((concreteC3ActualFields (I := I) place).q.q :
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

/-- Exact obstruction for the concrete tensor landing. -/
def ConcreteTensorLandingObstruction : Prop :=
  Nonempty (ConcreteTensorLandingData (I := I) place)

/-- The tensor obstruction is exactly the missing concrete landing datum. -/
theorem concreteTensorLandingObstruction_iff :
    ConcreteTensorLandingObstruction (I := I) place ↔
      Nonempty (ConcreteTensorLandingData (I := I) place) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S1267ConsumerProbe

end