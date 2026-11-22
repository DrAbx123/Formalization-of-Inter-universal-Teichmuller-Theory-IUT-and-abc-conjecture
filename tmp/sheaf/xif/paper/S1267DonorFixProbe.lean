import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-! # Concrete C3 donor actual fields

This file constructs the actual non-tensor C3 fields that are available at a
concrete rational finite place of the source number field:

* the prime p and the actual FinitePlaceAtPrime;
* the actual q candidate from the DVR q-candidate existence theorem;
* the actual theta packet of the source theater.

The root systems (NatRootSystem of the q-unit in the completion), the Kummer
class/root-change towers, and the tensor landing require objects whose types are
not supplied by the concrete source data: roots live in an algebraic closure of
the completion, while candidateUnits lives in the completion itself; tensor
landing is a completion-to-tensor-block map not present in the concrete input.
Those are recorded as exact type Obstruction propositions, not fabricated donors.
No inequality, toy, axiom, or sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua upi umon ui

variable {l : PrimeGeFive}

/-- The concrete finite bad place type used by the concrete input. -/
abbrev ConcretePlaces : Type := FinitePrimePlace 2 7

variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The actual q candidate at the concrete finite place, from the source DVR
q-candidate existence theorem. -/
noncomputable def concreteQCandidate :
    FinitePlaceQCandidate place.val :=
  Classical.choice (finitePlaceQCandidate_nonempty place.val)

/-- The actual q candidate satisfies the q-candidate law. -/
theorem concreteQCandidate_eq :
    concreteQCandidate I place =
      Classical.choice (finitePlaceQCandidate_nonempty place.val) := rfl

/-- The actual theta packet of the concrete source theater. -/
noncomputable def concreteThetaPacket : FiniteThetaPacket l :=
  (I.theaterAt 0 0).thetaPacket

/-- The actual unit in the completion attached to the concrete q candidate. -/
noncomputable def concreteQUnit :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ :=
  candidateUnits (K := I.initial.arithmetic.Fmod) place
    (concreteQCandidate I place)

/-- The root-system carrier type required by SourcePilotRegionDonors.  This is
the exact type of the root system of the actual q unit in the completion; the
concrete source does not supply an element of it. -/
def ConcreteRootSystemCarrier : Type :=
  NatRootSystem (concreteQUnit I place)

/-- Exact root-system obstruction: the required root system type is not
inhabited by the concrete source data. -/
def ConcreteRootSystemObstruction : Prop :=
  Nonempty (ConcreteRootSystemCarrier I place)

/-- The Kummer class tower carrier type over the actual completion. -/
def ConcreteKummerClassCarrier : Type :=
  CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)

/-- Exact Kummer-class obstruction for the concrete donor. -/
def ConcreteKummerClassObstruction : Prop :=
  Nonempty (ConcreteKummerClassCarrier I place)

/-- The root-change tower carrier type. -/
def ConcreteRootChangeCarrier : Type :=
  CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)

/-- Exact root-change obstruction for the concrete donor. -/
def ConcreteRootChangeObstruction : Prop :=
  Nonempty (ConcreteRootChangeCarrier I place)

/-- Actual concrete C3 data that can be constructed: p, place, q candidate, q
unit, and theta packet. -/
structure ConcreteC3ActualFields where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  q : FinitePlaceQCandidate place.val
  q_eq : q = Classical.choice (finitePlaceQCandidate_nonempty place.val)
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  qUnit_eq : qUnit = candidateUnits (K := I.initial.arithmetic.Fmod) place q
  thetaPacket : FiniteThetaPacket l

/-- Actual concrete C3 fields from the concrete source input and finite place. -/
noncomputable def concreteC3ActualFields :
    ConcreteC3ActualFields I where
  p := p
  hp := inferInstance
  place := place
  q := concreteQCandidate I place
  q_eq := rfl
  qUnit := concreteQUnit I place
  qUnit_eq := rfl
  thetaPacket := concreteThetaPacket I

/-- The actual p is the supplied concrete prime. -/
theorem concreteC3ActualFields_p :
    (concreteC3ActualFields I place).p = p := rfl

/-- The actual place is the supplied concrete finite place. -/
theorem concreteC3ActualFields_place :
    (concreteC3ActualFields I place).place = place := rfl

/-- The actual q candidate is the DVR q candidate at that place. -/
theorem concreteC3ActualFields_q :
    (concreteC3ActualFields I place).q =
      Classical.choice (finitePlaceQCandidate_nonempty place.val) := rfl

/-- The actual theta packet is the concrete source theater's packet. -/
theorem concreteC3ActualFields_theta :
    (concreteC3ActualFields I place).thetaPacket =
      (I.theaterAt 0 0).thetaPacket := rfl

end LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual

end