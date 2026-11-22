import tmp.sheaf.xif.paper.S1338C3LDonorFieldsActual
import tmp.sheaf.xif.paper.ConcreteC3DonorAssemblyActual
import tmp.sheaf.xif.paper.S1267TensorUnitActual
import tmp.sheaf.xif.paper.ConcreteC3RootCompletionActual

/-!
# S1349: L-side C3 donor restructure

S1338 constructs the actual C3 roots, Kummer class and root change on the
paper-faithful algebraic-closure carrier

  L = ConcreteQAlgebraicClosure (I := I) place,

with carrier unit 'concreteQUnitAlgebraicClosure'.  The older completion-valued
record 'ConcreteC3DonorMissingFields' has first field

  roots : NatRootSystem A.qUnit,

where 'A.qUnit' is a unit of the completion K, not of L.  The two carriers are
different, so the S1338 roots cannot be used as that first field.  No completion
root is constructed or fabricated here.

This file supplies the L-side donor restructure.  It consumes exactly S1338's
'roots', 'roots'', 'kummerClass' and 'rootChange' and records the L-side
root-change law in terms of the actual Galois root action.  It also constructs an
L-side 'SourcePilotRegionLData' carrying the actual completion q, theta packet,
tensor landing and tensor unit (the latter from S1267), with the L-side
roots/Kummer/rootChange block.

The old completion-valued first field is kept as the exact type

  S1349OldCompletionFirstField A = NatRootSystem A.qUnit

(via 'ConcreteC3DonorAssemblyActual'), with its obstruction equivalence.  The
L-side first field is the exact type

  S1349LFirstField = NatRootSystem (concreteQUnitAlgebraicClosure ...).

The two carriers are recorded exactly; no map from L-roots to completion roots is
asserted or fabricated.

No sorry, admit, axiom, arbitrary data or completion root is used.
-/

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1349C3LDonorRestructureActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootCompletionActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorAssemblyActual
open LeanFormal.IUT.XiFPaper.S1314C3GaloisRootActionActual
open LeanFormal.IUT.Theorem311Source.S1338C3LDonorFieldsActual
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.XiFPaper.S1267TensorUnitActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

local notation "C3K" =>
  CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place
local notation "C3L" => ConcreteQAlgebraicClosure (I := I) place
local notation "C3Gal" => C3L ≃ₐ[C3K] C3L

/-! ## 1. The L-side missing-field restructure -/

/-- L-side replacement of the root/Kummer fields of
'ConcreteC3DonorMissingFields'.  The carriers are those of S1338:
'NatRootSystem' on the algebraic-closure unit, and the Kummer/root-change towers
indexed by the actual Galois group 'Gal(L/K)'.  The root-change law is the
paper-faithful one: the change is the Kummer difference between the roots and
their actual Galois twist. -/
structure ConcreteC3DonorLMissingFields where
  roots : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)
  roots' : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)
  kummerClass : C3Gal → CyclotomicTower C3L
  rootChange : C3Gal → CyclotomicTower C3L
  kummerClass_eq_rootChange : ∀ σ, kummerClass σ = rootChange σ
  rootChange_eq : ∀ σ,
    rootChange σ =
      KummerClass.rootSystemDiff roots
        (galoisRootsAction I place σ roots)

/-- The actual L-side missing fields, consuming S1338's actual
roots/roots'/kummerClass/rootChange. -/
noncomputable def actualConcreteC3DonorLMissingFields :
    ConcreteC3DonorLMissingFields (I := I) place where
  roots := (actualConcreteC3DonorLFields (I := I) place).roots
  roots' := (actualConcreteC3DonorLFields (I := I) place).roots'
  kummerClass := (actualConcreteC3DonorLFields (I := I) place).kummerClass
  rootChange := (actualConcreteC3DonorLFields (I := I) place).rootChange
  kummerClass_eq_rootChange := fun σ =>
    actualConcreteC3DonorLFields_kummerClass_eq_rootChange
      (I := I) place σ
  rootChange_eq := fun σ =>
    actualConcreteC3DonorLFields_rootChange_eq_diff (I := I) place σ

/-- The actual L roots are exactly the S1338 roots. -/
theorem actualConcreteC3DonorLMissingFields_roots :
    (actualConcreteC3DonorLMissingFields (I := I) place).roots =
      (actualConcreteC3DonorLFields (I := I) place).roots := rfl

/-- The actual L roots' are exactly the S1338 roots'. -/
theorem actualConcreteC3DonorLMissingFields_roots' :
    (actualConcreteC3DonorLMissingFields (I := I) place).roots' =
      (actualConcreteC3DonorLFields (I := I) place).roots' := rfl

/-- The actual L Kummer class is exactly the S1338 Kummer class. -/
theorem actualConcreteC3DonorLMissingFields_kummerClass :
    (actualConcreteC3DonorLMissingFields (I := I) place).kummerClass =
      (actualConcreteC3DonorLFields (I := I) place).kummerClass := rfl

/-- The actual L root change is exactly the S1338 root change. -/
theorem actualConcreteC3DonorLMissingFields_rootChange :
    (actualConcreteC3DonorLMissingFields (I := I) place).rootChange =
      (actualConcreteC3DonorLFields (I := I) place).rootChange := rfl

/-- The L roots satisfy the power law in the algebraic closure. -/
theorem actualConcreteC3DonorLMissingFields_roots_pow
    (n : Nat) (hn : n ≠ 0) :
    (actualConcreteC3DonorLMissingFields (I := I) place).roots.root n ^ n =
      concreteQUnitAlgebraicClosure (I := I) place :=
  NatRootSystem.pow_self
    (actualConcreteC3DonorLMissingFields (I := I) place).roots n hn

/-- The L root change is the Kummer root-system difference between the chosen
roots and their actual Galois twist. -/
theorem actualConcreteC3DonorLMissingFields_rootChange_eq_diff
    (σ : C3Gal) :
    (actualConcreteC3DonorLMissingFields (I := I) place).rootChange σ =
      KummerClass.rootSystemDiff
        (actualConcreteC3DonorLMissingFields (I := I) place).roots
        (galoisRootsAction I place σ
          (actualConcreteC3DonorLMissingFields (I := I) place).roots) :=
  (actualConcreteC3DonorLMissingFields (I := I) place).rootChange_eq σ

/-! ## 2. L-side SourcePilotRegionData restructure -/

/-- L-side restructure of 'SourcePilotRegionData': q, theta and tensor data stay
on their actual carriers, while the four root/Kummer fields are the L-side block
'lFields'.  The completion q unit is tied to the algebraic-closure carrier by
'qUnitAlgClosure_eq'. -/
structure SourcePilotRegionLData
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  q : FinitePlaceQCandidate place.val
  thetaPacket : FiniteThetaPacket l
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  qUnit_eq : qUnit = candidateUnits (K := I.initial.arithmetic.Fmod) place q
  /-- The algebraic-closure carrier is the image of the completion q unit. -/
  qUnitAlgClosure_eq :
    concreteQUnitAlgebraicClosure (I := I) place =
      Units.map
        (algebraMap (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
          (ConcreteQAlgebraicClosure (I := I) place)).toMonoidHom qUnit
  lFields : ConcreteC3DonorLMissingFields (I := I) place
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
    (q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] SourcePilotRegionLData.hp
attribute [instance] SourcePilotRegionLData.tensorFintype

/-- The actual L-side SourcePilotRegionData.  Its L block is S1338's actual
data; its tensor block is the actual diagonal tensor unit and landing. -/
noncomputable def actualSourcePilotRegionLData
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (pl : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    SourcePilotRegionLData (I := I) where
  p := p
  hp := inferInstance
  place := pl
  q := concreteQCandidate I pl
  thetaPacket := concreteThetaPacket I
  qUnit := concreteQUnit I pl
  qUnit_eq := rfl
  qUnitAlgClosure_eq := rfl
  lFields := actualConcreteC3DonorLMissingFields (I := I) pl
  tensorIndex := ConcreteIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcretePlaceIndex
  tensorPlaces := concretePlaces I pl
  tensorTuple := concreteTuple
  tensorUnit := concreteActualTensorUnit I pl
  tensorLanding := concreteTensorLanding I pl
  tensorLanding_q := rfl

/-- The L-side q unit is the concrete completion q unit. -/
theorem actualSourcePilotRegionLData_qUnit :
    (actualSourcePilotRegionLData I place).qUnit =
      concreteQUnit (I := I) place := rfl

/-- The L-side q is the concrete q candidate. -/
theorem actualSourcePilotRegionLData_q :
    (actualSourcePilotRegionLData I place).q =
      concreteQCandidate (I := I) place := rfl

/-- The L-side roots are the S1338 algebraic-closure roots. -/
theorem actualSourcePilotRegionLData_roots :
    (actualSourcePilotRegionLData I place).lFields.roots =
      concreteRootsAlgebraicClosure (I := I) place := rfl

/-- The L-side roots' are the S1338 second algebraic-closure root system. -/
theorem actualSourcePilotRegionLData_roots' :
    (actualSourcePilotRegionLData I place).lFields.roots' =
      concreteRootsPrimeAlgebraicClosure (I := I) place := rfl

/-- The L-side Kummer class is S1338's actual Kummer class. -/
theorem actualSourcePilotRegionLData_kummerClass
    (σ : C3Gal) :
    (actualSourcePilotRegionLData I place).lFields.kummerClass σ =
      actualC3KummerClass I place σ := rfl

/-- The L-side root change is S1338's actual root change. -/
theorem actualSourcePilotRegionLData_rootChange
    (σ : C3Gal) :
    (actualSourcePilotRegionLData I place).lFields.rootChange σ =
      actualC3RootChange I place σ := rfl

/-- The L-side tensor landing is the actual diagonal tensor landing. -/
theorem actualSourcePilotRegionLData_tensorLanding :
    (actualSourcePilotRegionLData I place).tensorLanding =
      concreteTensorLanding I place := rfl

/-- The L-side tensor q landing law is definitional. -/
theorem actualSourcePilotRegionLData_tensorLanding_q :
    (actualSourcePilotRegionLData I place).tensorLanding
        (((actualSourcePilotRegionLData I place).q).q :
          CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) =
      ((actualSourcePilotRegionLData I place).tensorUnit :
        ArithmeticTensorTupleBlock
          (actualSourcePilotRegionLData I place).tensorPlaces
          (actualSourcePilotRegionLData I place).tensorTuple) := rfl

/-! ## 3. Exact first fields: the old completion field and the L-side field -/

/-- The exact first field of the old completion-valued donor
'ConcreteC3DonorMissingFields': a root system in the completion q-unit, with no
algebraic-closure substitution. -/
abbrev S1349OldCompletionFirstField
    {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
    (A : ConcreteC3DonorAssemblyActual (I := I)) : Type :=
  NatRootSystem A.qUnit

/-- Exact type of the old first field. -/
theorem S1349OldCompletionFirstField_eq
    (A : ConcreteC3DonorAssemblyActual (I := I)) :
    S1349OldCompletionFirstField A = NatRootSystem A.qUnit := rfl

/-- At the actual assembly the old first field is exactly the concrete
completion root system. -/
theorem S1349OldCompletionFirstField_actual :
    S1349OldCompletionFirstField
        (actualConcreteC3DonorAssembly (I := I) place) =
      NatRootSystem (concreteQUnit (I := I) place) := rfl

/-- The exact obstruction carried by the old first field. -/
def S1349OldCompletionFirstFieldObstruction
    {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
    (A : ConcreteC3DonorAssemblyActual (I := I)) : Prop :=
  Nonempty (S1349OldCompletionFirstField A)

/-- The obstruction is exactly the existence of a completion root system. -/
theorem S1349OldCompletionFirstFieldObstruction_iff
    (A : ConcreteC3DonorAssemblyActual (I := I)) :
    S1349OldCompletionFirstFieldObstruction A ↔
      Nonempty (NatRootSystem A.qUnit) :=
  Iff.rfl

/-- At the actual assembly the exact obstruction is S1338's
'ConcreteCompletionRootObstruction'. -/
theorem S1349OldCompletionFirstFieldObstruction_actual :
    S1349OldCompletionFirstFieldObstruction
        (actualConcreteC3DonorAssembly (I := I) place) ↔
      ConcreteCompletionRootObstruction (I := I) place :=
  Iff.rfl

/-- The L-side first field: a root system over the algebraic-closure q unit. -/
abbrev S1349LFirstField
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) : Type :=
  NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)

/-- Exact type of the L-side first field. -/
theorem S1349LFirstField_eq :
    S1349LFirstField I place =
      NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place) := rfl

/-- The L-side first field is inhabited by S1338's actual roots. -/
noncomputable def S1349LFirstFieldWitness :
    S1349LFirstField I place :=
  (actualConcreteC3DonorLFields (I := I) place).roots

/-- The old first-field type and the restructured L first-field type are the two
different exact carriers: the old one is 'NatRootSystem A.qUnit' in the
completion, the L one is 'NatRootSystem' of the algebraic-closure unit.  This is
the recorded carrier mismatch; it is not a claim that no completion root system
exists. -/
theorem S1349FirstFieldCarrier_exact :
    S1349OldCompletionFirstField
        (actualConcreteC3DonorAssembly (I := I) place) =
        NatRootSystem (concreteQUnit (I := I) place) ∧
      S1349LFirstField I place =
        NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place) :=
  ⟨rfl, rfl⟩

/-- Any old completion-valued missing-field record still has its exact first
field in the completion; the L-side restructure does not replace it. -/
theorem S1349OldMissingFields_firstField_exact
    (A : ConcreteC3DonorAssemblyActual (I := I))
    (M : ConcreteC3DonorMissingFields (I := I) A) :
    (M.roots : S1349OldCompletionFirstField A) = M.roots := rfl

/-! ## 4. Axiom check for the actual constructions -/

#print axioms actualConcreteC3DonorLMissingFields
#print axioms actualSourcePilotRegionLData
#print axioms S1349OldCompletionFirstFieldObstruction_actual
#print axioms S1349FirstFieldCarrier_exact

end LeanFormal.IUT.XiFPaper.S1349C3LDonorRestructureActual

end
