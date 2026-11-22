import tmp.sheaf.xif.paper.S1354C3LDonorRestructureActual
import tmp.sheaf.xif.paper.S1349C3LDonorRestructureActual

/-!
# S1391: the actual L-carrier SourcePilotRegionData replacement

## What this file does

S1349 supplies the nested L-side restructure SourcePilotRegionLData; S1354
supplies the actual C3LDonor whose root/Kummer block is S1338's actual
algebraic-closure block.  This file flattens the L-side data into a complete
L-carrier replacement for the old completion-valued schema (the shared core is
field-for-field; the root/Kummer block is the actual Galois-indexed block),
ties it to both actual donors, and records the exact first-field/carrier
mismatch.

The old schema SourcePilotRegionData has first field

  roots : NatRootSystem qUnit

where qUnit is a unit of the completion K.  The L replacement has first field

  roots : NatRootSystem (concreteQUnitAlgebraicClosure I place)

over the algebraic closure L.  The two carriers are recorded exactly; no
completion root, no map between the root-system carriers, and no unconditional
old completion-valued SourcePilotRegionData is constructed.  The conditional
old-schema constructor from an explicit completion root block is recorded
below for the exact mismatch.

## Replacement semantics

SourcePilotRegionCore is the common core of the old and L records: p, place,
q, thetaPacket, the completion q unit and the whole tensor landing block.  Both
SourcePilotRegionData and SourcePilotRegionDataL project to this core, and the
actual L record's core is the actual concrete core.

The old record is exactly core + CompletionRootBlock: the block is the four
completion-valued root/Kummer fields.  The L record is exactly the same core
with the four fields moved to L.  Thus the L record is a complete replacement
on the actual data, while the old completion block remains the exact first-field
gap and is not fabricated.

The L carrier is specialized to the actual concrete q unit selected by
concreteQCandidate, the unit used by S1338/S1314.  It is not a generic-q schema;
a generic-q version would have to carry the Galois action as data and is not
fabricated here.

No sorry, admit, axiom, arbitrary data, or completion root is used.
-/

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootCompletionActual
open LeanFormal.IUT.XiFPaper.S1314C3GaloisRootActionActual
open LeanFormal.IUT.Theorem311Source.S1338C3LDonorFieldsActual
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.XiFPaper.S1267TensorUnitActual
open LeanFormal.IUT.XiFPaper.S1349C3LDonorRestructureActual
open LeanFormal.IUT.Theorem311Source.S1354C3LDonorRestructureActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The Galois group Gal(L/K) of the algebraic closure of the completion over
the completion, in the exact form used by the S1314 actual action. -/
abbrev C3LGalois
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) : Type :=
  ConcreteQAlgebraicClosure (I := I) place ≃ₐ[
    CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place]
    ConcreteQAlgebraicClosure (I := I) place

/-! ## 1. The common core of the old and L-side records -/

/-- The fields shared literally by the old completion schema and the L
replacement: prime, place, actual q, theta packet, completion q unit, and the
whole tensor landing block.  The root/Kummer carrier is deliberately outside
the core. -/
structure SourcePilotRegionCore
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  q : FinitePlaceQCandidate place.val
  thetaPacket : FiniteThetaPacket l
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  qUnit_eq : qUnit = candidateUnits (K := I.initial.arithmetic.Fmod) place q
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

attribute [instance] SourcePilotRegionCore.hp
attribute [instance] SourcePilotRegionCore.tensorFintype

/-- The core of the old completion-valued SourcePilotRegionData. -/
noncomputable def oldSourcePilotToCore
    (D : SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I) :
    SourcePilotRegionCore (I := I) where
  p := D.p
  hp := D.hp
  place := D.place
  q := D.q
  thetaPacket := D.thetaPacket
  qUnit := D.qUnit
  qUnit_eq := D.qUnit_eq
  tensorIndex := D.tensorIndex
  tensorFintype := D.tensorFintype
  tensorPlaceIndex := D.tensorPlaceIndex
  tensorPlaces := D.tensorPlaces
  tensorTuple := D.tensorTuple
  tensorUnit := D.tensorUnit
  tensorLanding := D.tensorLanding
  tensorLanding_q := D.tensorLanding_q

/-- The exact completion-valued root/Kummer block of the old schema.  This is
the only block that the L replacement changes; it is never inhabited here. -/
structure CompletionRootBlock
    (C : SourcePilotRegionCore (I := I)) where
  roots : NatRootSystem C.qUnit
  roots' : NatRootSystem C.qUnit
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C.place)
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C.place)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- The old completion block of an old record. -/
noncomputable def oldSourcePilotToCompletionRootBlock
    (D : SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I) :
    CompletionRootBlock (I := I) (oldSourcePilotToCore (I := I) D) where
  roots := D.roots
  roots' := D.roots'
  kummerClass := D.kummerClass
  rootChange := D.rootChange
  rootChange_eq := D.rootChange_eq

/-- Reassemble an old record from its core and its completion root block.  This
is the exact old-schema constructor; it is conditional on the completion block. -/
noncomputable def oldSourcePilotOfCoreAndBlock
    (C : SourcePilotRegionCore (I := I)) (B : CompletionRootBlock (I := I) C) :
    SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I where
  p := C.p
  hp := C.hp
  place := C.place
  q := C.q
  thetaPacket := C.thetaPacket
  qUnit := C.qUnit
  qUnit_eq := C.qUnit_eq
  roots := B.roots
  roots' := B.roots'
  kummerClass := B.kummerClass
  rootChange := B.rootChange
  rootChange_eq := B.rootChange_eq
  tensorIndex := C.tensorIndex
  tensorFintype := C.tensorFintype
  tensorPlaceIndex := C.tensorPlaceIndex
  tensorPlaces := C.tensorPlaces
  tensorTuple := C.tensorTuple
  tensorUnit := C.tensorUnit
  tensorLanding := C.tensorLanding
  tensorLanding_q := C.tensorLanding_q

/-- The core of the reassembled old record is exactly the supplied core. -/
theorem oldSourcePilotToCore_ofCoreAndBlock
    (C : SourcePilotRegionCore (I := I)) (B : CompletionRootBlock (I := I) C) :
    oldSourcePilotToCore (I := I) (oldSourcePilotOfCoreAndBlock (I := I) C B) = C := rfl

/-- The completion block of the reassembled old record is exactly the supplied
block. -/
theorem oldSourcePilotToCompletionRootBlock_ofCoreAndBlock
    (C : SourcePilotRegionCore (I := I)) (B : CompletionRootBlock (I := I) C) :
    oldSourcePilotToCompletionRootBlock (I := I)
      (oldSourcePilotOfCoreAndBlock (I := I) C B) = B := rfl

/-- Every old record is exactly its core plus its completion root block. -/
theorem oldSourcePilotOfCoreAndBlock_toCore_toBlock
    (D : SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I) :
    oldSourcePilotOfCoreAndBlock (I := I)
      (oldSourcePilotToCore (I := I) D)
      (oldSourcePilotToCompletionRootBlock (I := I) D) = D := by
  cases D
  rfl

/-- A completion root system alone fills the whole completion root block: the
second root system can be the same, the Kummer class can be the trivial tower,
and the root change is the definitional root-system difference.  This is the
exact equivalence between the old block and its first field; no completion root
is constructed. -/
theorem completionRootBlock_nonempty_iff
    (C : SourcePilotRegionCore (I := I)) :
    Nonempty (CompletionRootBlock (I := I) C) ↔
      Nonempty (NatRootSystem C.qUnit) := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.roots⟩
  · rintro ⟨r⟩
    exact ⟨{
      roots := r
      roots' := r
      kummerClass := CyclotomicTower.one
      rootChange := KummerClass.rootSystemDiff r r
      rootChange_eq := rfl }⟩

/-! ## 2. The flat L-carrier replacement -/

/-- Complete L-carrier replacement for SourcePilotRegionData.  The first seven
and the last eight fields are literally the old schema's fields.  The
root/Kummer block uses the algebraic closure L and the actual S1314
Galois-indexed Kummer class/root change; it replaces the old single completion
towers.  qUnitAlgClosure_eq records that the L carrier is the image of the
completion q unit, so the replacement is not a free-floating carrier. -/
structure SourcePilotRegionDataL
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
  q : FinitePlaceQCandidate place.val
  thetaPacket : FiniteThetaPacket l
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  qUnit_eq : qUnit = candidateUnits (K := I.initial.arithmetic.Fmod) place q
  /-- The L carrier is the actual concrete algebraic-closure q unit. -/
  qUnitAlgClosure_eq :
    concreteQUnitAlgebraicClosure (I := I) place =
      Units.map
        (algebraMap (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
          (ConcreteQAlgebraicClosure (I := I) place)).toMonoidHom qUnit
  roots : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)
  roots' : NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)
  kummerClass : C3LGalois I place →
    CyclotomicTower (ConcreteQAlgebraicClosure (I := I) place)
  rootChange : C3LGalois I place →
    CyclotomicTower (ConcreteQAlgebraicClosure (I := I) place)
  kummerClass_eq_rootChange : ∀ σ, kummerClass σ = rootChange σ
  rootChange_eq : ∀ σ, rootChange σ =
    KummerClass.rootSystemDiff roots (galoisRootsAction I place σ roots)
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

attribute [instance] SourcePilotRegionDataL.hp
attribute [instance] SourcePilotRegionDataL.tensorFintype

/-- The common core of the L record. -/
noncomputable def sourcePilotRegionLToCore
    (D : SourcePilotRegionDataL (I := I)) :
    SourcePilotRegionCore (I := I) where
  p := D.p
  hp := D.hp
  place := D.place
  q := D.q
  thetaPacket := D.thetaPacket
  qUnit := D.qUnit
  qUnit_eq := D.qUnit_eq
  tensorIndex := D.tensorIndex
  tensorFintype := D.tensorFintype
  tensorPlaceIndex := D.tensorPlaceIndex
  tensorPlaces := D.tensorPlaces
  tensorTuple := D.tensorTuple
  tensorUnit := D.tensorUnit
  tensorLanding := D.tensorLanding
  tensorLanding_q := D.tensorLanding_q

/-! ## 3. The actual L-side data -/

/-- The actual common core: concrete q candidate, theta packet, completion q
unit and the actual diagonal tensor landing. -/
noncomputable def actualSourcePilotRegionCore :
    SourcePilotRegionCore (I := I) where
  p := p
  hp := inferInstance
  place := place
  q := concreteQCandidate (I := I) place
  thetaPacket := concreteThetaPacket (I := I)
  qUnit := concreteQUnit (I := I) place
  qUnit_eq := rfl
  tensorIndex := ConcreteIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcretePlaceIndex
  tensorPlaces := concretePlaces (I := I) place
  tensorTuple := concreteTuple
  tensorUnit := concreteActualTensorUnit (I := I) place
  tensorLanding := concreteTensorLanding (I := I) place
  tensorLanding_q := rfl

/-- The actual complete L-carrier replacement.  Its root/Kummer block is
S1338/S1314's actual algebraic-closure block, its tensor block is S1219/S1267's
actual diagonal unit and landing, and its core is the actual concrete core. -/
noncomputable def actualSourcePilotRegionDataL :
    SourcePilotRegionDataL (I := I) where
  p := p
  hp := inferInstance
  place := place
  q := concreteQCandidate (I := I) place
  thetaPacket := concreteThetaPacket (I := I)
  qUnit := concreteQUnit (I := I) place
  qUnit_eq := rfl
  qUnitAlgClosure_eq := rfl
  roots := concreteRootsAlgebraicClosure (I := I) place
  roots' := concreteRootsPrimeAlgebraicClosure (I := I) place
  kummerClass := actualC3KummerClass (I := I) place
  rootChange := actualC3RootChange (I := I) place
  kummerClass_eq_rootChange := fun σ =>
    actualC3KummerClass_eq_rootChange (I := I) place σ
  rootChange_eq := fun σ =>
    actualC3RootChange_eq (I := I) place σ
  tensorIndex := ConcreteIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcretePlaceIndex
  tensorPlaces := concretePlaces (I := I) place
  tensorTuple := concreteTuple
  tensorUnit := concreteActualTensorUnit (I := I) place
  tensorLanding := concreteTensorLanding (I := I) place
  tensorLanding_q := rfl

/-- The actual L record's core is the actual concrete core. -/
theorem actualSourcePilotRegionDataL_toCore :
    sourcePilotRegionLToCore (I := I) (actualSourcePilotRegionDataL (I := I) place) =
      actualSourcePilotRegionCore (I := I) place := rfl

/-- The actual L record's first root field is S1338's actual algebraic-closure
root system. -/
theorem actualSourcePilotRegionDataL_roots :
    (actualSourcePilotRegionDataL (I := I) place).roots =
      (actualC3LDonor (I := I) place).lFields.roots := rfl

/-- The actual L record's second root field is S1338's actual second algebraic-
closure root system. -/
theorem actualSourcePilotRegionDataL_roots' :
    (actualSourcePilotRegionDataL (I := I) place).roots' =
      concreteRootsPrimeAlgebraicClosure (I := I) place := rfl

/-- The same second root field is S1354's C3LDonor lFields.roots'. -/
theorem actualSourcePilotRegionDataL_roots'_eq_donor :
    (actualSourcePilotRegionDataL (I := I) place).roots' =
      (actualC3LDonor (I := I) place).lFields.roots' := rfl

/-- The actual L Kummer class is S1314's actual Kummer class. -/
theorem actualSourcePilotRegionDataL_kummerClass
    (σ : C3LGalois I place) :
    (actualSourcePilotRegionDataL (I := I) place).kummerClass σ =
      actualC3KummerClass (I := I) place σ := rfl

/-- The actual L root change is S1314's actual root change. -/
theorem actualSourcePilotRegionDataL_rootChange
    (σ : C3LGalois I place) :
    (actualSourcePilotRegionDataL (I := I) place).rootChange σ =
      actualC3RootChange (I := I) place σ := rfl

/-- S1354's C3LDonor tensor unit is the unit 1 of the old concrete tensor
donor, not the diagonal q unit.  This is exactly why the complete L record below
uses the S1267/S1349 diagonal unit: the old SourcePilotRegionData q-landing law
requires tensorLanding q = tensorUnit, which the diagonal q unit satisfies and
the unit 1 does not. -/
theorem actualC3LDonor_tensorUnit_val :
    ((actualC3LDonor (I := I) place).tensorUnit :
      ArithmeticTensorTupleBlock
        (actualC3LDonor (I := I) place).tensorPlaces
        (actualC3LDonor (I := I) place).tensorTuple) = 1 := rfl

/-- The actual L tensor unit is the actual diagonal q unit of S1267, also
used by the S1349 actual L record. -/
theorem actualSourcePilotRegionDataL_tensorUnit :
    (actualSourcePilotRegionDataL (I := I) place).tensorUnit =
      (actualSourcePilotRegionLData (I := I) place).tensorUnit := rfl

/-- The actual L tensor landing is the concrete diagonal landing. -/
theorem actualSourcePilotRegionDataL_tensorLanding :
    (actualSourcePilotRegionDataL (I := I) place).tensorLanding =
      concreteTensorLanding (I := I) place := rfl

/-- The L q landing law holds definitionally for the actual data. -/
theorem actualSourcePilotRegionDataL_tensorLanding_q :
    (actualSourcePilotRegionDataL (I := I) place).tensorLanding
        (((actualSourcePilotRegionDataL (I := I) place).q).q :
          CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) =
      ((actualSourcePilotRegionDataL (I := I) place).tensorUnit :
        ArithmeticTensorTupleBlock
          (actualSourcePilotRegionDataL (I := I) place).tensorPlaces
          (actualSourcePilotRegionDataL (I := I) place).tensorTuple) := rfl

/-! ## 4. Exact first field and old completion mismatch -/

/-- The exact first-field type of an old completion-valued record. -/
def OldFirstFieldType
    (D : SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I) : Type :=
  NatRootSystem D.qUnit

/-- The exact first-field type of the old schema. -/
theorem OldFirstFieldType_eq
    (D : SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I) :
    OldFirstFieldType (I := I) D = NatRootSystem D.qUnit := rfl

/-- The exact first-field type of the actual common core: a completion root
system of the concrete q unit. -/
def OldFirstFieldAtCore
    (C : SourcePilotRegionCore (I := I)) : Type :=
  NatRootSystem C.qUnit

/-- The exact first-field type of the L replacement. -/
def LFirstFieldType : Type :=
  NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place)

/-- The two first-field carriers, exactly.  The old field is over the
completion unit concreteQUnit; the L field is over the algebraic-closure unit
concreteQUnitAlgebraicClosure.  This is the recorded carrier mismatch, not a
claim that no completion root system exists. -/
theorem firstFieldCarriers_exact :
    OldFirstFieldAtCore (I := I) (actualSourcePilotRegionCore (I := I) place) =
        NatRootSystem (concreteQUnit (I := I) place) ∧
      LFirstFieldType (I := I) place =
        NatRootSystem (concreteQUnitAlgebraicClosure (I := I) place) :=
  ⟨rfl, rfl⟩

/-- The actual L first field is S1338's actual algebraic-closure root system. -/
theorem LFirstField_actual :
    (actualSourcePilotRegionDataL (I := I) place).roots =
      concreteRootsAlgebraicClosure (I := I) place := rfl

/-- The actual L first-field carrier is inhabited by the actual S1338 roots. -/
theorem LFirstField_nonempty :
    Nonempty (LFirstFieldType (I := I) place) :=
  ⟨concreteRootsAlgebraicClosure (I := I) place⟩

/-- The exact first missing field of the old completion schema: a completion
root system of the concrete q unit.  No inhabitant is constructed. -/
def completionFirstFieldObstruction : Prop :=
  Nonempty (NatRootSystem (concreteQUnit (I := I) place))

/-- The obstruction is exactly the old first field type. -/
theorem completionFirstFieldObstruction_iff :
    completionFirstFieldObstruction (I := I) place ↔
      Nonempty (NatRootSystem (concreteQUnit (I := I) place)) :=
  Iff.rfl

/-- The entire old completion root block is nonempty exactly when the old first
field is; the remaining three fields are derived, not independent. -/
theorem actualCompletionRootBlock_nonempty_iff :
    Nonempty (CompletionRootBlock (I := I)
      (actualSourcePilotRegionCore (I := I) place)) ↔
      completionFirstFieldObstruction (I := I) place := by
  rw [completionRootBlock_nonempty_iff]
  rfl

/-- Conditional old-schema existence: the actual old SourcePilotRegionData
exists as soon as the exact completion root block exists.  This is the precise
remaining gap; the block is not constructed. -/
theorem oldSourcePilotRegionData_nonempty_of_completionRootBlock
    (B : CompletionRootBlock (I := I)
      (actualSourcePilotRegionCore (I := I) place)) :
    Nonempty (SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I) :=
  ⟨oldSourcePilotOfCoreAndBlock (I := I)
    (actualSourcePilotRegionCore (I := I) place) B⟩

/-- Old completion records whose common core is exactly the actual concrete
core.  This is the precise carrier on which the L replacement and the old schema
are comparable field by field. -/
def OldSourcePilotWithActualCore : Prop :=
  Nonempty { D : SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I //
    oldSourcePilotToCore (I := I) D =
      actualSourcePilotRegionCore (I := I) place }

/-- Exact first-field reduction for old records with the actual core: such an
old record exists exactly when the completion first field exists.  The L
replacement supplies every other field, so the only old-schema obstruction is
the completion root carrier. -/
theorem oldSourcePilotWithActualCore_nonempty_iff :
    OldSourcePilotWithActualCore (I := I) place ↔
      completionFirstFieldObstruction (I := I) place := by
  constructor
  · rintro ⟨⟨D, hD⟩⟩
    have hroots :
        NatRootSystem (actualSourcePilotRegionCore (I := I) place).qUnit :=
      hD ▸ D.roots
    exact ⟨hroots⟩
  · intro h
    refine ⟨⟨oldSourcePilotOfCoreAndBlock (I := I)
      (actualSourcePilotRegionCore (I := I) place)
      ((actualCompletionRootBlock_nonempty_iff (I := I) place).mpr h).some, ?_⟩⟩
    rfl

/-- Conditional old-schema existence from the completion first field.  No
completion root is constructed; this is a conditional implication. -/
theorem oldSourcePilotRegionData_nonempty_of_completionRoots
    (h : completionFirstFieldObstruction (I := I) place) :
    Nonempty (SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I) :=
  oldSourcePilotRegionData_nonempty_of_completionRootBlock (I := I) place
    ((actualCompletionRootBlock_nonempty_iff (I := I) place).mpr h).some

/-! ## 5. Axiom check -/

#print axioms actualSourcePilotRegionCore
#print axioms actualSourcePilotRegionDataL
#print axioms firstFieldCarriers_exact
#print axioms oldSourcePilotWithActualCore_nonempty_iff

end LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual

end
