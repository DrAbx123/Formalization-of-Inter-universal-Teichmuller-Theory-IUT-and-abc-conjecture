import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import tmp.sheaf.n8.closure.C3Actual

/-!
# S1408: L-side source pilot consumer bridge

S1391 supplies the actual L-carrier SourcePilotRegionDataL for the concrete
C3 place, together with the exact old completion root block

  CompletionRootBlock (sourcePilotRegionLToCore D).

This file plugs that L-side pilot into the two frozen completion-valued C3
consumers without constructing a completion root:

* the C3 donor consumer C3Actual.SourcePilotRegionDonors;
* the old source-clause consumer SourcePilotRegionData (the C3 source pilot
  record itself, and hence every downstream consumer of that record).

The L pilot supplies every donor/source-clause field literally: p, place, q,
thetaPacket, the completion q unit, and the whole tensor block.  The only data
not carried by the L pilot is the old completion root/Kummer block, which is
exactly S1391's CompletionRootBlock.  The block is passed as an explicit
input; it is never inhabited here.

The exact mismatch theorem is

  OldSourcePilotWithActualCore  <->  Nonempty (CompletionRootBlock at the L core)
                                <->  Nonempty (NatRootSystem (concreteQUnit ...)).

Thus the L pilot feeds all completion-valued consumers exactly when the old
completion first field is supplied, and the first field is exactly the missing
carrier.  No completion root, no map between the L and completion root-system
carriers, and no old completion-valued record is constructed unconditionally.

The generic consumer definitions below accept any downstream consumer function
of the donor/source-clause records, so the bridge is not tied to one consumer.

No sorry, admit, axiom, arbitrary data, or completion root is used.
-/

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1408C3LSourcePilotConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-! ## 1. The exact old completion block of the L pilot -/

/-- The exact old completion root/Kummer block at the common core of the L
pilot.  This is literally S1391's CompletionRootBlock at
sourcePilotRegionLToCore D; it is an input, not an inhabitant. -/
abbrev SourcePilotOldCompletionBlock (D : SourcePilotRegionDataL (I := I)) : Type :=
  CompletionRootBlock (I := I) (sourcePilotRegionLToCore (I := I) D)

/-- The old block exists exactly when the L pilot's completion q unit has a
root system.  This is S1391's exact first-field equivalence at the L core. -/
theorem sourcePilotOldCompletionBlock_nonempty_iff
    (D : SourcePilotRegionDataL (I := I)) :
    Nonempty (SourcePilotOldCompletionBlock (I := I) D) ↔
      Nonempty (NatRootSystem D.qUnit) :=
  completionRootBlock_nonempty_iff (I := I) (sourcePilotRegionLToCore (I := I) D)

/-- At the actual L pilot the exact old block is nonempty exactly when the
concrete completion first field is.  No such root system is constructed. -/
theorem actualSourcePilotOldCompletionBlock_nonempty_iff :
    Nonempty (SourcePilotOldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) ↔
      completionFirstFieldObstruction (I := I) place := by
  rw [sourcePilotOldCompletionBlock_nonempty_iff]
  rfl

/-- The exact first-field type of the old block at the actual L pilot. -/
theorem actualSourcePilotOldCompletionBlock_firstField :
    Nonempty (SourcePilotOldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) ↔
      Nonempty (NatRootSystem (concreteQUnit (I := I) place)) :=
  actualSourcePilotOldCompletionBlock_nonempty_iff (I := I) place

/-! ## 2. Transport of root systems across the L q-unit equation -/

/-- Casting both root systems along the q-unit equation does not change the
Kummer root-system difference.  This is the only transport needed to move the
old block onto the donor's candidateUnits q unit. -/
theorem rootSystemDiff_cast {M : Type*} [CommMonoid M] {u v : Mˣ} (h : u = v)
    (r r' : NatRootSystem u) :
    KummerClass.rootSystemDiff (h ▸ r) (h ▸ r') =
      KummerClass.rootSystemDiff r r' := by
  cases h
  rfl

/-! ## 3. C3 donor consumer: SourcePilotRegionDonors from the L pilot -/

/-- The frozen C3 donor consumer record built from the L pilot and its exact
old completion block.  All non-root fields are the pilot's fields; the roots
are the block's roots transported along the pilot's qUnit_eq; the Kummer
class and root change are the block's completion towers. -/
noncomputable def sourcePilotRegionDonorsOfLBlock
    (D : SourcePilotRegionDataL (I := I))
    (B : SourcePilotOldCompletionBlock (I := I) D) :
    SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I where
  p := D.p
  hp := D.hp
  place := D.place
  q := D.q
  thetaPacket := D.thetaPacket
  roots := D.qUnit_eq ▸ B.roots
  roots' := D.qUnit_eq ▸ B.roots'
  kummerClass := B.kummerClass
  rootChange := B.rootChange
  rootChange_eq := by
    rw [rootSystemDiff_cast, B.rootChange_eq]
    rfl
  tensorIndex := D.tensorIndex
  tensorFintype := D.tensorFintype
  tensorPlaceIndex := D.tensorPlaceIndex
  tensorPlaces := D.tensorPlaces
  tensorTuple := D.tensorTuple
  tensorUnit := D.tensorUnit
  tensorLanding := D.tensorLanding
  tensorLanding_q := D.tensorLanding_q

/-- Apply any C3 donor consumer to the L pilot once the exact old completion
block is supplied.  This is the generic consumer edge, not a new donor. -/
noncomputable def c3DonorConsumerOfLBlock {X : Sort*}
    (f : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I → X)
    (D : SourcePilotRegionDataL (I := I))
    (B : SourcePilotOldCompletionBlock (I := I) D) : X :=
  f (sourcePilotRegionDonorsOfLBlock (I := I) D B)

/-! ## 4. Source-clause consumer: the old SourcePilotRegionData -/

/-- The old completion-valued source-clause consumer record built from the L
pilot and its exact old completion block.  This is the frozen
SourcePilotRegionData, so every downstream consumer of that record is
available on the same input. -/
noncomputable def oldSourcePilotOfLBlock
    (D : SourcePilotRegionDataL (I := I))
    (B : SourcePilotOldCompletionBlock (I := I) D) :
    SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I :=
  sourcePilotRegionDataOfDonors (l := l) (V := FinitePrimePlace 2 7) I
    (sourcePilotRegionDonorsOfLBlock (I := I) D B)

/-- The old source-clause record's common core is the actual L core.  The only
difference between the L record and the reconstructed old record is the old
completion root/Kummer block. -/
theorem oldSourcePilotOfLBlock_core_actual
    (B : SourcePilotOldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    oldSourcePilotToCore (I := I)
        (oldSourcePilotOfLBlock (I := I)
          (actualSourcePilotRegionDataL (I := I) place) B) =
      actualSourcePilotRegionCore (I := I) place := rfl

/-- The reconstructed old record is exactly S1391's core-plus-block assembly at
the actual core. -/
theorem oldSourcePilotOfLBlock_eq_coreAndBlock
    (B : SourcePilotOldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    oldSourcePilotOfLBlock (I := I)
        (actualSourcePilotRegionDataL (I := I) place) B =
      oldSourcePilotOfCoreAndBlock (I := I)
        (actualSourcePilotRegionCore (I := I) place)
        { roots := B.roots
          roots' := B.roots'
          kummerClass := B.kummerClass
          rootChange := B.rootChange
          rootChange_eq := B.rootChange_eq } := by
  cases B
  rfl

/-- The first root field of the reconstructed old record is the block's root
field, not the L root field. -/
theorem oldSourcePilotOfLBlock_roots
    (B : SourcePilotOldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    (oldSourcePilotOfLBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place) B).roots = B.roots := rfl

/-- The old Kummer class of the reconstructed record is the block's completion
tower, not the L Galois-indexed Kummer class. -/
theorem oldSourcePilotOfLBlock_kummerClass
    (B : SourcePilotOldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    (oldSourcePilotOfLBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place) B).kummerClass =
      B.kummerClass := rfl

/-- Apply any old source-clause consumer to the L pilot once the exact old
completion block is supplied. -/
noncomputable def oldSourcePilotConsumerOfLBlock {X : Sort*}
    (f : SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I → X)
    (D : SourcePilotRegionDataL (I := I))
    (B : SourcePilotOldCompletionBlock (I := I) D) : X :=
  f (oldSourcePilotOfLBlock (I := I) D B)

/-! ## 5. Exact old completion mismatch -/

/-- Old source-clause records with the actual core exist exactly when the L
pilot's exact old completion block exists.  This is the precise consumer-level
mismatch: the L pilot is complete on the actual data, and the only old-schema
obstruction is the completion root block. -/
theorem oldSourcePilotWithActualCore_nonempty_iff_LBlock :
    OldSourcePilotWithActualCore (I := I) place ↔
      Nonempty (SourcePilotOldCompletionBlock (I := I)
        (actualSourcePilotRegionDataL (I := I) place)) :=
  (oldSourcePilotWithActualCore_nonempty_iff (I := I) place).trans
    (actualSourcePilotOldCompletionBlock_nonempty_iff (I := I) place).symm

/-- The same exact mismatch in first-field form: old records with the actual
core exist exactly when the concrete completion q unit has a root system. -/
theorem oldSourcePilotWithActualCore_nonempty_iff_completionFirstField :
    OldSourcePilotWithActualCore (I := I) place ↔
      completionFirstFieldObstruction (I := I) place :=
  oldSourcePilotWithActualCore_nonempty_iff (I := I) place

/-- Conditional old source-clause consumer from the L pilot and the exact old
completion block.  This is the consumer entry point; no completion root is
constructed. -/
theorem oldSourcePilotOfLBlock_nonempty
    (B : SourcePilotOldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    Nonempty (SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I) :=
  ⟨oldSourcePilotOfLBlock (I := I)
    (actualSourcePilotRegionDataL (I := I) place) B⟩

/-! ## 6. Axiom check -/

#print axioms sourcePilotRegionDonorsOfLBlock
#print axioms oldSourcePilotOfLBlock
#print axioms oldSourcePilotOfLBlock_core_actual
#print axioms oldSourcePilotWithActualCore_nonempty_iff_LBlock

end LeanFormal.IUT.XiFPaper.S1408C3LSourcePilotConsumerActual

end
