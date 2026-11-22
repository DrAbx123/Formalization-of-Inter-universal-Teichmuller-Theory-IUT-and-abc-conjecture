import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import tmp.sheaf.xif.paper.S1354C3LDonorRestructureActual
import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.C3T11NamedClosure
import tmp.sheaf.xif.PaperXiFInclusion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace ProbeS1408

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.Theorem311Source.S1354C3LDonorRestructureActual
open LeanFormal.IUT.Theorem311Source.S1338C3LDonorFieldsActual
open LeanFormal.IUT.XiFPaper

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- C3 L-donor consumer of the actual L source pilot. -/
noncomputable def c3LDonorOfPilot : C3LDonor (I := I) place where
  p := p
  hp := inferInstance
  place := place
  q := (actualSourcePilotRegionDataL (I := I) place).q
  thetaPacket := (actualSourcePilotRegionDataL (I := I) place).thetaPacket
  lFields :=
    { qUnitAlgClosure := concreteQUnitAlgebraicClosure (I := I) place
      qUnitAlgClosure_eq := rfl
      roots := (actualSourcePilotRegionDataL (I := I) place).roots
      roots_eq := rfl
      roots' := (actualSourcePilotRegionDataL (I := I) place).roots'
      roots'_eq := rfl
      kummerClass := (actualSourcePilotRegionDataL (I := I) place).kummerClass
      kummerClass_eq := fun σ => rfl
      rootChange := (actualSourcePilotRegionDataL (I := I) place).rootChange
      rootChange_eq := fun σ => rfl }
  tensorIndex := (actualSourcePilotRegionDataL (I := I) place).tensorIndex
  tensorFintype := (actualSourcePilotRegionDataL (I := I) place).tensorFintype
  tensorPlaceIndex := (actualSourcePilotRegionDataL (I := I) place).tensorPlaceIndex
  tensorPlaces := (actualSourcePilotRegionDataL (I := I) place).tensorPlaces
  tensorTuple := (actualSourcePilotRegionDataL (I := I) place).tensorTuple
  tensorUnit := (actualSourcePilotRegionDataL (I := I) place).tensorUnit

theorem c3LDonorOfPilot_lFields :
    (c3LDonorOfPilot (I := I) place).lFields =
      actualConcreteC3DonorLFields (I := I) place := rfl

theorem c3LDonorOfPilot_q :
    (c3LDonorOfPilot (I := I) place).q =
      (actualSourcePilotRegionDataL (I := I) place).q := rfl

/-- Exact old completion block needed to feed completion-valued consumers. -/
structure OldCompletionBlock (D : SourcePilotRegionDataL (I := I)) where
  roots : NatRootSystem D.qUnit
  roots' : NatRootSystem D.qUnit
  kummerClass : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) D.place)
  rootChange : CyclotomicTower
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) D.place)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

theorem rootSystemDiff_cast {M : Type*} [CommMonoid M] {u v : Mˣ} (h : u = v)
    (r r' : NatRootSystem u) :
    KummerClass.rootSystemDiff (h ▸ r) (h ▸ r') =
      h ▸ (KummerClass.rootSystemDiff r r') := by
  cases h
  rfl

theorem cyclotomicTower_cast {M : Type*} [CommMonoid M] {u v : Mˣ} (h : u = v)
    (x : CyclotomicTower M) : h ▸ x = x := by
  cases h
  rfl

theorem oldCompletionBlock_nonempty_iff (D : SourcePilotRegionDataL (I := I)) :
    Nonempty (OldCompletionBlock (I := I) D) ↔
      Nonempty (NatRootSystem D.qUnit) := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.roots⟩
  · rintro ⟨r⟩
    exact ⟨{ roots := r
             roots' := r
             kummerClass := CyclotomicTower.one
             rootChange := KummerClass.rootSystemDiff r r
             rootChange_eq := rfl }⟩

theorem actualOldCompletionBlock_nonempty_iff :
    Nonempty (OldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) ↔
      completionFirstFieldObstruction (I := I) place :=
  Iff.rfl

noncomputable def donorsOfBlock (D : SourcePilotRegionDataL (I := I))
    (B : OldCompletionBlock (I := I) D) :
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
    exact (cyclotomicTower_cast D.qUnit_eq
      (KummerClass.rootSystemDiff B.roots B.roots')).symm
  tensorIndex := D.tensorIndex
  tensorFintype := D.tensorFintype
  tensorPlaceIndex := D.tensorPlaceIndex
  tensorPlaces := D.tensorPlaces
  tensorTuple := D.tensorTuple
  tensorUnit := D.tensorUnit
  tensorLanding := D.tensorLanding
  tensorLanding_q := D.tensorLanding_q

noncomputable def oldRecordOfBlock (D : SourcePilotRegionDataL (I := I))
    (B : OldCompletionBlock (I := I) D) :
    SourcePilotRegionData.{0, 0, upi, umon, ui, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) I :=
  sourcePilotRegionDataOfDonors (l := l) (V := FinitePrimePlace 2 7) I
    (donorsOfBlock (I := I) D B)

theorem oldRecordOfBlock_core_actual
    (B : OldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    oldSourcePilotToCore (I := I)
        (oldRecordOfBlock (I := I) (actualSourcePilotRegionDataL (I := I) place) B) =
      actualSourcePilotRegionCore (I := I) place := rfl

theorem oldRecordOfBlock_roots (D : SourcePilotRegionDataL (I := I))
    (B : OldCompletionBlock (I := I) D) :
    (oldRecordOfBlock (I := I) D B).roots = D.qUnit_eq ▸ B.roots := rfl

theorem actualOldRecordOfBlock_eq_coreAndBlock
    (B : OldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    oldRecordOfBlock (I := I) (actualSourcePilotRegionDataL (I := I) place) B =
      oldSourcePilotOfCoreAndBlock (I := I)
        (actualSourcePilotRegionCore (I := I) place)
        { roots := B.roots
          roots' := B.roots'
          kummerClass := B.kummerClass
          rootChange := B.rootChange
          rootChange_eq := B.rootChange_eq } := by
  cases B
  rfl

/-- Paper q-parameter consumer. -/
theorem paperQParameter_oldRecordOfBlock (D : SourcePilotRegionDataL (I := I))
    (B : OldCompletionBlock (I := I) D) :
    paperQParameter (oldRecordOfBlock (I := I) D B) = ‖D.q.q‖ := rfl

/-- T11 source theta-packet consumer. -/
noncomputable def thetaPacketWitnessOfBlock
    (B : OldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    ABCBridge.N8.T11Reductions.ThetaPacketWitness (I := I) where
  C3 := oldRecordOfBlock (I := I) (actualSourcePilotRegionDataL (I := I) place) B
  thetaPacket_eq := rfl

theorem thetaPacketIdentificationOfBlock
    (B : OldCompletionBlock (I := I)
      (actualSourcePilotRegionDataL (I := I) place)) :
    ABCBridge.N8.T11Native.ThetaPacketIdentification (I := I)
      (oldRecordOfBlock (I := I) (actualSourcePilotRegionDataL (I := I) place) B) :=
  ABCBridge.N8.C3T11NamedClosure.c3T11_thetaPacketIdentification (I := I)
    (thetaPacketWitnessOfBlock (I := I) place B)

#print axioms c3LDonorOfPilot
#print axioms oldRecordOfBlock_core_actual
#print axioms thetaPacketIdentificationOfBlock

end ProbeS1408

end
