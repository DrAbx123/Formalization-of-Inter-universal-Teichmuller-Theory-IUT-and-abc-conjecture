import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import tmp.sheaf.xif.paper.PrimeStripLogShellActual

/-! # Paper A pure multi-factor carrier

Actual finite capsule model Capsule j = Fin (j+1), with the actual tensor packet
over Capsule j.  This is a pure index/tensor carrier: no root, no conditional
theta image, no qVFam Unit.

The paper-level comparison V ≃ C3.tensorIndex plus place agreement is recorded
as the existing exact missing object PrimeStripC3PlaceComparisonRequired. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.PaperAPureCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual

universe ua uv upi umon ui

variable {l : PrimeGeFive}

/-- The actual multi-factor Capsule j index. -/
abbrev PaperAIndex (j : Nat) : Type := Capsule j

/-- Trivial actual LogShellFamily over the capsule, with factor ℤ. -/
noncomputable def paperATrivialLogShellFamily (j : Nat) :
    LogShellFamily ℤ (fun _ : Unit => Unit) j where
  Shell := fun _ _ _ => ℤ
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

/-- The actual multi-factor tensor packet over Capsule j. -/
abbrev PaperATensorPacket (j : Nat) : Type :=
  TensorPacket (paperATrivialLogShellFamily j) ()

/-- The source capsule cardinality. -/
theorem paperAIndex_card (j : Nat) : Fintype.card (PaperAIndex j) = j + 1 :=
  capsule_card j

/-- The actual pure A-carrier object: capsule index, tensor packet, and factor
cardinality.  It contains no theta/root data. -/
structure PaperACarrierObject (j : Nat) where
  index : Type
  index_eq : index = PaperAIndex j
  [indexFintype : Fintype index]
  packet : Type
  packet_eq : packet = PaperATensorPacket j
  factorCard : Nat
  factorCard_eq : factorCard = j + 1
  capsule_card : Fintype.card (PaperAIndex j) = j + 1

attribute [instance] PaperACarrierObject.indexFintype

/-- The actual pure carrier object. -/
noncomputable def paperACarrierObject (j : Nat) : PaperACarrierObject j where
  index := PaperAIndex j
  index_eq := rfl
  indexFintype := inferInstance
  packet := PaperATensorPacket j
  packet_eq := rfl
  factorCard := j + 1
  factorCard_eq := rfl
  capsule_card := paperAIndex_card j

/-- The carrier has the actual multi-factor index cardinality j+1. -/
theorem paperACarrier_multiFactor (j : Nat) :
    Fintype.card (paperACarrierObject j).index = j + 1 :=
  paperAIndex_card j

/-- Exact missing paper-level index/place comparison: V ≃ C3.tensorIndex with
place agreement.  This is the existing S326 gap, not constructed here. -/
abbrev PaperAC3IndexComparisonGap
    {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (V := V) I) : Prop :=
  PrimeStripC3PlaceComparisonRequired (V := V) (I := I) C3

end LeanFormal.IUT.XiFPaper.PaperAPureCarrierActual

end
