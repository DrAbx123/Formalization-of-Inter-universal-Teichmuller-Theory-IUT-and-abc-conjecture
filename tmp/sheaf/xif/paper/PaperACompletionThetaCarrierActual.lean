import tmp.sheaf.n8.closure.NativeBadLiftActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData

/-! # Paper A multi-factor carrier (no theta image)

S342 showed PaperQRootCard is impossible, so the previous conditional theta
image is withdrawn as a paper theta object.  This file keeps only the actual
multi-factor carrier:

* index Capsule j = Fin (j+1);
* packet = tensor over Capsule j of the actual completion.

No root card, no conditional theta image, no qVFam Unit, no inequality. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.PaperACompletionThetaCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

universe u

variable {l : PrimeGeFive}

/-- The actual completion used as the factor type. -/
abbrev PaperACompletion (T : SourceNativeInitialThetaData l)
    (b : Bad (nativePlaceSelection T)) : Type :=
  Completion ((nativeBadLift T).lift b)

/-- The actual multi-factor Capsule j index. -/
abbrev PaperAIndex (j : Nat) : Type := Capsule j

/-- The actual multi-factor paper A tensor carrier over Capsule j. -/
abbrev PaperATensorPacket (T : SourceNativeInitialThetaData l)
    (b : Bad (nativePlaceSelection T)) (j : Nat) : Type :=
  ⨂[ℤ] _i : Capsule j, PaperACompletion (l := l) T b

/-- The multi-factor carrier object: Capsule j index, its actual tensor packet,
and the source capsule cardinality j+1.  No theta image is attached. -/
structure PaperACarrierObject (T : SourceNativeInitialThetaData l)
    (b : Bad (nativePlaceSelection T)) (j : Nat) where
  index : Type
  index_eq : index = Capsule j
  packet : Type
  packet_eq : packet = PaperATensorPacket (l := l) T b j
  factor : Capsule j → Type
  factor_eq : factor = fun _ => PaperACompletion (l := l) T b
  capsule_card : Fintype.card (Capsule j) = j + 1

noncomputable def paperACarrierObject
    (T : SourceNativeInitialThetaData l) (b : Bad (nativePlaceSelection T))
    (j : Nat) : PaperACarrierObject (l := l) T b j where
  index := Capsule j
  index_eq := rfl
  packet := PaperATensorPacket (l := l) T b j
  packet_eq := rfl
  factor := fun _ => PaperACompletion (l := l) T b
  factor_eq := rfl
  capsule_card := capsule_card j

end LeanFormal.IUT.XiFPaper.PaperACompletionThetaCarrierActual

end
