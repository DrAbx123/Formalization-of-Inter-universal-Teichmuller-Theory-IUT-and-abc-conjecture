import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! Mainline: skeleton APT statement layer (contract-slot identification re-export). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1APTSkeletonStatementActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe uG uG' uG'' uG₂ uv ua upi umon ui uOut₁ uOut₂ uOut₃

variable {l : PrimeGeFive} {V : Type uv}
variable {G₁ : Type uG} [Group G₁] {G₁' : Type uG'} [Group G₁']
variable {G₂ : Type uG₂} [Group G₂]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n n' : Int}
variable {Output₁ : Type uOut₁} {Output₂ : Type uOut₂}
variable {S : SourceOneColumnArithmeticHolomorphicStructure V}
variable {A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁}
variable {A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂}

/-- Skeleton-node statement for APT: inhabitation of the reduced transport record. -/
def SkeletonAPTStatement : Prop :=
  SourceAPTStatement S A A'

theorem skeletonAPTStatement_iff :
    SkeletonAPTStatement (S := S) (A := A) (A' := A') ↔
      Nonempty (SourceAlgorithmicParallelTransport S A A') :=
  Iff.rfl

theorem skeletonAPTStatement_of_transport
    (t : SourceAlgorithmicParallelTransport S A A') :
    SourceAPTStatement S A A' :=
  ⟨t⟩

theorem skeletonAPT_evidence (X : SourceAPTSlotAssembly S A A')
    (h : SourceAPTStatement S A A') : X.contract.apt :=
  aptSlot_evidence X h

end LeanFormal.IUT.XiFPaper.Mzk1APTSkeletonStatementActualAdapted