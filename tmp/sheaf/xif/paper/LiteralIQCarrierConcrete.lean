import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.xif.paper.LiteralIQCarrierTypeActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional candidate only: arithmeticIQCarrier is not the literal inductive-system IQ carrier; no literal_IQ_carrier witness is constructed.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Literal IQ carrier concrete attempt: arithmeticIQCarrier vs C6 tensor block

Task-595.  The actual project carrier `arithmeticIQCarrier` is the rational
span of the actual arithmetic log-shell tensor region inside
`ArithmeticPacketTensor places` (all finite completion packets at each
index).  This file builds its concrete data and linear/homeomorphism
identifications, and states exactly why it is not the paper literal
`IQ(S+_{j+1}; n,circ D^vdash_{vQ})` and why no equivalence to the C6
`ArithmeticTensorTupleBlock` is constructed.

## Actual construction

* `ArithmeticIQCarrierCandidate places` = `arithmeticIQCarrier places`
  (actual ℚ-submodule).
* `arithmeticIQEquiv` / `arithmeticIQHomeomorph` are the project's actual
  `ℚ`-linear / topological equivalences to `ArithmeticPacketTensor places`
  under `[Nonempty ι]`.
* `arithmeticTensorLogRegion` compactness and `one_mem` are actual.

## Exact missing / non-faithfulness

`ArithmeticPacketTensor places` is the tensor of full completion packets
`CompletionPacket (places i)`, whereas `ArithmeticTensorTupleBlock
C3.tensorPlaces C3.tensorTuple` is the selected-place tensor block.  No
equivalence between them is in the tree; `arithmeticIQCarrier` is a rational
span local carrier, not the paper's inductive-system IQ carrier with
O-module/prime-strip/procession structure.  Hence it cannot be used as the
literal IQ carrier or as a witness for `literal_IQ_carrier`.

No arbitrary type, `True`, `PUnit`, `sorry`, or axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.PaperIQCarrierActual.LiteralConcrete

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ

universe u v w ua uv upi umon ui

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

/-- Actual candidate: the rational span arithmetic IQ carrier. -/
abbrev ArithmeticIQCarrierCandidate : Type (max u (max v w)) :=
  arithmeticIQCarrier places

theorem arithmeticIQCarrierCandidate_eq :
    ArithmeticIQCarrierCandidate places = arithmeticIQCarrier places := rfl

variable [Nonempty ι]

/-- Actual linear equivalence from the candidate carrier to the packet tensor. -/
def arithmeticIQCarrierCandidateEquiv :
    ArithmeticIQCarrierCandidate places ≃ₗ[ℚ] ArithmeticPacketTensor places :=
  arithmeticIQEquiv places

@[simp] theorem arithmeticIQCarrierCandidateEquiv_apply
    (x : ArithmeticIQCarrierCandidate places) :
    arithmeticIQCarrierCandidateEquiv places x = x.val := rfl

/-- Actual topological equivalence from the candidate carrier to the packet
tensor. -/
def arithmeticIQCarrierCandidateHomeomorph :
    ArithmeticIQCarrierCandidate places ≃ₜ ArithmeticPacketTensor places :=
  arithmeticIQHomeomorph places

@[simp] theorem arithmeticIQCarrierCandidateHomeomorph_apply
    (x : ArithmeticIQCarrierCandidate places) :
    arithmeticIQCarrierCandidateHomeomorph places x = x.val := rfl

theorem arithmeticIQCarrierCandidate_compact_logRegion :
    IsCompact (arithmeticTensorLogRegion places) :=
  isCompact_arithmeticTensorLogRegion places

variable {l : PrimeGeFive} {Vc : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l Vc}
variable (C3 : SourcePilotRegionData (l := l) (V := Vc) I)

/-- Exact candidate comparison to the C6 selected-place tensor block.  It is
a proposition, not a constructed equivalence; the two types differ (full
completion packet tensor vs selected-place tuple block). -/
def ArithmeticIQToC6TensorComparison : Prop :=
  Nonempty (ArithmeticPacketTensor C3.tensorPlaces ≃
    ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)

end LeanFormal.IUT.N8Closure.PaperIQCarrierActual.LiteralConcrete

end
