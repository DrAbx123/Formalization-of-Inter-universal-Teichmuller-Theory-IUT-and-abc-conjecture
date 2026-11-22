import tmp.sheaf.xif.paper.S2162NativeSourceActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2171SourceCompletionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2162NativeSourceActual
open LeanFormal.IUT.XiFPaper.S2153NativeTotalizationActual

universe uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The source sign quotient as the first block -/

/-- Exact pointwise source sign quotient above the paper arithmetic root. -/
def S2171SourceSignQuotientRequired
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (SourceSignQuotientData I.initial.arithmetic)

/-- The tree's contract-root sign quotient supply. -/
abbrev S2171ContractRootSignQuotientRequired (l : PrimeGeFive) : Prop :=
  ContractRootSignQuotientSupply.{0} l

/-- Restatement of the tree definition. -/
theorem s2171ContractRootSignQuotient_iff
    (l : PrimeGeFive) :
    S2171ContractRootSignQuotientRequired l ↔
      ∀ S : SourceDefinition31Data.{0} l,
        Nonempty (SourceSignQuotientData S.arithmetic) :=
  Iff.rfl

/-- A SourceCompletion above the paper root supplies the source sign quotient. -/
theorem s2171SourceCompletion_requires_signQuotient
    {I : OriginalInput.{0, uv, upi, umon, ui} l V}
    (C : S2162SourceCompletionRequired I) :
    S2171SourceSignQuotientRequired I :=
  ⟨C.arithmetic_root_eq ▸ C.C.signQuotient.toSourceSignQuotientData⟩

/-- A native source above the paper root supplies the source sign quotient. -/
theorem s2171NativeSource_requires_signQuotient
    {I : OriginalInput.{0, uv, upi, umon, ui} l V}
    (T : S2153NativeSourceRequired I) :
    S2171SourceSignQuotientRequired I :=
  ⟨T.arithmetic_root_eq ▸ T.T.tuple.source⟩

/-! ## 2. Exact source-completion obligation -/

/-- Exact pointwise SourceCompletion obligation above the paper root. -/
abbrev S2171SourceCompletionRequired
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Prop :=
  S2162SourceCompletionRequiredProp I

/-- The source-completion obligation is definitionally the completion
structure's nonemptiness. -/
theorem s2171SourceCompletionRequired_iff
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :
    S2171SourceCompletionRequired I ↔
      Nonempty (S2162SourceCompletionRequired I) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2171SourceCompletionActual
end
