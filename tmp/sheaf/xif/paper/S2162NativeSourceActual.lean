import tmp.sheaf.xif.paper.S2153NativeTotalizationActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2162NativeSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.S2153NativeTotalizationActual
open LeanFormal.IUT.XiFPaper.S2148PaperLineBundleActual

universe uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. SourceCompletion as the exact native source carrier -/

/-- Exact source-completion datum above the paper arithmetic root: the
`SourceCompletion` record already contains fbar, sign quotient, arithmetic
prelude and clauses A-F. -/
structure S2162SourceCompletionRequired
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) where
  C : SourceCompletion.{0} l
  arithmetic_root_eq : C.arithmetic = I.initial.arithmetic

/-- A source completion above the paper root gives the native source. -/
noncomputable def s2162NativeSourceOfCompletion
    {I : OriginalInput.{0, uv, upi, umon, ui} l V}
    (C : S2162SourceCompletionRequired I) :
    S2153NativeSourceRequired I where
  T := C.C.toSourceNativeInitialThetaData
  arithmetic_root_eq :=
    C.C.toSourceNative_arithmetic.trans C.arithmetic_root_eq

/-- A native source gives its source completion. -/
noncomputable def s2162CompletionOfNativeSource
    {I : OriginalInput.{0, uv, upi, umon, ui} l V}
    (T : S2153NativeSourceRequired I) :
    S2162SourceCompletionRequired I where
  C := SourceCompletion.ofSourceNative T.T
  arithmetic_root_eq :=
    (SourceCompletion.ofSourceNative_arithmetic T.T).trans T.arithmetic_root_eq

/-- Exact equivalence: the native source is exactly a source completion above
the paper arithmetic root. -/
theorem s2162NativeSourceRequired_iff_completion
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :
    Nonempty (S2153NativeSourceRequired I) ↔
      Nonempty (S2162SourceCompletionRequired I) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨s2162CompletionOfNativeSource T⟩
  · rintro ⟨C⟩
    exact ⟨s2162NativeSourceOfCompletion C⟩

/-! ## 2. Contract-native bridge and pointwise totalization consumers -/

/-- The tree's contract-to-native bridge gives the native source for every paper
input.  No bridge inhabitant is asserted. -/
theorem s2162NativeSource_of_contractBridge
    (hB : ContractNativeRecordBridge.{0} l)
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :
    Nonempty (S2153NativeSourceRequired I) := by
  rcases hB with ⟨Ψ, hΨ⟩
  exact ⟨⟨Ψ I.initial, hΨ I.initial⟩⟩

/-- The pointwise native totalization statement gives the native source for
every paper input. -/
theorem s2162NativeSource_of_pointwiseTotalization
    (h : PointwiseNativeTotalizationOverContractRoots.{0} l)
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :
    Nonempty (S2153NativeSourceRequired I) := by
  rcases h I.initial with ⟨T, hT⟩
  exact ⟨⟨T, hT⟩⟩

/-- The exact first missing of the source completion: a `SourceCompletion`
above the paper arithmetic root. -/
def S2162SourceCompletionRequiredProp
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (S2162SourceCompletionRequired I)

/-- The proposition is definitionally the nonemptiness of the completion
requirement. -/
theorem s2162SourceCompletionRequiredProp_iff
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :
    S2162SourceCompletionRequiredProp I ↔
      Nonempty (S2162SourceCompletionRequired I) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2162NativeSourceActual
end