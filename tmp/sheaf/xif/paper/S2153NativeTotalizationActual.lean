import tmp.sheaf.xif.paper.S2148PaperLineBundleActual
import tmp.sheaf.n8.closure.NativeInput
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2153NativeTotalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.S2148PaperLineBundleActual

universe uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The two native components -/

/-- A native initial Theta datum whose arithmetic root is the paper original
input's arithmetic root. -/
structure S2153NativeSourceRequired
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) where
  T : SourceNativeInitialThetaData l
  arithmetic_root_eq : T.arithmetic = I.initial.arithmetic

/-- The actual Hodge-theater lattice component of N8NativeInput: a dependent
family of actual Hodge theaters over the native places, with injective theater
map, links, permutation coherence, and arithmetic alignment. -/
abbrev S2153NativeLatticeRequired
    (T : SourceNativeInitialThetaData l) : Type _ :=
  NativeLattice T

/-- The exact component form of the native totalization: native source above
the paper arithmetic root, plus its actual lattice. -/
structure S2153NativeComponentsRequired
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) where
  source : S2153NativeSourceRequired I
  lattice : S2153NativeLatticeRequired source.T

/-- The native totalization type used by OrigXiFPaperLineBundleData. -/
abbrev S2153NativeTotalization
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Type _ :=
  S2148NativeArithmeticRootData I

/-- Exact first-missing proposition: nonempty native totalization above the
paper arithmetic root. -/
def S2153NativeTotalizationRequired
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (S2153NativeTotalization I)

/-! ## 2. Exact decomposition of the totalization -/

/-- From two components, build the N8NativeInput package. -/
noncomputable def s2153NativeInputOfComponents
    {I : OriginalInput.{0, uv, upi, umon, ui} l V}
    (C : S2153NativeComponentsRequired I) :
    N8NativeInput l where
  S := C.source.T
  lattice := C.lattice

/-- The constructed native input has the required arithmetic root. -/
theorem s2153NativeInputOfComponents_arithmetic
    {I : OriginalInput.{0, uv, upi, umon, ui} l V}
    (C : S2153NativeComponentsRequired I) :
    (s2153NativeInputOfComponents C).S.arithmetic = I.initial.arithmetic :=
  C.source.arithmetic_root_eq

/-- Components give the exact native totalization. -/
noncomputable def s2153NativeTotalizationOfComponents
    {I : OriginalInput.{0, uv, upi, umon, ui} l V}
    (C : S2153NativeComponentsRequired I) :
    S2153NativeTotalization I where
  X := s2153NativeInputOfComponents C
  arithmetic_root_eq := C.source.arithmetic_root_eq

/-- Exact equivalence: the native totalization is exactly a native source above
the paper arithmetic root together with its actual NativeLattice. -/
theorem s2153NativeTotalizationRequired_iff_components
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :
    S2153NativeTotalizationRequired I ↔
      Nonempty (S2153NativeComponentsRequired I) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨{ source := ⟨D.X.S, D.arithmetic_root_eq⟩, lattice := D.X.lattice }⟩
  · rintro ⟨C⟩
    exact ⟨s2153NativeTotalizationOfComponents C⟩

/-- The component form is itself exactly: a native source over the paper root
and a lattice on it. -/
theorem s2153NativeTotalizationRequired_components_explicit
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :
    S2153NativeTotalizationRequired I ↔
      ∃ T : SourceNativeInitialThetaData l,
        T.arithmetic = I.initial.arithmetic ∧ Nonempty (NativeLattice T) := by
  rw [s2153NativeTotalizationRequired_iff_components]
  constructor
  · rintro ⟨C⟩
    exact ⟨C.source.T, C.source.arithmetic_root_eq, ⟨C.lattice⟩⟩
  · rintro ⟨T, hT, ⟨L⟩⟩
    exact ⟨{ source := ⟨T, hT⟩, lattice := L }⟩

end LeanFormal.IUT.XiFPaper.S2153NativeTotalizationActual
end