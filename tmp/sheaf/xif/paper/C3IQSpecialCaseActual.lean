import tmp.sheaf.xif.paper.C3IQCoordinateEquivalenceActual
import tmp.sheaf.xif.paper.C3IQActualPacketGapActual

/-!
# C3/IQ special case: K = Qp and unique tensor index

Assume the C3 tensor index is a singleton and every C3 local completion has
`ℚ_[p]`-dimension one.  Then the actual C3 tensor block is one-dimensional over
`ℚ_[p]`, and the canonical source function space with `K = ℚ_[p]` is also
one-dimensional over `ℚ_[p]`.  Using the S344 product-basis coordinates, this
file constructs the actual ℚ-linear equivalence
`C3LogShellTensorBlock C3 ≃ₗ[ℚ] ((i : C3.tensorIndex) → ℚ_[C3.p])`
and proves the actual region/IQ-span image law.

For arbitrary K the same equivalence is not constructed; the exact missing
object is imported from `C3IQActualPacketGapActual`.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.C3IQSpecialCaseActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3IQCoordinateEquivalenceActual
open LeanFormal.IUT.XiFPaper.C3IQActualPacketGapActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Special-case actual ℚ_[p]-linear equivalence between the C3 tensor block
and the canonical `K = ℚ_[p]` function space. -/
noncomputable def c3BlockEquivQp [Unique C3.tensorIndex]
    (hfin : ∀ i : C3.tensorIndex,
      Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) = 1) :
    C3LogShellTensorBlock C3 ≃ₗ[ℚ_[C3.p]]
      ((i : C3.tensorIndex) → ℚ_[C3.p]) := by
  letI : ∀ i : C3.tensorIndex,
      Unique (Fin (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))) := by
    intro i
    rw [hfin i]
    infer_instance
  letI : Unique (FinitePadicTensorIndex (p := C3.p)
      (fun i : C3.tensorIndex => C3LogShellFiber C3 i)) := Pi.unique
  exact (c3LogShellTensorCoordinates C3).trans
    ((LinearEquiv.funUnique (FinitePadicTensorIndex (p := C3.p)
        (fun i : C3.tensorIndex => C3LogShellFiber C3 i)) ℚ_[C3.p] ℚ_[C3.p]).trans
      (LinearEquiv.funUnique C3.tensorIndex ℚ_[C3.p] ℚ_[C3.p]).symm)

/-- The special-case equivalence as a ℚ-linear equivalence. -/
noncomputable def c3BlockEquivQpRat [Unique C3.tensorIndex]
    (hfin : ∀ i : C3.tensorIndex,
      Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) = 1) :
    C3LogShellTensorBlock C3 ≃ₗ[ℚ]
      ((i : C3.tensorIndex) → ℚ_[C3.p]) :=
  (c3BlockEquivQp C3 hfin).restrictScalars ℚ

/-- The actual IQ span maps to the ℚ-span of the coordinate region under the
special-case equivalence. -/
theorem c3BlockEquivQpRat_iq_span [Unique C3.tensorIndex]
    (hfin : ∀ i : C3.tensorIndex,
      Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i) = 1) :
    Submodule.map (c3BlockEquivQpRat C3 hfin).toLinearMap
        (actualC3LogShellTensorIQ C3) =
      Submodule.span ℚ
        (c3BlockEquivQpRat C3 hfin '' actualC3LogShellTensorRegion C3) := by
  unfold actualC3LogShellTensorIQ
  exact Submodule.map_span (c3BlockEquivQpRat C3 hfin).toLinearMap _

/-- For an arbitrary source family K, only the exact missing equivalence is
recorded; no arbitrary-field isomorphism is fabricated. -/
def GeneralSourceKExactMissing
    (D : C3.tensorIndex → SourceLogShellDatum) : Prop :=
  C3IQActualLinearEquivalenceRequired C3 D

end LeanFormal.IUT.XiFPaper.C3IQSpecialCaseActual
end
