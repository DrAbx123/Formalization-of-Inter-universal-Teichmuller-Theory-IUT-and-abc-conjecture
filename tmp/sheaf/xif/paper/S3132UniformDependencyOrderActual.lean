import tmp.sheaf.xif.paper.S3132UniformIndexConstructibleActual
import tmp.sheaf.xif.paper.S3132UniformFiberMissingActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3132UniformFactorComparisonComponentActual
open LeanFormal.IUT.XiFPaper.S3132UniformIndexConstructibleActual
open LeanFormal.IUT.XiFPaper.S3132UniformFiberMissingActual

namespace LeanFormal.IUT.XiFPaper.S3132UniformDependencyOrderActual

universe u v uv upi umon ui

/-!
# task-62 (3): dependency order of the uniform HDD/C3 comparison

**Component, not a paper object.**  Owner: hull.  Consumers: task-38's transport/
Theta-half reduction; mainline registry; shehdd gate.

Recorded dependency order (constructible/blocked split):

1. **Index half (constructed up to cardinality):**
   `indexEquiv_of_rank_card` (S3132UniformIndexConstructibleActual) builds
   `Fin D.rank ≃ C3.tensorIndex` from `D.rank = card C3.tensorIndex`; conversely
   any uniform datum gives that cardinality equality
   (`card_eq_of_missingData`, `rank_card_of_missing`).  Paper-faithful index
   data (badplace comparison + all-place place provenance) remains exact
   missing; cardinality alone is numerical and trivializes as in
   `S3132PrimeStripC3AllPlaceComparisonComponent`.
2. **Fiber half (exact missing, type form constructed):**
   `MissingOneColumnC3FiberComparison` (S3132UniformFiberMissingActual) is the
   uniform ring comparison of the one-column rational completions with the C3
   packet fibers; the actual fiber type form is `c3Fiber_eq_actualCompletion`
   (stage4 `lgpC3Fiber_eq_completion`).  Blocked by the contract-missing place
   data; pages III Prop 3.2(ii) pp. 97-99; III Prop 3.7(ii),(v) pp. 108-112.
3. **Uniform datum ⇔ index + fiber:** `missingData_iff_pair`.
4. **Downstream (constructed given the datum):** the actual product transport
   `hddToC3Function` / transported hull `hddToC3Hull` (task-38) and the Theta-half
   reduction `missingThetaHalf_of_transport_and_normalization` (task-30/38); the
   normalization residual `thetaNormalizationFactor` (task-41/61) is independent
   of the transport.

Minimal registerable exact missing: `D.rank = card C3.tensorIndex` **plus** the
paper-faithful index/place choice **plus** `MissingOneColumnC3FiberComparison`;
the fiber half is the irreducible one.
-/

/-- **Equivalence:** the task-38 uniform datum is exactly an index equivalence
together with the minimal exact missing fiber comparison. -/
theorem missingData_iff_pair
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID) :
    MissingC3PacketUniformComparison ID C3 D ↔
      ∃ e : Fin D.rank ≃ C3.tensorIndex,
        MissingOneColumnC3FiberComparison ID C3 D e := by
  constructor
  · rintro ⟨M⟩
    exact ⟨M.indexEquiv, ⟨{ fiberEquiv := M.fiberEquiv }⟩⟩
  · rintro ⟨e, ⟨f⟩⟩
    exact ⟨{ indexEquiv := e, fiberEquiv := f.fiberEquiv }⟩

/-- **Cardinality consequence:** the uniform datum forces
`D.rank = card C3.tensorIndex`. -/
theorem rank_card_of_missing
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (M : MissingC3PacketUniformComparison ID C3 D) :
    D.rank = Fintype.card C3.tensorIndex := by
  obtain ⟨M⟩ := M
  exact card_eq_of_missingData ID C3 D M

/-- **Downstream transport is constructed from the datum** (task-38): the product
transport into the C3 packet fibers along the uniform index comparison. -/
noncomputable def hddTransport_of_missingData
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (M : MissingC3PacketUniformComparisonData ID C3 D)
    (v : NumberField.FinitePlace ℚ) :
    ((i : Fin D.rank) → D.E i) →
      ((i : Fin D.rank) → C3LogShellFiber C3 (M.indexEquiv i)) :=
  hddToC3Function ID C3 D M v

#check missingData_iff_pair
#check rank_card_of_missing
#check hddTransport_of_missingData

end LeanFormal.IUT.XiFPaper.S3132UniformDependencyOrderActual

end
