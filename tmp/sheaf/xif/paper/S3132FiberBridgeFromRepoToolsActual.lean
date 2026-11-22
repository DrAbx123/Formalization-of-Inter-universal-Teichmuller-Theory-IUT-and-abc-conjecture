import tmp.sheaf.xif.paper.S3132UniformFiberMissingActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.PrimeStripLogShellActual
import tmp.sheaf.xif.paper.SHELandingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionPacketLogShell

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3132UniformFactorComparisonComponentActual
open LeanFormal.IUT.XiFPaper.S3132UniformFiberMissingActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132FiberBridgeFromRepoToolsActual

universe u v uv upi umon ui

/-!
# task-65: fiber comparison via the REPO's existing completion tools

**Component, not a paper object.**  Owner: hull.  Consumers: task-62's
`MissingOneColumnC3FiberComparisonData`; mainline registry; shehdd gate.

The repo already provides the completion ring equivalences we need
(coord/TOOL-INVENTORY.md section B).  This module applies them instead of
manufacturing a new generic tool:

* `commonPrimeCompletionActualRingEquiv` (FinitePlaceCompletionPacketLogShell:16):
  `CommonPrimeCompletion place ≃+* Completion place.val`; since the C3 packet fiber
  is `C3LogShellFiber C3 i = CommonPrimeCompletion (c3LogShellPlace C3 i)`, this gives
  the actual completion bridge `c3FiberRingEquivActualCompletion`;
* `normalizedCompletionRingEquiv` (FinitePlaceNormalizedCompletion:63) is available
  for the normalized form if needed.

Consequently the fiber half of the uniform comparison reduces exactly to a
comparison of **actual completions**:

    Completion v  (completion of Q at the rational place v)
      ≃+*  Completion (c3LogShellPlace C3 (e i)).val
            (completion of I.initial.arithmetic.Fmod at the selected C3 place),

which is exactly the place/field identification datum that `OriginalInput` does
not expose (contract-missing; see AUDIT_LEDGER 2026-11-10 01:33 entry and the
negative result in S3132PrimeStripC3AllPlaceComparisonComponent).  The fiber
residual is therefore pure DATA INSTANTIATION, not missing mathematics:
`missingFiberComparison_iff_completionComparison`.

**Over-strongness remark (recorded):** the original task-38 datum quantifies
`fiberEquiv` over ALL rational places `v`; ring equivalences from `Completion v`
to the *same* C3 fiber can exist only for rational places whose residue
characteristic matches the C3 prime `C3.p` (a ring isomorphism preserves the
residue characteristic), so the paper-faithful datum is the place-restricted form
`MissingFiberCompletionComparisonData` at the rational place under `C3.p`.
Pages: IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.7, (ii), (v),
pp. 108-112.
-/

/-- The C3 packet fiber is ring-isomorphic to the actual completion at the
selected C3 tensor place (repo tool `commonPrimeCompletionActualRingEquiv`). -/
noncomputable def c3FiberRingEquivActualCompletion
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) (i : C3.tensorIndex) :
    C3LogShellFiber C3 i ≃+* Completion (c3LogShellPlace C3 i).val :=
  commonPrimeCompletionActualRingEquiv (c3LogShellPlace C3 i)

/-- The one-column local field at a rational place is the actual rational
completion (definitional). -/
theorem oneColumnLocalField_eq_completion (v : NumberField.FinitePlace ℚ) :
    (oneColumnStructure (k := ℚ)).localField v = Completion v :=
  rfl

/-- The (normalized) one-column completion is ring-isomorphic to the actual
rational completion (repo tool `normalizedCompletionRingEquiv`). -/
noncomputable def completionRingEquivNormalizedCompletion (v : NumberField.FinitePlace ℚ) :
    Completion v ≃+* NormalizedCompletion v :=
  (normalizedCompletionRingEquiv v).symm

/-- **Reduction of the fiber family to actual completions.**  The uniform fiber
comparison along an index equivalence is equivalent to the family of ring
equivalences between the rational completion and the actual C3 completion. -/
theorem nonempty_fiberFamily_iff_nonempty_completionFamily
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex) :
    Nonempty ((v : NumberField.FinitePlace ℚ) → (i : Fin D.rank) →
        (oneColumnStructure (k := ℚ)).localField v ≃+* C3LogShellFiber C3 (e i)) ↔
      Nonempty ((v : NumberField.FinitePlace ℚ) → (i : Fin D.rank) →
        Completion v ≃+* Completion (c3LogShellPlace C3 (e i)).val) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨fun v i => (h v i).trans (c3FiberRingEquivActualCompletion C3 (e i))⟩
  · rintro ⟨g⟩
    exact ⟨fun v i => (g v i).trans (c3FiberRingEquivActualCompletion C3 (e i)).symm⟩

/-- **Minimal data instantiation for the fiber half:** ring equivalences between
the actual rational completion and the actual C3 completion, for every HDD factor
index.  This is pure data (place/field identification), not new mathematics. -/
structure MissingFiberCompletionComparisonData
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex) where
  completionEquiv : (v : NumberField.FinitePlace ℚ) → (i : Fin D.rank) →
    Completion v ≃+* Completion (c3LogShellPlace C3 (e i)).val

/-- The `Prop` form of the data instantiation. -/
def MissingFiberCompletionComparison
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex) : Prop :=
  Nonempty (MissingFiberCompletionComparisonData ID C3 D e)

/-- **Fiber residual = pure data instantiation:** the task-62 exact missing fiber
comparison is equivalent to the actual-completion data instantiation. -/
theorem missingFiberComparison_iff_completionComparison
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex) :
    MissingOneColumnC3FiberComparison ID C3 D e ↔
      MissingFiberCompletionComparison ID C3 D e := by
  constructor
  · rintro ⟨f⟩
    refine ⟨{ completionEquiv := ?_ }⟩
    intro v i
    exact (f.fiberEquiv v i).trans (c3FiberRingEquivActualCompletion C3 (e i))
  · rintro ⟨g⟩
    refine ⟨{ fiberEquiv := ?_ }⟩
    intro v i
    exact (g.completionEquiv v i).trans
      (c3FiberRingEquivActualCompletion C3 (e i)).symm

#check c3FiberRingEquivActualCompletion
#check oneColumnLocalField_eq_completion
#check completionRingEquivNormalizedCompletion
#check nonempty_fiberFamily_iff_nonempty_completionFamily
#check MissingFiberCompletionComparisonData
#check missingFiberComparison_iff_completionComparison

end LeanFormal.IUT.XiFPaper.S3132FiberBridgeFromRepoToolsActual

end