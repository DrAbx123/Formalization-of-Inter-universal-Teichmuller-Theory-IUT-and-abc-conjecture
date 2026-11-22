import tmp.sheaf.xif.paper.S3132UniformFactorComparisonComponentActual
import tmp.sheaf.xif.paper.S3136LGPGlobalUnitsToLocalUnitsActual
import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.PrimeStripLogShellActual

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
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3136LGPGlobalUnitsToLocalUnitsActual
open LeanFormal.IUT.XiFPaper.S3132UniformFactorComparisonComponentActual

namespace LeanFormal.IUT.XiFPaper.S3132UniformFiberMissingActual

universe u v uv upi umon ui

/-!
# task-62 (2): the fiber half of the uniform HDD/C3 comparison — exact missing

**Component, not a paper object.**  Owner: hull.  Consumers: task-38's
`MissingC3PacketUniformComparisonData`; mainline registry; shehdd gate.

The second half is the uniform ring comparison of the one-column local fields
with the C3 packet fibers.  Its *actual type form* is constructed by
`lgpC3Fiber_eq_completion` (stage4, EXIT=0): the packet fiber is the actual
completion at the selected place,

    C3LogShellFiber C3 i = Completion (c3LogShellPlace C3 i).val,

so the comparison is exactly a comparison of completions:

    oneColumnStructure.localField v = Completion v  (completion of Q at v)
      vs
    C3LogShellFiber C3 (e i) = Completion (c3LogShellPlace C3 (e i)).val
      (completion of I.initial.arithmetic.Fmod at the selected C3 place).

**Why it is not constructible.**  A ring equivalence of these completions exists
only when the C3 place is a degree-one completion over the rational place below
it with matching rational primes; the source place data certifying this
(`placeToMod : V → NumberFieldPlace Fmod` with bijectivity, residue
characteristic and degree-one comparison) is not exposed by `OriginalInput`
(`SourceDefinition31DualContractAlignment.lean:88`: no record projection
`SourceInitialThetaData -> SourceDefinition31Data`).  The prime half is
available on the bad places only (qpilot `S3131BadTensorPrimeMatch`,
`S3131BadTensorPlaceMatch`); the all-place/fiber half is this exact missing.
Pages: IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.7, (ii), (v),
pp. 108-112.
-/

/-- **Actual type form (constructed from stage4):** the C3 packet fiber is the
actual completion at the selected C3 tensor place. -/
theorem c3Fiber_eq_actualCompletion
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) (i : C3.tensorIndex) :
    C3LogShellFiber C3 i = Completion (c3LogShellPlace C3 i).val :=
  lgpC3Fiber_eq_completion C3 i

/-- **Minimal exact missing fiber datum:** the uniform comparison of the
one-column rational completions with the C3 packet fibers, ring level, along a
chosen index equivalence. -/
structure MissingOneColumnC3FiberComparisonData
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex) where
  fiberEquiv : (v : NumberField.FinitePlace ℚ) → (i : Fin D.rank) →
    (oneColumnStructure).localField v ≃+* C3LogShellFiber C3 (e i)

/-- The `Prop` form of the minimal exact missing fiber datum. -/
def MissingOneColumnC3FiberComparison
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex) : Prop :=
  Nonempty (MissingOneColumnC3FiberComparisonData ID C3 D e)

/-- **Construction of the task-38 missing datum from the index equivalence and
the minimal exact missing fiber datum.** -/
theorem missingC3PacketUniformComparison_of_index_and_fiber
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex)
    (Mf : MissingOneColumnC3FiberComparison ID C3 D e) :
    MissingC3PacketUniformComparison ID C3 D := by
  obtain ⟨f⟩ := Mf
  exact ⟨{ indexEquiv := e, fiberEquiv := f.fiberEquiv }⟩

#check c3Fiber_eq_actualCompletion
#check MissingOneColumnC3FiberComparisonData
#check MissingOneColumnC3FiberComparison
#check missingC3PacketUniformComparison_of_index_and_fiber

end LeanFormal.IUT.XiFPaper.S3132UniformFiberMissingActual

end