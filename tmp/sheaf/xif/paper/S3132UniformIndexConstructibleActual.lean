import tmp.sheaf.xif.paper.S3132UniformFactorComparisonComponentActual
import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.S3137C3TensorBlockDimensionActual

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
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3132UniformFactorComparisonComponentActual

namespace LeanFormal.IUT.XiFPaper.S3132UniformIndexConstructibleActual

universe u v uv upi umon ui

/-!
# task-62 (1): the index part of the uniform HDD/C3 comparison, constructed

**Component, not a paper object.**  Owner: hull.  Consumers: task-38's
`MissingC3PacketUniformComparisonData`; mainline registry; shehdd gate.

The index component `indexEquiv : Fin D.rank ≃ C3.tensorIndex` of the task-38
missing datum is **constructible from a cardinality equality alone**:
`indexEquiv_of_rank_card`.  Conversely any datum yields the cardinality equality
`card_eq_of_missingData`; therefore the index part is *numerical only*.

**Paper-faithfulness is NOT supplied by cardinality:** the actual index
comparison is the badplace/tensor-index comparison of the paper
(qpilot's `S3131BadTensorIndexEquivalence` for the bad places) together with the
all-place `placeToMod` provenance (contract-missing; see
`S3132PrimeStripC3AllPlaceComparisonComponent` negative result).  So construction
of `indexEquiv` here is a real mathematical step only as an *existence from
cardinality*; the paper-faithful choice remains an exact Missing datum and the
fiber comparison below is the second, independent half.
Pages: IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.7, (ii), (v),
pp. 108-112.
-/

/-- **Constructed (given the cardinality equality):** the index equivalence
`Fin D.rank ≃ C3.tensorIndex`. -/
noncomputable def indexEquiv_of_rank_card
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (h : D.rank = Fintype.card C3.tensorIndex) :
    Fin D.rank ≃ C3.tensorIndex :=
  Fintype.equivOfCardEq (by simpa using h)

/-- **Necessary condition (constructed):** any uniform comparison datum forces
the actual cardinality equality of the HDD rank and the C3 tensor index. -/
theorem card_eq_of_missingData
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (M : MissingC3PacketUniformComparisonData ID C3 D) :
    D.rank = Fintype.card C3.tensorIndex := by
  have h := Fintype.card_congr M.indexEquiv
  simpa using h

/-- **Construction of the missing datum from its two halves:** an index
equivalence and the uniform fiber comparison. -/
noncomputable def missingData_of_index_and_fiber
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex)
    (fiber : (v : NumberField.FinitePlace ℚ) → (i : Fin D.rank) →
      (oneColumnStructure).localField v ≃+* C3LogShellFiber C3 (e i)) :
    MissingC3PacketUniformComparisonData ID C3 D :=
  { indexEquiv := e, fiberEquiv := fiber }

/-- The `Prop` form from the two halves. -/
theorem missingC3Packet_of_index_and_fiber
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex)
    (fiber : (v : NumberField.FinitePlace ℚ) → (i : Fin D.rank) →
      (oneColumnStructure).localField v ≃+* C3LogShellFiber C3 (e i)) :
    MissingC3PacketUniformComparison ID C3 D :=
  ⟨missingData_of_index_and_fiber ID C3 D e fiber⟩

#check indexEquiv_of_rank_card
#check card_eq_of_missingData
#check missingData_of_index_and_fiber
#check missingC3Packet_of_index_and_fiber

end LeanFormal.IUT.XiFPaper.S3132UniformIndexConstructibleActual

end