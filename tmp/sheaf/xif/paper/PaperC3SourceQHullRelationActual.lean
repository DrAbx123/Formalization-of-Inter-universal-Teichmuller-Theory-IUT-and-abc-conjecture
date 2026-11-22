import tmp.sheaf.xif.paper.PaperC3SourceDataQConsistencyActual
import tmp.sheaf.xif.paper.PaperC3TensorBlockActual
import tmp.sheaf.xif.paper.GenericQPilotCompletionPowerActual

-- S143: actual qUnit lambda-O hull relation and generic qPilot comparison.
--
-- The paper/paper-block qUnit hull is compared with the source-geometry
-- qUnit hull on the same Block.  Transport to SourceQTensorBlock is recorded
-- as an exact field, not assumed.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.GenericQPilotCompletionPowerActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def sourceQGeometry :
    CompletionValuedSourceGeometry (l := l) (K := T.arithmetic.F)
      (p := qVFamTensorP T b) PUnit.{1} where
  place := fun _ => sourceThetaPlace T b
  qUnit := fun _ => sourceQUnit T b
  thetaPacket := sourceQThetaPacket T b
  thetaPacket_q_eq := fun _ => sourceQThetaPacket_q_eq_norm T b

-- The actual qUnit lambda-O multiplication image on the same Block.
noncomputable def sourceQHullInPaperBlock :
    Set (Block (G := sourceQGeometry (l := l) T b)) :=
  {x | ∃ o ∈ paperUnitReference (G := sourceQGeometry (l := l) T b),
    x = qParameterUnitLambda (G := sourceQGeometry (l := l) T b) * o}

theorem qParameterUnitLambdaHull_subset_sourceQHullInPaperBlock :
    qParameterUnitLambdaHull (G := sourceQGeometry (l := l) T b) ⊆
      sourceQHullInPaperBlock T b := by
  rintro x ⟨o, ho, hx⟩
  exact ⟨o, ho, hx⟩

theorem genericQPilotImagePoint_mem_sourceQHullInPaperBlock
    (hq : ∀ v : PUnit.{1},
      ‖((sourceQGeometry (l := l) T b).qUnit v :
        CommonPrimeCompletion ((sourceQGeometry (l := l) T b).place v))‖ ≤ 1) :
    genericQPilotImagePoint (G := sourceQGeometry (l := l) T b) ∈
      sourceQHullInPaperBlock T b :=
  qParameterUnitLambdaHull_subset_sourceQHullInPaperBlock T b
    (genericQPilotImagePoint_mem_qUnitLambdaHull
      (G := sourceQGeometry (l := l) T b) (l := l) hq)

structure SourceQHullTransportGap where
  transport : Block (G := sourceQGeometry (l := l) T b) → SourceQTensorBlock T b
  hull_relation : Prop
  hull_relation_holds : hull_relation

#check sourceQGeometry
#check sourceQHullInPaperBlock
#check qParameterUnitLambdaHull_subset_sourceQHullInPaperBlock
#check genericQPilotImagePoint_mem_sourceQHullInPaperBlock

-- S159: the type equality is rfl; actual identity transport and hull relation.
noncomputable def sourceQHullTransport :
    Block (G := sourceQGeometry (l := l) T b) → SourceQTensorBlock T b :=
  fun x => x

theorem sourceQHullTransport_apply
    (x : Block (G := sourceQGeometry (l := l) T b)) :
    sourceQHullTransport T b x = x := rfl

theorem sourceQHullTransport_hull_relation
    (x : Block (G := sourceQGeometry (l := l) T b)) :
    x ∈ sourceQHullInPaperBlock T b ↔
      sourceQHullTransport T b x ∈ sourceQTensorLambdaOHull T b := by
  rfl

noncomputable def sourceQHullTransportGapClosed :
    SourceQHullTransportGap T b where
  transport := sourceQHullTransport T b
  hull_relation := ∀ x : Block (G := sourceQGeometry (l := l) T b),
    x ∈ sourceQHullInPaperBlock T b ↔
      sourceQHullTransport T b x ∈ sourceQTensorLambdaOHull T b
  hull_relation_holds := sourceQHullTransport_hull_relation T b

theorem sourceQHullTransportGap_nonempty :
    Nonempty (SourceQHullTransportGap T b) :=
  ⟨sourceQHullTransportGapClosed T b⟩

theorem genericQPilotImagePoint_mem_sourceQTensorLambdaOHull
    (hq : ∀ v : PUnit.{1},
      ‖((sourceQGeometry (l := l) T b).qUnit v :
        CommonPrimeCompletion ((sourceQGeometry (l := l) T b).place v))‖ ≤ 1) :
    sourceQHullTransport T b
      (genericQPilotImagePoint (G := sourceQGeometry (l := l) T b)) ∈
      sourceQTensorLambdaOHull T b :=
  (sourceQHullTransport_hull_relation T b _).mp
    (genericQPilotImagePoint_mem_sourceQHullInPaperBlock T b hq)

#check sourceQHullTransport
#check sourceQHullTransport_hull_relation
#check sourceQHullTransportGapClosed
#check sourceQHullTransportGap_nonempty
#check genericQPilotImagePoint_mem_sourceQTensorLambdaOHull
end LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual

end