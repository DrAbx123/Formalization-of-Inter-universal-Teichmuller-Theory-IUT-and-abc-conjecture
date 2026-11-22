import tmp.sheaf.xif.paper.ConcreteQPilotLogIdentificationActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.ConcreteQPilotLogIdentificationActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1QPilotLogConsumerActual
universe ua uv upi umon ui uG uL uC uC3 uD3
variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I))
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

theorem S3128Stage1QPilotLogConsumer_paper
    (h : ConcreteSourceQIdentification (I := I) C3) :
    O.qPilotLogVolume = paperQPilotLogVolume C3 :=
  concreteO_qPilotLogVolume_eq_paper O C3 h

theorem S3128Stage1QPilotLogConsumer_signed
    (hC3 : Oa.line.C3 = C3)
    (h : ConcreteSourceQIdentification (I := I) C3) :
    O.qPilotLogVolume = Oa.signedQPilotLogVolume :=
  concreteO_qPilotLogVolume_eq_signed O Oa C3 hC3 h

theorem S3128Stage1QPilotLogConsumer_iff
    (hC3 : Oa.line.C3 = C3) :
    (O.qPilotLogVolume = paperQPilotLogVolume C3 ∧
      O.qPilotLogVolume = Oa.signedQPilotLogVolume) ↔
      ConcreteSourceQIdentification (I := I) C3 :=
  concreteQPilotLogIdentifications_iff_sourceQ O Oa C3 hC3

#check S3128Stage1QPilotLogConsumer_paper
#check S3128Stage1QPilotLogConsumer_signed
#check S3128Stage1QPilotLogConsumer_iff
end LeanFormal.IUT.XiFPaper.S3128Stage1QPilotLogConsumerActual