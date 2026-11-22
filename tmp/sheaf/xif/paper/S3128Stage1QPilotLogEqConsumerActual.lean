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
namespace LeanFormal.IUT.XiFPaper.S3128Stage1QPilotLogEqConsumerActual
universe ua uv upi umon ui uG uL uC uC3 uD3
variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I))
variable (C3 : SourcePilotRegionData I)

theorem S3128Stage1QPilotLogEqConsumer_local
    (h : O.qPilotLogVolume = paperQPilotLogVolume C3) :
    O.qPilotLogVolume = localSignedLog C3.q := by
  rw [h]
  exact concretePaperQPilotLogVolume_eq_localSignedLog

theorem S3128Stage1QPilotLogEqConsumer_paper_of_local
    (h : O.qPilotLogVolume = localSignedLog C3.q) :
    O.qPilotLogVolume = paperQPilotLogVolume C3 := by
  rw [h]
  exact concretePaperQPilotLogVolume_eq_localSignedLog.symm

#check S3128Stage1QPilotLogEqConsumer_local
#check S3128Stage1QPilotLogEqConsumer_paper_of_local
end LeanFormal.IUT.XiFPaper.S3128Stage1QPilotLogEqConsumerActual