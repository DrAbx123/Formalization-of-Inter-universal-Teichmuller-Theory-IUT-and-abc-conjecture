import tmp.sheaf.xif.paper.S2712MultiQConsumerActual
import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataUnconditionalActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2714MultiConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2712MultiQConsumerActual
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uG uL uC uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

structure PaperMultiUnconditionalData
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (P : PaperSignedHull X label)
    (D : MultiPlaceQPilotDonor I) where
  sourceLink : MultiQPaperXiFSourceLink O P D
  sourceLink_holds : sourceLink.link_identification

namespace PaperMultiUnconditionalData
variable {O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
  I G envStrip}
variable {P : PaperSignedHull X label}
variable {D : MultiPlaceQPilotDonor I}

theorem qPilot_le_signedHull (Ddata : PaperMultiUnconditionalData O P D) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  MultiQPaperXiFInclusion.qPilot_le_signedHull
    ⟨Ddata.sourceLink, Ddata.sourceLink_holds⟩

theorem qPilot_mem_ray (Ddata : PaperMultiUnconditionalData O P D) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume :=
  MultiQPaperXiFInclusion.qPilot_mem_ray
    ⟨Ddata.sourceLink, Ddata.sourceLink_holds⟩

theorem qPilotLogVolume_eq_multi (Ddata : PaperMultiUnconditionalData O P D) :
    O.qPilotLogVolume = paperQPilotLogVolume_multi D :=
  MultiQPaperXiFInclusion.qPilotLogVolume_eq_multi
    ⟨Ddata.sourceLink, Ddata.sourceLink_holds⟩
end PaperMultiUnconditionalData

end LeanFormal.IUT.XiFPaper.S2714MultiConsumerActual
end
