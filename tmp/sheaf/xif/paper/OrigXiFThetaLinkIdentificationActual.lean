import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.OrigXiFPaperSignedHullActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotScalarActual

-- S1458: concrete ThetaLink link_identification at the paper O layer.
-- link_identification is the actual qPilot scalar compatibility plus the
-- signed-hull log-volume comparison; link_implies_inclusion is proved.
-- No placeholder Prop, no target-as-input in the ray direction.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.ThetaLink

universe u uG uL uC

variable {X : Type u} [TopologicalSpace X] {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}

variable (O : PaperQPilotObject (Label := Label) (Choice := Choice)
  I G envStrip)
variable (D : OrigXiFPaperSignedHullData X l)
variable (C3 : SourcePilotRegionDataL I)

/-- Concrete ThetaLink link_identification: the actual paper qPilot scalar
(from the actual L-carrier C3) equals the object scalar, and is bounded
by the actual signed theta hull log-volume. -/
def OrigXiFThetaLinkIdentification
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL I) : Prop :=
  O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3 ∧
    OrigXiFPaperQPilotLogVolume C3 ≤ OrigXiFSignedThetaHullLogVolume D

/-- Concrete link_implies_inclusion: the paper comparison yields membership
in the actual signed-hull ray. -/
theorem OrigXiFThetaLinkIdentification_implies_inclusion
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL I)
    (h : OrigXiFThetaLinkIdentification O D C3) :
    O.qPilotLogVolume ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume := by
  rcases h with ⟨hq, hle⟩
  rw [hq]
  exact (OrigXiFThetaLinkRay_iff_le D (OrigXiFPaperQPilotLogVolume C3)).mpr hle

/-- Producer direction from the two actual fields. -/
theorem OrigXiFThetaLinkIdentification_of_fields
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL I)
    (hq : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3)
    (hle : OrigXiFPaperQPilotLogVolume C3 ≤
      OrigXiFSignedThetaHullLogVolume D) :
    OrigXiFThetaLinkIdentification O D C3 :=
  ⟨hq, hle⟩

/-- Exact first scalar field, retained: the object scalar is the actual
paper q-pilot scalar. -/
def OrigXiFThetaLinkScalarExactFirstField
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL I) : Prop :=
  O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3

/-- Exact signed-hull comparison field. -/
def OrigXiFThetaLinkComparisonExactField
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL I) : Prop :=
  OrigXiFPaperQPilotLogVolume C3 ≤ OrigXiFSignedThetaHullLogVolume D

#check OrigXiFThetaLinkIdentification
#check OrigXiFThetaLinkIdentification_implies_inclusion
#check OrigXiFThetaLinkIdentification_of_fields
#check OrigXiFThetaLinkScalarExactFirstField
#check OrigXiFThetaLinkComparisonExactField

end LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkIdentificationActual

end