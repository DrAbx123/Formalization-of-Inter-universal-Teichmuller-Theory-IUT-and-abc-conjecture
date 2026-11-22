import tmp.sheaf.xif.paper.OrigXiFThetaLinkIdentificationActual

-- S1463: O-layer actual ThetaLink structure.
-- link_identification is the S1458 concrete proposition, not a free Prop.
-- The two exact scalar fields are structure inputs; no inhabitant is faked.
-- link_implies_inclusion is actual via S1458.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkIdentificationActual

universe u uG uL uC

variable {X : Type u} [TopologicalSpace X] {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}

/-- Conditional O-layer ThetaLink actual data.  The two exact scalar fields
are exactly the S1458 scalar compatibility and signed-hull comparison. -/
structure OrigXiFThetaLinkActual
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL I) where
  /-- Exact scalar compatibility: the object scalar is the actual paper qPilot scalar. -/
  scalar_eq : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3
  /-- Exact signed-hull comparison: actual qPilot scalar <= actual signed hull. -/
  signedHull_le :
    OrigXiFPaperQPilotLogVolume C3 ≤ OrigXiFSignedThetaHullLogVolume D

/-- Concrete link_identification, definitionally the S1458 proposition. -/
def OrigXiFThetaLinkActual.link_identification
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {D : OrigXiFPaperSignedHullData X l}
    {C3 : SourcePilotRegionDataL I}
    (_A : OrigXiFThetaLinkActual O D C3) : Prop :=
  OrigXiFThetaLinkIdentification O D C3

theorem OrigXiFThetaLinkActual.link_identification_eq
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {D : OrigXiFPaperSignedHullData X l}
    {C3 : SourcePilotRegionDataL I}
    (A : OrigXiFThetaLinkActual O D C3) :
    A.link_identification = OrigXiFThetaLinkIdentification O D C3 := rfl

/-- Actual link_implies_inclusion for the structure. -/
theorem OrigXiFThetaLinkActual.link_implies_inclusion
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {D : OrigXiFPaperSignedHullData X l}
    {C3 : SourcePilotRegionDataL I}
    (A : OrigXiFThetaLinkActual O D C3)
    (h : A.link_identification) :
    O.qPilotLogVolume ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume :=
  OrigXiFThetaLinkIdentification_implies_inclusion O D C3 h

/-- Conditional constructor from the two exact scalar fields. -/
noncomputable def origXiFThetaLinkActualOf
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL I)
    (hscalar : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3)
    (hcomparison : OrigXiFPaperQPilotLogVolume C3 ≤
      OrigXiFSignedThetaHullLogVolume D) :
    OrigXiFThetaLinkActual O D C3 :=
  ⟨hscalar, hcomparison⟩

/-- Exact first scalar field, not asserted. -/
def OrigXiFThetaLinkActualScalarExactField
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (C3 : SourcePilotRegionDataL I) : Prop :=
  O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3

/-- Exact signed-hull comparison field, not asserted. -/
def OrigXiFThetaLinkActualComparisonExactField
    (D : OrigXiFPaperSignedHullData X l)
    (C3 : SourcePilotRegionDataL I) : Prop :=
  OrigXiFPaperQPilotLogVolume C3 ≤ OrigXiFSignedThetaHullLogVolume D

#check OrigXiFThetaLinkActual
#check OrigXiFThetaLinkActual.link_identification
#check OrigXiFThetaLinkActual.link_implies_inclusion
#check origXiFThetaLinkActualOf
#check OrigXiFThetaLinkActualScalarExactField
#check OrigXiFThetaLinkActualComparisonExactField

end LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual

end