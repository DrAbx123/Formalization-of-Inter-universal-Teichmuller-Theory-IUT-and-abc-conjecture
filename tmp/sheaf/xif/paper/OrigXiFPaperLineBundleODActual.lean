import tmp.sheaf.xif.paper.OrigXiFPaperLineBundleActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundleODActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual

universe uG
variable {l : PrimeGeFive}
variable {V : Type}
variable {Label : Type} {Choice : Type} [AddGroup Label] [Preorder Choice]
variable (I : OriginalInput.{0, 0, 0, 0, 0} l V)
variable (G : Type uG) [Group G] [TopologicalSpace G]
variable (envStrip : FPrimeStrip V)

/-- Actual O(-D) line-bundle identification: the carrier is the actual
q-pilot fractional-ideal O(-D) carrier of OrigXiFPaperLineBundleCarrier, with
the same completion localizations.  This is not the completion-localized
trivial line bundle. -/
def OrigXiFPaperLineBundleODIdentified
    (D : OrigXiFPaperLineBundleData I)
    (L : PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod)) : Prop :=
  L = OrigXiFPaperLineBundleCarrier I D

/-- The actual O(-D) carrier satisfies the O(-D) identification. -/
theorem OrigXiFPaperLineBundleODCarrier_identified
    (D : OrigXiFPaperLineBundleData I) :
    OrigXiFPaperLineBundleODIdentified I D
      (OrigXiFPaperLineBundleCarrier I D) :=
  rfl

/-- The section type of the O(-D) carrier is the actual q-pilot fractional
ideal, not the completion-localized trivial carrier. -/
theorem OrigXiFPaperLineBundleODCarrier_total
    (D : OrigXiFPaperLineBundleData I) :
    (OrigXiFPaperLineBundleCarrier I D).total =
      ↥(OrigXiFPaperQPilotLineBundle I D) := rfl

/-- Frozen paper q-pilot object with the actual O(-D) fractional-ideal line
bundle, conditional exactly on the existing first field D.  The frozen
paper_lineBundle_identification is instantiated by the O(-D) proposition, not
the completion-carrier simplification. -/
noncomputable def origXiFPaperQPilotObjectOD
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : OrigXiFPaperLineBundleData I) :
    PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip where
  boundary := O.boundary
  strip := O.strip
  strip_eq_source := O.strip_eq_source
  oneColumn := O.oneColumn
  lineBundle := OrigXiFPaperLineBundleCarrier I D
  logKummer := O.logKummer
  qPilotLogVolume := O.qPilotLogVolume
  qPilotLogVolume_eq := O.qPilotLogVolume_eq
  paper_strip_identification := O.paper_strip_identification
  paper_lineBundle_identification :=
    OrigXiFPaperLineBundleODIdentified I D
      (OrigXiFPaperLineBundleCarrier I D)
  paper_logKummer_identification := O.paper_logKummer_identification
  paper_qPilot_log_identification := O.paper_qPilot_log_identification

/-- The O(-D) object's line-bundle identification is exactly the actual O(-D)
carrier proposition, not the completion-carrier version. -/
theorem origXiFPaperQPilotObjectOD_paper_lineBundle
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      I G envStrip)
    (D : OrigXiFPaperLineBundleData I) :
    (origXiFPaperQPilotObjectOD I G envStrip O D).paper_lineBundle_identification :=
  OrigXiFPaperLineBundleODCarrier_identified I D

end LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundleODActual

end
