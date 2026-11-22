import tmp.sheaf.xif.paper.S3136Gap2AdditiveWiringActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: lgpSourceInterface_hunit|lgpGap2_of_additive|region obligation -> hits S3136Gap2AdditiveWiringActual:45/51/62 + S3136RegionCObligationStatusActual rows (hunit WIRED, hpoint CONDITIONAL) -> REUSE (anchor record; no re-proof).

# (c) region record: stage4 gap-2 wiring anchor (no closure)

Corpus: IUT IV Region (c) paper-route.  stage4's gap-2 wiring provides the
source-interface log-volume inequality (lgpSourceInterface_hunit: the unit-region
bound with D0 = 0) and the conditional gap-2 theorem lgpGap2_of_additive with the
three named analytic inputs hmem/hadd/hline.  This file records the anchor rows so
the Theta-side (c) record can cite the exact tree declarations; nothing is re-proved
and no region closure is claimed.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideGap2AnchorRecordActual

open LeanFormal.IUT.XiFPaper.S3136Gap2AdditiveWiringActual

/-- A gap-2 anchor row: (item, stage4 declaration, status). -/
structure Gap2AnchorRow where
  item : String
  declaration : String
  status : String

/-- The gap-2 wiring anchors for the (c) region record. -/
def gap2AnchorRows : List Gap2AnchorRow :=
  [ { item := "source-interface IQ hull log-volume",
      declaration := "lgpSourceInterface (S3136Gap2AdditiveWiringActual:45)",
      status := "interface built on sourceHaarActualOriginalInput (reuse)" }
  , { item := "unit-region bound hunit, D0 = 0",
      declaration := "lgpSourceInterface_hunit (S3136Gap2AdditiveWiringActual:51)",
      status := "elementary bound PROVED in stage4 (reuse; no re-proof)" }
  , { item := "conditional gap-2 region theorem",
      declaration := "lgpGap2_of_additive (S3136Gap2AdditiveWiringActual:62) with named inputs hmem/hadd/hline",
      status := "conditional; (c) closure NOT claimed" }
  , { item := "region obligation status rows",
      declaration := "S3136RegionCObligationStatusActual (hunit WIRED; hpoint CONDITIONAL)",
      status := "reference only" } ]

/-- The anchor record has four rows. -/
theorem gap2AnchorRows_length : gap2AnchorRows.length = 4 := rfl

#check Gap2AnchorRow
#check gap2AnchorRows
#check gap2AnchorRows_length

end LeanFormal.IUT.XiFPaper.S3132ThetaSideGap2AnchorRecordActual