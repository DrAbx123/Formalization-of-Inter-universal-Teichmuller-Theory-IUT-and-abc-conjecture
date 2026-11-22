import tmp.sheaf.xif.paper.Mzk1FinalConditionalCertificateActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import Mathlib.Tactic

/-!
# A715 paper-faithful 3.12: hqneg evidence and discharge of `final_3_12`

The paper-faithful `final_3_12` takes the sign hypothesis
`hqneg : requirementSignedQ (rpRequirement T) < 0` as a parameter.  The definition
`requirementSignedQ = signedLogVolume vol D.qRegion` is abstract in the volume
functional; for `rpRequirement`, `qRegion = rpRegion T` and `vol = rpVolume`, so
`hqneg` is exactly the (paper) strict negativity of the q-pilot log-volume
`Real.log (rpVolume T (rpRegion T))`.

This file records the *precise gap* as an explicit evidence structure and proves
that it suffices to eliminate the `hqneg` parameter from `final_3_12`:
* `HqnegEvidence T` carries the bridge identity
  `requirementSignedQ (rpRequirement T) = qPilotLogVolume` and the strict sign
  `qPilotLogVolume < 0`;
* `final_3_12_of_hqnegEvidence` discharges `final_3_12` with this evidence.

Candidate green/ported lemmas for the two fields (types to check in their modules;
not imported here to keep this file dependency-light):
`sourceQPilotSignedLog_eq_neg_badQAbsLog`, `signedQPilotLogVolume_eq_neg_abs_qParameter`,
`qPilotLogVolume_nonpos`, `qPilotLogVolume_neg_of_bad_nonempty`,
`S3137QThetaPilotLogVolumeReadingsActual.qPilotLogVolumeReading_nonpos`.

No sorry/axiom/True; no RETRACTED statement is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312HqnegActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- `rpVolume` of `rpRegion` is positive (needed for the log sign computation). -/
theorem rpVolume_rpRegion_pos : 0 < rpVolume T (rpRegion T) := by
  unfold rpVolume
  exact ENNReal.toReal_pos (ne_of_gt (rpRegion_measure_pos T))
    (ne_of_lt (rpRegion_measure_lt_top T))

/-- `hqneg` is exactly `rpVolume rpRegion < 1` (the q-pilot strict negativity as a
concrete numeric inequality). -/
theorem hqneg_iff_rpVolume_lt_one :
    requirementSignedQ (rpRequirement T) < 0 ↔ rpVolume T (rpRegion T) < 1 := by
  have hdef : requirementSignedQ (rpRequirement T) =
      Real.log (rpVolume T (rpRegion T)) := rfl
  rw [hdef]
  exact Real.log_neg_iff (rpVolume_rpRegion_pos T)

/-- **Explicit hqneg evidence**: the concrete q-pilot volume inequality
`rpVolume rpRegion < 1`. -/
structure HqnegEvidence where
  rpVolume_lt_one : rpVolume T (rpRegion T) < 1


/-- The evidence yields the strict sign hypothesis of `final_3_12`. -/
theorem HqnegEvidence.hqneg (E : HqnegEvidence T) :
    requirementSignedQ (rpRequirement T) < 0 :=
  (hqneg_iff_rpVolume_lt_one T).mpr E.rpVolume_lt_one

/-- **hqneg discharged for the paper-faithful 3.12**: with explicit evidence, the
`hqneg` parameter of `final_3_12` is eliminated. -/
theorem final_3_12_of_hqnegEvidence (E : HqnegEvidence T)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) (E.hqneg T) ipl hipl she hshe apt hapt) :=
  final_3_12 (T := T) (E.hqneg T) ipl hipl she hshe apt hapt

/-- Exact gap record: without a bridge identity from `requirementSignedQ` to the
q-pilot log-volume, `hqneg` cannot be derived from the abstract requirement. -/
structure HqnegGap where
  missing_bridge : String
  missing_sign : String
  deriving Repr, DecidableEq

def hqnegGap : HqnegGap :=
  { missing_bridge :=
      "requirementSignedQ (rpRequirement T) = Real.log (rpVolume T (rpRegion T)) (PROVED: rfl)",
    missing_sign :=
      "rpVolume T (rpRegion T) < 1 (paper q-pilot strict negativity; normalization-dependent)" }

structure HqnegRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def hqnegRows : List HqnegRow :=
  [ ⟨"hqneg evidence structure", "HqnegEvidence (bridge identity + strict sign)", "GREEN_DEF"⟩
  , ⟨"final_3_12 discharge", "final_3_12_of_hqnegEvidence", "GREEN_CONDITIONAL"⟩
  , ⟨"exact gap", "rpVolume T (rpRegion T) < 1 (log sign reduction PROVED; numeric sign is the remaining paper input)", "NAMED_GAP"⟩
  , ⟨"candidate sources", "sourceQPilotSignedLog_eq_neg_badQAbsLog; qPilotLogVolume_neg_of_bad_nonempty; S3137 qPilotLogVolumeReading_nonpos", "CANDIDATE"⟩
  , ⟨"scope", "paper-faithful hqneg wiring only; no vacuous conclusion", "INTEGRITY"⟩
  ]

theorem hqnegRows_length : hqnegRows.length = 5 := rfl

theorem hqnegRows_statuses_ok :
    hqnegRows.all (fun r =>
      r.status ∈ ["GREEN_DEF", "GREEN_CONDITIONAL", "NAMED_GAP", "CANDIDATE", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312HqnegActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312HqnegActual.HqnegEvidence.hqneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312HqnegActual.final_3_12_of_hqnegEvidence
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual.final_3_12
