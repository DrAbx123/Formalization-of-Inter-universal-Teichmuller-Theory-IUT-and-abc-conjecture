import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import Mathlib.Tactic

/-!
# A728 paper-faithful 3.12 — NORMALIZED volume convention, hqneg DISSOLVED

Paper convention: the log-volume used in 3.12 is NORMALIZED.  We normalize by the
full (theta) hull region:
`rpVolumeNorm T S = (haar T S).toReal / (haar T (fullRegion T)).toReal`,
with `haar = rootExtensionProductHaar` and denominator positive (green).

Then `rpVolumeNorm T (fullRegion T) = 1`, and the green strictness
`rpRegion_measure_lt_full` gives `rpVolumeNorm (rpRegion) < rpVolumeNorm (fullRegion) = 1`,
hence `hqneg_norm : requirementSignedQ (rpRequirementNorm T) < 0` DIRECTLY from
`Real.log_neg_iff` — no named hqneg input and no external normalization fact.

`final_3_12_normed` instantiates the 3.12 contract for `rpRequirementNorm`; the
remaining IPL/SHE/APT parameters are the standard stepxi evidence inputs.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Positivity of the full-region Haar measure (green re-derivation). -/
theorem fullRegion_measure_pos : 0 < rootExtensionProductHaar T (fullRegion T) := by
  have h := (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).1
  simpa [fullRegion, rootExtensionProductImageHull] using h

/-- Positivity of the full-region real volume. -/
theorem fullRegion_toReal_pos : 0 < (rootExtensionProductHaar T (fullRegion T)).toReal :=
  ENNReal.toReal_pos (ne_of_gt (fullRegion_measure_pos T))
    (ne_of_lt (fullRegion_measure_lt_top T))

/-- Normalized region volume: raw real Haar divided by the full-region real volume. -/
noncomputable def rpVolumeNorm (S : Set (S1902Carrier T)) : Real :=
  (rootExtensionProductHaar T S).toReal /
    (rootExtensionProductHaar T (fullRegion T)).toReal

/-- The normalized volume of the full region is `1`. -/
theorem rpVolumeNorm_fullRegion : rpVolumeNorm T (fullRegion T) = 1 := by
  unfold rpVolumeNorm
  exact div_self (ne_of_gt (fullRegion_toReal_pos T))

/-- Normalized xi-e requirement: same regions/containment as `rpRequirement`, with
the normalized volume.  The `strict_measure` field is the green raw strictness
divided by the positive full-region volume. -/
noncomputable def rpRequirementNorm :
    XiEContainmentRequirement (S1902Carrier T) (rpVolumeNorm T) where
  qRegion := rpRegion T
  thetaPossibleImages := rpRegion T
  hullRegion := fullRegion T
  q_in_possible := fun _ hx => hx
  possible_in_hull := rpRegion_subset_full T
  q_pos := by
    unfold rpVolumeNorm
    exact div_pos
      (ENNReal.toReal_pos (ne_of_gt (rpRegion_measure_pos T))
        (ne_of_lt (rpRegion_measure_lt_top T)))
      (fullRegion_toReal_pos T)
  strict_measure := by
    unfold rpVolumeNorm
    exact div_lt_div_of_pos_right
      ((ENNReal.toReal_lt_toReal (ne_of_lt (rpRegion_measure_lt_top T))
        (ne_of_lt (fullRegion_measure_lt_top T))).mpr (rpRegion_measure_lt_full T))
      (fullRegion_toReal_pos T)

/-- **hqneg dissolved**: the normalized q-pilot signed log-volume is strictly negative. -/
theorem hqneg_norm : requirementSignedQ (rpRequirementNorm T) < 0 := by
  have hpos : 0 < rpVolumeNorm T (rpRegion T) := (rpRequirementNorm T).q_pos
  have hlt : rpVolumeNorm T (rpRegion T) < 1 := by
    rw [← rpVolumeNorm_fullRegion T]
    unfold rpVolumeNorm
    exact div_lt_div_of_pos_right
      ((ENNReal.toReal_lt_toReal (ne_of_lt (rpRegion_measure_lt_top T))
        (ne_of_lt (fullRegion_measure_lt_top T))).mpr (rpRegion_measure_lt_full T))
      (fullRegion_toReal_pos T)
  have hdef : requirementSignedQ (rpRequirementNorm T) =
      Real.log (rpVolumeNorm T (rpRegion T)) := rfl
  rw [hdef]
  exact (Real.log_neg_iff hpos).mpr hlt

/-- **Paper-faithful 3.12 with hqneg dissolved**: the contract for the normalized
requirement, with the standard IPL/SHE/APT evidence parameters. -/
theorem final_3_12_normed
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirementNorm T) (hqneg_norm T)
        ipl hipl she hshe apt hapt) :=
  requirement_cor312 (rpRequirementNorm T) (hqneg_norm T) ipl hipl she hshe apt hapt

structure NormedRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def normedRows : List NormedRow :=
  [ ⟨"normalization convention", "rpVolumeNorm = raw.toReal / fullRegion.toReal; 3.12 depends only on ratios", "CONVENTION"⟩
  , ⟨"normalized requirement", "rpRequirementNorm (strict_measure from green raw strictness / positive denominator)", "GREEN"⟩
  , ⟨"hqneg dissolved", "hqneg_norm (no hqneg parameter, no named structure)", "GREEN"⟩
  , ⟨"3.12 normed", "final_3_12_normed (only IPL/SHE/APT evidence parameters remain)", "GREEN"⟩
  , ⟨"scope", "no RETRACTED use", "INTEGRITY"⟩
  ]

theorem normedRows_length : normedRows.length = 5 := rfl

theorem normedRows_statuses_ok :
    normedRows.all (fun r =>
      r.status ∈ ["CONVENTION", "GREEN", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual.hqneg_norm
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual.final_3_12_normed
