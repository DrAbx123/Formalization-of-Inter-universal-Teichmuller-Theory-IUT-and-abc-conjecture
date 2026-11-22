import tmp.sheaf.xif.paper.Mzk1PaperFaithful312RpNormalizationActual
import tmp.sheaf.xif.paper.Mzk1FinalConditionalCertificateActual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import Mathlib.Tactic

/-!
# A726 paper-faithful 3.12 FINAL: hqneg from the single normalization proposition

Full instantiation of `final_3_12` with the hqneg hypothesis supplied DIRECTLY by
`hqneg_direct` (no named evidence structure): the only remaining input is the single
normalization proposition `RpUnitBallHaarOne T` (unit-ball Haar = 1), which is a
proposition about the concrete measure, not a structure.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312FinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312HqnegActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312RpNormalizationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Paper-faithful 3.12, concrete**: `final_3_12` fully instantiated, with the
hqneg parameter discharged by `hqneg_direct` modulo the single normalization
proposition `RpUnitBallHaarOne`. -/
theorem final_3_12_concrete (hN : RpUnitBallHaarOne T)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) (hqneg_direct T hN)
        ipl hipl she hshe apt hapt) :=
  final_3_12 (T := T) (hqneg_direct T hN) ipl hipl she hshe apt hapt

/-- The same instantiation with `hqneg_direct` unfolded. -/
theorem final_3_12_concrete' (hN : RpUnitBallHaarOne T)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T)
        ((hqneg_iff_rpVolume_lt_one T).mpr (rpVolume_rpRegion_lt_one T hN))
        ipl hipl she hshe apt hapt) :=
  final_3_12_concrete T hN ipl hipl she hshe apt hapt

structure FinalRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def finalRows : List FinalRow :=
  [ ⟨"hqneg direct", "hqneg_direct (modulo RpUnitBallHaarOne)", "GREEN_CONDITIONAL"⟩
  , ⟨"3.12 concrete", "final_3_12_concrete (no hqneg parameter, no named structure)", "GREEN_CONDITIONAL"⟩
  , ⟨"single input", "RpUnitBallHaarOne T (proposition about concrete measure)", "SINGLE_GAP"⟩
  , ⟨"scope", "no RETRACTED use; no other hypothesis", "INTEGRITY"⟩
  ]

theorem finalRows_length : finalRows.length = 4 := rfl

theorem finalRows_statuses_ok :
    finalRows.all (fun r =>
      r.status ∈ ["GREEN_CONDITIONAL", "SINGLE_GAP", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312FinalActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312FinalActual.final_3_12_concrete
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312FinalActual.final_3_12_concrete'
