import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesReductionShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesHeightWeightShaActual

-- AUDIT A612 WARNING: reexported height-model equivalence assumes logVolume := arithmeticWeight;
-- it does not narrow the real paper HeightEstimate (region log-volume). See
-- Mzk1ABCTwoEstimatesAuditCorrectionShaActual for the honest interface.

/-!
# shehdd A611 two-estimates thin re-export (Sha)

Thin re-exports of the A596/A606 two-estimates reduction interface and the
A611 substantive height-estimate lemmas.  Canonical names are mainline-exclusive;
this file uses the shehdd `Sha` suffix.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesThinReexportShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightWeightShaActual

theorem reexport_abc_of_reductions (R : ABCTwoEstimatesReductions) :
    ABCConjecture :=
  abc_of_reductions R

theorem reexport_heightBound_of_reductions (R : ABCTwoEstimatesReductions) :
    ABCFormAdditiveHeightBound :=
  abc_of_reductions_heightBound R

theorem reexport_height_estimate_of_height_bound
    (hheight : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ arithmeticWeight (abcRationalPoint a c)) :
    ∀ δ : Real, 0 < δ → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + δ) * arithmeticWeight (abcRationalPoint a c) :=
  height_estimate_of_height_bound_of_triples hheight

theorem reexport_height_estimate_iff_weight {h w : Real} (hw : 0 < w) :
    (∀ δ : Real, 0 < δ → h ≤ (1 + δ) * w) ↔ h ≤ w :=
  height_estimate_iff_weight_bound hw

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesThinReexportShaActual
