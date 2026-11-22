import tmp.sheaf.xif.paper.S3135IUTIVThetaBoundToComparisonActual
import tmp.sheaf.xif.paper.S3135ComparisonAssemblyActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVSection2BridgeActual — IUT IV §1→§2 transfer composites

Genuine new consumers connecting the existing IUT IV §1 (Thm 1.10 display) and
§2 (uniformity/comparison) assets:
* IUTIVSection2Uniformity yields the section-2 uniform display family;
* hence ABCConjecture via the EXIT0 section-2 assembly;
* Thm 1.10 display and its height-bound consequence are packaged together.
No new paper input is proved; named inputs remain named; no closure;
gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135IUTIVThetaBoundToComparisonActual
open LeanFormal.IUT.XiFPaper.S3135ComparisonAssemblyActual

/-- IUT IV §2 uniformity yields the section-2 uniform display family. -/
theorem section2UniformDisplayFamily_of_uniformity
    (hu : IUTIVSection2Uniformity) : IUTIVSection2UniformDisplayFamily := by
  intro eps heps
  obtain ⟨l, dmod, emod, eta, D, W, hl, hd, he, heta, hslope, hconst, hdict, hdisp⟩ :=
    hu eps heps
  refine ⟨l, dmod, emod, eta, D, hl, hd, he, heta, hslope, hconst, ?_⟩
  intro a b c habc
  have h := hdisp a b c habc
  rw [hdict a b c habc] at h
  exact h

/-- ABCConjecture from the section-2 uniformity input (via the EXIT0 assembly). -/
theorem abcConjecture_of_section2Uniformity (hu : IUTIVSection2Uniformity) :
    ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr
    (s3135_ABCHeightWeightAdditiveBoundV2_of_paperInputs hu)

/-- Thm 1.10 display together with its actual height-bound consequence. -/
theorem iutIVTheorem110_display_and_heightBound (l dmod emod eta : ℝ)
    (hl : 5 ≤ l) (hd : 0 ≤ dmod) (he : 1 ≤ emod) (heta : 0 ≤ eta)
    {W : ℕ → ℕ → ℕ → ℝ} {HTheta : ℕ → ℕ → ℕ → ℝ}
    (hW : ∀ a b c : ℕ, 0 ≤ W a b c)
    (hBatchA : IUTIVCor312LowerBound l HTheta)
    (hTheta : IUTIVThetaHullComputation l dmod emod eta W HTheta)
    (hlogq_le : ∀ a b c : ℕ, IsABCTriple a b c → LeanFormal.IUT.XiFPaper.S3135IUTIVThetaBoundToComparisonActual.freyLogQ a b c ≤ l ^ 2)
    (hlogq_pos : ∀ a b c : ℕ, IsABCTriple a b c → 0 < LeanFormal.IUT.XiFPaper.S3135IUTIVThetaBoundToComparisonActual.freyLogQ a b c) :
    IUTIVTheorem110Display l dmod emod eta W ∧
      (∀ a b c : ℕ, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + 20 * dmod / l) * W a b c + 20 * (emod * l + eta) -
            Real.log (27 / 64 : ℝ) / 6) := by
  have hdisp := s3135_display_of_cor312_thetaComputation l dmod emod eta hl hd he heta
    hW hBatchA hTheta hlogq_le hlogq_pos
  exact ⟨hdisp, s3135_heightBound_of_display l dmod emod eta hdisp⟩

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2BridgeActual

end
