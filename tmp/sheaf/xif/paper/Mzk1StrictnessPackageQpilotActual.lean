/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1OneDimStrictQpilotActual
import tmp.sheaf.xif.paper.Mzk1ProductStrictQpilotActual
import Mathlib.Tactic

/-! # Mzk1StrictnessPackageQpilotActual — 1D + product strictness package

A586/A578 (qpilot lane): one package bundling the 1D ball strictness and the
finite-product strictness lemmas used for strict Haar increase. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictnessPackageQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1OneDimStrictQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ProductStrictQpilotActual
open MeasureTheory
open scoped ENNReal
open scoped NNReal

/-- The strictness package: 1D subset/measure strictness and product strictness. -/
structure StrictnessPackage where
  /-- 1D proper-subset strictness. -/
  oneDimStrict : ∀ {r R : Real}, 0 ≤ r → r < R →
    Metric.closedBall (0 : Real) r ⊂ Metric.closedBall (0 : Real) R
  /-- 1D strict measure increase. -/
  oneDimVolume : ∀ {r R : Real}, 0 ≤ r → r < R →
    volume (Metric.closedBall (0 : Real) r) < volume (Metric.closedBall (0 : Real) R)
  /-- product strictness in NNReal. -/
  prodStrict : ∀ {ι : Type} [Fintype ι] (f g : ι → ℝ≥0),
    (∀ i, 0 < f i) → (∀ i, f i ≤ g i) →
    ∀ (i0 : ι), f i0 < g i0 → (∏ i, f i) < ∏ i, g i

/-- The constructed strictness package. -/
noncomputable def strictnessPackage : StrictnessPackage where
  oneDimStrict := fun {r R} hr hrR => oneDim_strict_subset hr hrR
  oneDimVolume := fun {r R} hr hrR => oneDim_volume_strict hr hrR
  prodStrict := fun {ι} _inst f g hpos hle i0 hlt =>
    nnreal_prod_strict f g hpos hle i0 hlt

#check strictnessPackage

end LeanFormal.IUT.XiFPaper.Mzk1StrictnessPackageQpilotActual
end
