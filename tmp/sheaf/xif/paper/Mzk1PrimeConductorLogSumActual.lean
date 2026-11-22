/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorUnconditionalActual
import tmp.sheaf.xif.paper.Mzk1DExactActual
import tmp.sheaf.xif.paper.Mzk1SSIneqExplicitFormActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import Mathlib.Tactic

/-! # GAP-PC-LOGSUM: `log C.p ≤ ∑_b |log q_b|` reduced to order positivity

Green inputs:
* `baseQLogMagnitude_eq_order_mul_log` (`BaseQLogVolumeActual`): each local
  magnitude is `order_b · log (residueNormBase (nativeBaseSectionPlace T b))`;
* `baseQ_order_pos`: every actual order is positive;
* `nativeBadLocalWeight_eq_one_of_localCompletionDegree_one` (task-118).

Remaining named input: **GAP-PC-RESNORM** — the actual residue norms at the bad
section places all equal the prime conductor `C.p`.  In the prime-conductor tame
case this is the residue-degree-one statement at each bad place (not constructed).
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorLogSumActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorUnconditionalActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **GAP-PC-RESNORM input**: every actual bad section place has residue norm
equal to the prime conductor.  This is the residue-degree-one statement at the bad
places (not constructed in the tree). -/
def PrimeConductorResidueNormData (C : PrimeConductorCurve) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    residueNormBase (nativeBaseSectionPlace T b) = (C.p : ℝ)

/-- Sum of the actual base-q log magnitudes, under GAP-PC-RESNORM. -/
theorem sum_baseQLogMagnitude_eq (C : PrimeConductorCurve)
    (hres : PrimeConductorResidueNormData T C) :
    (∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b) =
      (∑ b : Bad (nativePlaceSelection T), ((baseQ T b).order : ℝ)) *
        Real.log (C.p : ℝ) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [baseQLogMagnitude_eq_order_mul_log, hres b]

/-- **GAP-PC-LOGSUM (conditional on GAP-PC-RESNORM)**:
`log C.p ≤ ∑_b |log q_b|`.  Uses: nonempty bad set, positive order at every bad
place, and `log C.p ≥ 0`. -/
theorem log_le_sum_baseQLogMagnitude (C : PrimeConductorCurve)
    [Nonempty (Bad (nativePlaceSelection T))]
    (hres : PrimeConductorResidueNormData T C)
    (hlogp : 0 ≤ Real.log (C.p : ℝ)) :
    Real.log (C.p : ℝ) ≤ ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := by
  rw [sum_baseQLogMagnitude_eq T C hres]
  have hcard_pos : 0 < Fintype.card (Bad (nativePlaceSelection T)) := Fintype.card_pos
  have hcard : (1 : ℝ) ≤ (Fintype.card (Bad (nativePlaceSelection T)) : ℝ) := by
    exact_mod_cast hcard_pos
  have hsum_ge_card :
      (Fintype.card (Bad (nativePlaceSelection T)) : ℝ) ≤
        ∑ b : Bad (nativePlaceSelection T), ((baseQ T b).order : ℝ) := by
    calc (Fintype.card (Bad (nativePlaceSelection T)) : ℝ)
        = ∑ _b : Bad (nativePlaceSelection T), (1 : ℝ) := by simp
      _ ≤ ∑ b : Bad (nativePlaceSelection T), ((baseQ T b).order : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro b _
          exact_mod_cast (Nat.succ_le_of_lt (baseQ_order_pos T b))
  have hsum_ge_one :
      (1 : ℝ) ≤ ∑ b : Bad (nativePlaceSelection T), ((baseQ T b).order : ℝ) :=
    le_trans hcard hsum_ge_card
  calc Real.log (C.p : ℝ) = 1 * Real.log (C.p : ℝ) := by ring
    _ ≤ (∑ b : Bad (nativePlaceSelection T), ((baseQ T b).order : ℝ)) *
          Real.log (C.p : ℝ) :=
        mul_le_mul_of_nonneg_right hsum_ge_one hlogp

/-- **LOGSUM discharged inside task-118**: actual D_exact L7 with GAP-PC-LOGSUM
replaced by GAP-PC-RESNORM (and order positivity automatic). -/
theorem nativeDExact_L7_of_residueNorm
    (C : PrimeConductorCurve) (lR arch : ℝ) (hl1 : 1 ≤ lR)
    [Nonempty (Bad (nativePlaceSelection T))]
    (hres : PrimeConductorResidueNormData T C)
    (hlogp : 0 ≤ Real.log (C.p : ℝ))
    (hweight : ∀ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b = 1)
    (harch : 0 ≤ arch) :
    DExactLowerTarget C lR (nativeDExact T arch) :=
  nativeDExact_L7_of_conditions T C lR arch hl1 hweight
    (log_le_sum_baseQLogMagnitude T C hres hlogp) harch

/-- Prime-conductor SSIneqExplicit with both content inputs now explicit:
GAP-PC-WEIGHT (hweight) and GAP-PC-RESNORM (hres). -/
theorem primeConductor_ssIneqExplicit_of_actual_residueNorm
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (lR arch : ℝ) (hl : 11 ≤ lR)
    (hlogp : 0 ≤ Real.log (C.p : ℝ))
    [Nonempty (Bad (nativePlaceSelection T))]
    (hres : PrimeConductorResidueNormData T C)
    (hweight : ∀ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b = 1)
    (harch : 0 ≤ arch) :
    SSIneqExplicit (sL lR) ((C.e : ℝ) * Real.log (C.p : ℝ)) lR
      (((lR + 5) / 4) * (nativeDExact T arch)) :=
  primeConductor_ssIneqExplicit_of_actual T hMO C lR arch hl hlogp hweight
    (log_le_sum_baseQLogMagnitude T C hres hlogp) harch

/-- Status rows. -/
def logSumRows : List (String × String × String) :=
  [ ("sum_baseQLogMagnitude_eq", "sum |log q_b| = (sum order_b) * log C.p", "PROVED (given GAP-PC-RESNORM)"),
    ("log_le_sum_baseQLogMagnitude", "log C.p <= sum |log q_b|", "PROVED (given GAP-PC-RESNORM, nonempty, log>=0)"),
    ("nativeDExact_L7_of_residueNorm", "actual D_exact L7 with GAP-PC-LOGSUM discharged", "PROVED (conditional on GAP-PC-WEIGHT + GAP-PC-RESNORM)"),
    ("primeConductor_ssIneqExplicit_of_actual_residueNorm", "SSIneqExplicit with explicit content inputs", "PROVED (conditional)"),
    ("PrimeConductorResidueNormData", "all bad section places have residue norm C.p", "GAP-PC-RESNORM (content input)"),
    ("baseQ_order_pos", "order_b > 0 for every b", "PROVED (existing)"),
    ("bad set nonempty", "[Nonempty (Bad ...)]", "input instance") ]

theorem logSumRows_length : logSumRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorLogSumActual

end
