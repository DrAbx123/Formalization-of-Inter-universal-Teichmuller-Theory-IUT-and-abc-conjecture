/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DExactActual
import tmp.sheaf.xif.paper.Mzk1DExactFromHullActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import tmp.sheaf.xif.paper.Mzk1ThetaDataLegalityActual
import tmp.sheaf.xif.paper.Mzk1DExactLowerActual
import Mathlib.Tactic

/-! # task-118: prime-conductor L7 (hD) reduction to actual D_exact content

Green inputs: `Mzk1PrimeConductorRouteActual` (paperGap skeleton, external
Mestre–Oesterlé as an explicit Prop parameter), `Mzk1DExactActual.nativeDExact`
(actual weighted base-q log-magnitude + arch), `Mzk1DExactFromHullActual`
(per-place and global L7 tools).

We replace the abstract hypothesis `hD : D_exact ≥ (1-1/l)·log p` by a theorem
about the **actual** `nativeDExact`, conditional on two content-level inputs:

* GAP-PC-WEIGHT: each actual native local weight is `1` (completion degree 1,
  expected in the prime-conductor tame case; not constructed here);
* GAP-PC-LOGSUM: `log p ≤ ∑_b |log q_b|` (sum of actual base-q log magnitudes;
  not constructed here).

`MestreOesterleBound` remains an explicit external published-theorem parameter
(not an axiom, not proved in this project).  No sorry/axiom.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorUnconditionalActual

open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactFromHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Unit weight when the actual completion degree is one (prime-conductor tame
case).  `nativeBadLocalWeight_eq_inv` is `rfl` in the actual definitions. -/
theorem nativeBadLocalWeight_eq_one_of_localCompletionDegree_one
    (b : Bad (nativePlaceSelection T))
    (hdeg : localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 1) :
    nativeBadLocalWeight T b = 1 := by
  rw [nativeBadLocalWeight_eq_inv T b, hdeg]
  norm_num

/-- **L7 for the actual D_exact**: `(1-1/l)·log p ≤ nativeDExact T arch`,
reduced to content-level inputs (GAP-PC-WEIGHT, GAP-PC-LOGSUM) and `arch ≥ 0`. -/
theorem nativeDExact_L7_of_conditions
    (C : PrimeConductorCurve) (lR arch : ℝ) (hl1 : 1 ≤ lR)
    (hweight : ∀ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b = 1)
    (hlogsum : Real.log (C.p : ℝ) ≤
      ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b)
    (harch : 0 ≤ arch) :
    DExactLowerTarget C lR (nativeDExact T arch) := by
  unfold DExactLowerTarget
  have hde : nativeDExact T arch =
      (∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b) + arch := by
    rw [nativeDExact_eq_weighted_sum T arch]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [hweight b, one_mul]
  rw [hde]
  have hsum_nonneg : 0 ≤ ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := by
    refine Finset.sum_nonneg ?_
    intro b _
    exact le_of_lt (baseQLogMagnitude_pos T b)
  have hl0 : (0 : ℝ) < lR := by linarith
  have hcoef_nonneg : 0 ≤ 1 - 1 / lR := by
    have h1l : 1 / lR ≤ 1 := by
      rw [div_le_one hl0]
      linarith
    linarith
  have hcoef_le_one : 1 - 1 / lR ≤ 1 := by
    have h1l : 0 ≤ 1 / lR := by positivity
    linarith
  have h1 : (1 - 1 / lR) * Real.log (C.p : ℝ) ≤
      (1 - 1 / lR) * (∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b) :=
    mul_le_mul_of_nonneg_left hlogsum hcoef_nonneg
  have h2 : (1 - 1 / lR) * (∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b) ≤
      1 * (∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b) :=
    mul_le_mul_of_nonneg_right hcoef_le_one hsum_nonneg
  linarith

/-- **Prime-conductor SSIneqExplicit from actual D_exact content**:
only the external Mestre–Oesterlé parameter plus the two named content inputs. -/
theorem primeConductor_ssIneqExplicit_of_actual
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (lR arch : ℝ) (hl : 11 ≤ lR)
    (hlogp : 0 ≤ Real.log (C.p : ℝ))
    (hweight : ∀ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b = 1)
    (hlogsum : Real.log (C.p : ℝ) ≤
      ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b)
    (harch : 0 ≤ arch) :
    SSIneqExplicit (sL lR) ((C.e : ℝ) * Real.log (C.p : ℝ)) lR
      (((lR + 5) / 4) * (nativeDExact T arch)) :=
  paperGap_of_primeConductor hMO C lR hl hlogp (nativeDExact T arch)
    (nativeDExact_L7_of_conditions T C lR arch (by linarith) hweight hlogsum harch)

/-- Status rows. -/
def primeConductorRows : List (String × String × String) :=
  [ ("nativeDExact", "∑_b weight_b·|log q_b| + arch", "DEF (actual)"),
    ("nativeBadLocalWeight_eq_one_of_localCompletionDegree_one", "degree 1 => weight 1", "PROVED (rfl)"),
    ("nativeDExact_L7_of_conditions", "L7 for actual D_exact given GAP-PC-WEIGHT/LOGSUM/arch", "PROVED (conditional)"),
    ("primeConductor_ssIneqExplicit_of_actual", "SSIneqExplicit depends only on external hMO + content gaps", "PROVED (conditional)"),
    ("MestreOesterleBound", "external published theorem as explicit Prop parameter", "EXTERNAL_PARAM (not axiom, not proved)"),
    ("GAP-PC-WEIGHT", "∀ b, nativeBadLocalWeight b = 1 (local completion degree 1)", "GAP (content input)"),
    ("GAP-PC-LOGSUM", "log p <= ∑_b |log q_b| (actual base-q identification)", "GAP (content input)"),
    ("arch", "0 <= arch (nonnegative archimedean addend)", "input hypothesis") ]

theorem primeConductorRows_length : primeConductorRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorUnconditionalActual

end
