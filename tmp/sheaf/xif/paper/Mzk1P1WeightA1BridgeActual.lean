/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1RootRadiusBridgeActual
import tmp.sheaf.xif.paper.Mzk1A1DeltaExplicitActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import Mathlib.Tactic

/-! # P1 #1: weight clarification and exact `a1Delta` expansion

**`localCompletionDegree` is the total local degree** `[K_w : F_v]`
(`Module.finrank` of `completionAlgebra`), i.e. `e * f` — not merely `f`.
Hence `nativeBadLocalWeight = 1/[K_w : F_v]` (paper normalized weight).
`s1915LocalDegree = [L_b : Q_p] = finrank(rootNormedExtension)` is a different degree;
the relation is the degree tower (`Module.finrank_mul_finrank`) with the root degree
`n_b` as the remaining factor. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1WeightA1BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1A1DeltaExplicitActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1RootRadiusBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-! ### (1) weight: `1/[K_w : F_v]`, and the distinction from `d_b`. -/

/-- The paper weight is the inverse of the **total** local completion degree
`[K_w : F_v]` (`e * f`). -/
theorem nativeBadLocalWeight_eq_inv_total_local_degree :
    nativeBadLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  nativeBadLocalWeight_eq_inv T b

/-- `s1915LocalDegree` is the `Q_p`-degree of the root normed extension (a different
degree from the local completion degree; cf. degree tower). -/
theorem s1915LocalDegree_eq_finrank :
    s1915LocalDegree T b =
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) := rfl

/-! ### (2) exact `a1Delta` expansion via the log-radius dictionary. -/

/-- `a1Delta = log(r) - (1/d)*(log mu(q) - log mu(O))`, with `log r` given by the
normalized coefficient. -/
theorem a1Delta_eq_neg_coefficient_logP_sub_signed
    (hd : 0 < s1915LocalDegree T b) :
    a1Delta (T := T) (b := b) =
      -((qVFamNormalizedCoefficient T b / (2 * (l.value : Real))) *
          Real.log (qVFamTensorP T b : Real)) -
        (1 / (s1915LocalDegree T b : Real)) *
          (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
            Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) := by
  rw [a1Delta_eq_log_radius_sub_signedTerm]
  unfold a1SignedTerm
  rw [log_rootImageRadius_eq_neg_coefficient_mul_logP]

/-- **Conditional** weight conversion: given the explicit degree identification
`[F_v : Q_p] = [K_w : F_v]` (i.e. `localCompletionDegree = qVFamTensorRationalDegree`),
`d_b * weight = [L : F_v] = finrank (rootBase) L`.  This is NOT derivable from the
finrank tower alone: `rootBase = NormalizedCompletion (qVFamTensorPlace)` is an
`F_v`-completion, while `weight = 1/[K_w : F_v]` is a `K_w`-degree. -/
theorem weight_conversion_cond
    (hdF : Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) =
      localCompletionDegree T.arithmetic (nativeBadToKPlace T b))
    (hdpos : 0 < Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b)) :
    (s1915LocalDegree T b : Real) * nativeBadLocalWeight T b =
      (Module.finrank (rootBase T b) (rootNormedExtension T b) : Real) := by
  have hmul := Module.finrank_mul_finrank
    ℚ_[(qVFamTensorP T b)] (rootBase T b) (rootNormedExtension T b)
  have hcast : (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : Real) =
      (Module.finrank (rootBase T b) (rootNormedExtension T b) : Real) *
        ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) : Nat) : Real) := by
    exact_mod_cast (hmul.symm.trans (Nat.mul_comm _ _))
  have hbase : ((Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) : Nat) : Real) =
      (localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Real) := by
    exact_mod_cast hdF
  have hbne : (localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Real) ≠ 0 := by
    rw [← hbase]
    exact_mod_cast ne_of_gt hdpos
  rw [s1915LocalDegree_eq_finrank, nativeBadLocalWeight_eq_inv_total_local_degree]
  rw [hcast, hbase]
  field_simp [hbne]

def weightA1Rows : List (String × String × String) :=
  [ ("nativeBadLocalWeight_eq_inv_total_local_degree", "paper weight = 1/[K_w:F_v] (e*f)", "PROVED (rfl)"),
    ("s1915LocalDegree_eq_finrank", "d_b = finrank_Qp(rootNormedExtension)", "PROVED (rfl)"),
    ("a1Delta_eq_neg_coefficient_logP_sub_signed", "a1Delta expansion via log r", "PROVED (conditional hd)") ]

theorem weightA1Rows_length : weightA1Rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1WeightA1BridgeActual

end