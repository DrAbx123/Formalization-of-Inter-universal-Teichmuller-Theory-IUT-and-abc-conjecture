/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-! # P0-L: product-space normalized readout (mirrors s1915 hull factorization)

Uses `rootExtensionProductHaar` (product space), not the tensor `addHaar`:
`thetaNormReadProduct := log(hullMass) - log(unitMass)`, so the (unknown) tensor-map
scaling constant cancels in the normalized ratio.  `s1915_hull_measure_eq` gives
`hullMass = prod (r_b^{d_b}) * unitMass`, hence
`thetaNormReadProduct = sum_b d_b log r_b` and `= s1915ClosedForm - 1`.
`unitMass = 1` is NOT assumed. -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutProductActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Product-space normalized theta readout: log(hull mass) - log(unit mass). -/
noncomputable def thetaNormReadProduct : Real :=
  Real.log (s1915HullMass T).toReal - Real.log (s1915UnitMass T).toReal

/-- Product factorization: the normalized readout is the sum of degree-weighted log radii. -/
theorem thetaNormReadProduct_eq_sum :
    thetaNormReadProduct (T := T) =
      ∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) := by
  have hH : (s1915HullMass T).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (s1915_hullMass_pos T))
      (ne_of_lt (s1915_hullMass_lt_top T)))
  have hU : (s1915UnitMass T).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (s1915_unitMass_pos T))
      (ne_of_lt (s1915_unitMass_lt_top T)))
  have hprod : (∏ b : Bad (nativePlaceSelection T),
      (rootImageRadius T b : Real) ^ s1915LocalDegree T b) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    exact pow_ne_zero _ (ne_of_gt (s1915_rootImageRadius_pos T b))
  unfold thetaNormReadProduct
  rw [s1915_hull_toReal, Real.log_mul hprod hU]
  rw [s1915_log_prod_radius]
  ring

/-- The normalized readout is the S1915 closed form minus one. -/
theorem thetaNormReadProduct_eq_closedForm_sub_one :
    thetaNormReadProduct (T := T) = s1915ClosedForm T - 1 := by
  have hU : (s1915UnitMass T).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (s1915_unitMass_pos T))
      (ne_of_lt (s1915_unitMass_lt_top T)))
  have hHnon : (s1915HullMass T).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (s1915_hullMass_pos T))
      (ne_of_lt (s1915_hullMass_lt_top T)))
  have hnorm := s1915_log_normalized_hull (T := T)
  rw [s1915_normalized_hull_toReal] at hnorm
  have hA : Real.exp 1 / (s1915UnitMass T).toReal ≠ 0 := by
    apply div_ne_zero (Real.exp_ne_zero 1) hU
  rw [Real.log_mul hA hHnon] at hnorm
  rw [Real.log_div (Real.exp_ne_zero 1) hU, Real.log_exp] at hnorm
  simp only [thetaNormReadProduct, s1915ClosedForm] at hnorm ⊢
  linarith

/-- The normalized readout in terms of the normalized coefficients and `log P`. -/
theorem thetaNormReadProduct_eq_neg_sum_coefficient :
    thetaNormReadProduct (T := T) =
      ∑ b : Bad (nativePlaceSelection T),
        -(((s1915LocalDegree T b : Real) * qVFamNormalizedCoefficient (T := T) (b := b)) /
          (2 * (l.value : Real))) * Real.log (qVFamTensorP (T := T) (b := b) : Real) := by
  rw [thetaNormReadProduct_eq_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [rootImageRadius_eq_rootNorm]
  rw [rootNormedElementNorm_eq_p_rpow]
  have hlog : Real.log
      ((qVFamTensorP (T := T) (b := b) : Real).rpow
        (-(qVFamNormalizedCoefficient (T := T) (b := b)) / (2 * (l.value : Real)))) =
      (-(qVFamNormalizedCoefficient (T := T) (b := b)) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP (T := T) (b := b) : Real) := by
    simpa using Real.log_rpow
      (x := (qVFamTensorP (T := T) (b := b) : Real))
      (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP (T := T) (b := b))).pos)
      (-(qVFamNormalizedCoefficient (T := T) (b := b)) / (2 * (l.value : Real)))
  rw [hlog]
  ring

/-- **Object-mismatch condition**: the L carrier is a single-place/local tensor object,
while `thetaNormReadProduct` is the global sum over `Bad (nativePlaceSelection T)`.
Relating them needs (i) an identification of the arithmetic data and (ii) a
`Bad`-index <-> `tensorIndex` correspondence; neither is in the tree. -/
structure LGlobalLocalObjectLock where
  bad_set_finite : Fintype (Bad (nativePlaceSelection T))
  single_place : Prop
  local_eq_global_restriction : single_place

def lNormGlobalLocalObjectLockGap : Prop := Nonempty (LGlobalLocalObjectLock (T := T))

def lNormProductRows : List (String × String × String) :=
  [ ("thetaNormReadProduct", "log(hullMass) - log(unitMass) (product space)", "DEFINED"),
    ("thetaNormReadProduct_eq_sum", "= sum d_b log r_b", "PROVED"),
    ("thetaNormReadProduct_eq_closedForm_sub_one", "= s1915ClosedForm - 1", "PROVED"),
    ("thetaNormReadProduct_eq_neg_sum_coefficient", "= sum -(d_b c_norm_b)/(2l) log P_b (S709/S305)", "PROVED"),
    ("LGlobalLocalObjectLock", "global Bad-sum vs single-place L tensor object", "EXPLICIT OBJECT-MISMATCH GAP"),
    ("unitMass = 1", "NOT assumed (GAP record)", "NOT CLAIMED") ]

theorem lNormProductRows_length : lNormProductRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutProductActual

end