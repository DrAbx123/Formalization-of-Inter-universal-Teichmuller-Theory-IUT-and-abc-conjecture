/-
  Two-sided splicing of the rigid Tate series with the integer-indexed Tate coordinates.

  `RigidTateSeries` keeps the four one-sided sums `xPositiveSeries`, `xNegativeSeries`,
  `yPositiveSeries`, `yNegativeSeries` over a rigid parameter `P` and a point `u` of the
  fundamental annulus.  The integer-indexed coordinates `coordinateSeries` and
  `yCoordinateSeries` are split into their positive and negative halves in
  `TateYSeriesTwoSidedSplit.lean`.  This file identifies the terms of the two languages
  at `q = P.q`, `u = u.1` and splices the two-sided integer sums with the four one-sided
  sums:

      coordinateSeries P.q u.1 = xPositiveSeries P u + xNegativeSeries P u
      yCoordinateSeries P.q u.1 = yPositiveSeries P u + yNegativeSeries P u

  Everything is unconditional over a complete non-archimedean field; the contraction
  hypothesis `‖P.q‖ < 1` is carried by the parameter `P` itself, and root's
  `TateYSeriesTwoSidedSplit` supplies the two-sided splits that are consumed here.
-/

import LeanFormal.IUT.Foundations.Geometry.RigidTateSeries
import LeanFormal.IUT.Foundations.Geometry.TateYSeriesTwoSidedSplit
import Mathlib.Tactic

namespace LeanFormal.IUT

universe u

noncomputable section

namespace RigidTate

set_option linter.unusedSectionVars false

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ## Termwise identification of the two kernel languages -/

/-- The rigid x-positive term is the Tate x-kernel at exponent `n`. -/
theorem xPositiveTerm_eq_coordinateKernel (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) :
    xPositiveTerm P u n = TateCurve.coordinateKernel (P.q ^ (n : ℤ) * u.1) := by
  simp only [xPositiveTerm, positiveArgument, TateCurve.coordinateKernel]

/-- The rigid x-negative term is the Tate x-kernel at exponent `-((n : ℤ) + 1)`. -/
theorem xNegativeTerm_eq_coordinateKernel (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) :
    xNegativeTerm P u n = TateCurve.coordinateKernel (P.q ^ (-((n : ℤ) + 1)) * u.1) := by
  have hcast : (-(n + 1 : ℕ) : ℤ) = -((n : ℤ) + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
  simp only [xNegativeTerm, negativeArgument, TateCurve.coordinateKernel]
  rw [hcast]

/-- The rigid y-positive term is the Tate y-kernel at exponent `n`. -/
theorem yPositiveTerm_eq_yCoordinateKernel (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) :
    yPositiveTerm P u n = TateCurve.yCoordinateKernel (P.q ^ (n : ℤ) * u.1) := by
  simp only [yPositiveTerm, positiveArgument, TateCurve.yCoordinateKernel]

/-- The rigid y-negative term is the Tate y-kernel at exponent `-((n : ℤ) + 1)`. -/
theorem yNegativeTerm_eq_yCoordinateKernel (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) :
    yNegativeTerm P u n = TateCurve.yCoordinateKernel (P.q ^ (-((n : ℤ) + 1)) * u.1) := by
  have hcast : (-(n + 1 : ℕ) : ℤ) = -((n : ℤ) + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
  simp only [yNegativeTerm, negativeArgument, TateCurve.yCoordinateKernel]
  rw [hcast]

/-! ## Identification of the one-sided sums with the integer halves -/

/-- The nonnegative half of the integer x-series is `xPositiveSeries`. -/
theorem coordinatePositivePart_eq_xPositiveSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) :
    TateCurve.coordinatePositivePart P.q u.1 = xPositiveSeries P u := by
  simp only [TateCurve.coordinatePositivePart, xPositiveSeries]
  exact tsum_congr fun n => (xPositiveTerm_eq_coordinateKernel P u n).symm

/-- The negative half of the integer x-series is `xNegativeSeries`. -/
theorem coordinateNegativePart_eq_xNegativeSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) :
    TateCurve.coordinateNegativePart P.q u.1 = xNegativeSeries P u := by
  simp only [TateCurve.coordinateNegativePart, xNegativeSeries]
  exact tsum_congr fun n => (xNegativeTerm_eq_coordinateKernel P u n).symm

/-- The nonnegative half of the integer y-series is `yPositiveSeries`. -/
theorem yPositivePart_eq_yPositiveSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) :
    TateCurve.yPositivePart P.q u.1 = yPositiveSeries P u := by
  simp only [TateCurve.yPositivePart, yPositiveSeries]
  exact tsum_congr fun n => (yPositiveTerm_eq_yCoordinateKernel P u n).symm

/-- The negative half of the integer y-series is `yNegativeSeries`. -/
theorem yNegativePart_eq_yNegativeSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) :
    TateCurve.yNegativePart P.q u.1 = yNegativeSeries P u := by
  simp only [TateCurve.yNegativePart, yNegativeSeries]
  exact tsum_congr fun n => (yNegativeTerm_eq_yCoordinateKernel P u n).symm

/-! ## The spliced two-sided decompositions -/

/-- Two-sided decomposition of the integer-indexed Tate x-coordinate at a point of the
rigid fundamental annulus: the integer `ℤ`-series is the sum of the two one-sided
`RigidTateSeries` halves. -/
theorem coordinateSeries_eq_xPositiveSeries_add_xNegativeSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) :
    TateCurve.coordinateSeries P.q u.1 = xPositiveSeries P u + xNegativeSeries P u := by
  rw [TateCurve.coordinateSeries_eq_coordinatePositivePart_add_coordinateNegativePart
    P.q_norm_lt_one u.1,
    coordinatePositivePart_eq_xPositiveSeries P u,
    coordinateNegativePart_eq_xNegativeSeries P u]

/-- Two-sided decomposition of the integer-indexed Tate y-coordinate at a point of the
rigid fundamental annulus: the integer `ℤ`-series is the sum of the two one-sided
`RigidTateSeries` halves. -/
theorem yCoordinateSeries_eq_yPositiveSeries_add_yNegativeSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) :
    TateCurve.yCoordinateSeries P.q u.1 = yPositiveSeries P u + yNegativeSeries P u := by
  rw [TateCurve.yCoordinateSeries_eq_yPositivePart_add_yNegativePart
    P.q_norm_lt_one u.1,
    yPositivePart_eq_yPositiveSeries P u,
    yNegativePart_eq_yNegativeSeries P u]

end RigidTate

end

end LeanFormal.IUT
