import tmp.sheaf.xif.paper.S2500CategoricalOtriangleActual
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralMonoid
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidCards
import Mathlib.NumberTheory.Padics.Complex

/-! # S2505: the actual additive `rho` on `O^◃` from the p-adic norm

`O^◃ = LocalIntegralMonoid p` is the nonzero integral-closure monoid of
`AlgebraicClosure ℚ_[p]`.  The ambient norm on `AlgebraicClosure ℚ_[p]` is the
unique extension of the p-adic norm (`PadicAlgCl.normedField`).  We define the
actual realified map

  `S2505Rho p x = Real.log ‖x‖`

on `O^◃`, prove `S2505Rho p 1 = 0` and
`S2505Rho p (x * y) = S2505Rho p x + S2505Rho p y`, and show that its
restriction to the unit group `O^▷ = (O^◃)ˣ` is identically zero.  The unit
group is the ring-unit group of `O^◃`; a unit and its inverse both lie in
`O^◃`, hence both have norm at most one, so the unit has norm one and its
log-norm is zero.

The unit-level `rho_v` restriction is therefore actual and zero; it is
packaged as `S2505RhoVUnitRestriction`.  The remaining exact missing datum is
the universal-covering pro-system with its `O^▷` pro-generators
(`S2500UniversalCoverRequired p`); no inhabitant is asserted here.  For any
such cover, the realified value of the chosen generator is not extra numerical
data: it is forced to be the actual log-norm of the generator's image in
`O^◃`, see `S2505GeneratorRho`.  S2490 records that a carrier-only
construction of the pro-generator layer is impossible. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual

namespace LeanFormal.IUT.XiFPaper.S2505RhoVActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The actual realified logarithmic norm on `O^◃`. -/
noncomputable def S2505Rho (x : S2500ODiamond p) : ℝ :=
  Real.log
    ‖(LocalIntegralMonoid.toAlgebraicClosureUnits p x :
      AlgebraicClosure ℚ_[p])‖

/-- The actual `rho` sends the identity to zero. -/
theorem S2505Rho_one : S2505Rho p 1 = 0 := by
  simp only [S2505Rho]
  rw [map_one]
  simp

/-- The actual `rho` is additive: it is the logarithm of a multiplicative
norm. -/
theorem S2505Rho_mul (x y : S2500ODiamond p) :
    S2505Rho p (x * y) = S2505Rho p x + S2505Rho p y := by
  simp only [S2505Rho]
  rw [map_mul, Units.val_mul, norm_mul]
  exact Real.log_mul
    (norm_ne_zero_iff.mpr
      (Units.ne_zero (LocalIntegralMonoid.toAlgebraicClosureUnits p x)))
    (norm_ne_zero_iff.mpr
      (Units.ne_zero (LocalIntegralMonoid.toAlgebraicClosureUnits p y)))

/-- The actual `rho` is nonpositive on `O^◃`: every integral-closure element
has p-adic norm at most one. -/
theorem S2505Rho_nonpos (x : S2500ODiamond p) : S2505Rho p x ≤ 0 := by
  have hnorm :
      ‖(LocalIntegralMonoid.toAlgebraicClosureUnits p x :
        AlgebraicClosure ℚ_[p])‖ ≤ 1 := by
    simpa [LocalIntegralMonoid.toAlgebraicClosureUnits] using
      localAlgebraicInteger_norm_le_one p x.1
  simp only [S2505Rho]
  exact Real.log_nonpos (norm_nonneg _) hnorm

/-- The actual restriction of `S2505Rho` to the unit group `O^▷`. -/
noncomputable def S2505RhoOnUnits (u : S2500OTriangle p) : ℝ :=
  S2505Rho p (u : S2500ODiamond p)

/-- The unit restriction sends the identity to zero. -/
theorem S2505RhoOnUnits_one : S2505RhoOnUnits p 1 = 0 := by
  simp only [S2505RhoOnUnits, Units.val_one]
  exact S2505Rho_one p

/-- The unit restriction is additive. -/
theorem S2505RhoOnUnits_mul (u v : S2500OTriangle p) :
    S2505RhoOnUnits p (u * v) =
      S2505RhoOnUnits p u + S2505RhoOnUnits p v := by
  simp only [S2505RhoOnUnits, Units.val_mul]
  exact S2505Rho_mul p (u : S2500ODiamond p) (v : S2500ODiamond p)

/-- Every `O^▷` unit has `rho`-value zero.  A unit and its inverse both lie
in the integral-closure monoid, so both have norm at most one; multiplicativity
of the norm then forces the unit norm to be exactly one. -/
theorem S2505RhoOnUnits_eq_zero (u : S2500OTriangle p) :
    S2505RhoOnUnits p u = 0 := by
  have hsum :
      S2505Rho p (u : S2500ODiamond p) +
        S2505Rho p ((u⁻¹ : S2500OTriangle p) : S2500ODiamond p) = 0 := by
    have hone :
        (u : S2500ODiamond p) *
            ((u⁻¹ : S2500OTriangle p) : S2500ODiamond p) = 1 := by
      simpa using congrArg
        (fun v : S2500OTriangle p => (v : S2500ODiamond p))
        (mul_inv_cancel u)
    have h := S2505Rho_mul p (u : S2500ODiamond p)
      ((u⁻¹ : S2500OTriangle p) : S2500ODiamond p)
    rw [hone, S2505Rho_one p] at h
    exact h.symm
  have hu : S2505Rho p (u : S2500ODiamond p) ≤ 0 :=
    S2505Rho_nonpos p _
  have hu' :
      S2505Rho p ((u⁻¹ : S2500OTriangle p) : S2500ODiamond p) ≤ 0 :=
    S2505Rho_nonpos p _
  have ha0 : 0 ≤ S2505Rho p (u : S2500ODiamond p) := by
    have hneg :
        S2505Rho p (u : S2500ODiamond p) =
          -S2505Rho p ((u⁻¹ : S2500OTriangle p) : S2500ODiamond p) :=
      eq_neg_of_add_eq_zero_left hsum
    rw [hneg]
    exact neg_nonneg.mpr hu'
  change S2505Rho p (u : S2500ODiamond p) = 0
  exact le_antisymm hu ha0

/-- The actual unit-level `rho_v`: the restriction of the log-norm map to
`O^▷`.  It is the genuine restriction of `S2505Rho`, not a fabricated
placeholder, and it is identically zero.  This inhabits only the unit-level
half of the S2500 `rho_v` specification; the pro-generator values require the
still-missing universal cover. -/
noncomputable def S2505RhoVUnitRestriction : S2500RhoVRequired p where
  rho := S2505RhoOnUnits p
  rho_one := S2505RhoOnUnits_one p
  rho_mul := S2505RhoOnUnits_mul p

/-- Conditional generator value of the missing `rho_v` layer.  Given a
universal cover with a chosen `O^▷` pro-generator
(`S2500UniversalCoverRequired p`, which is exact missing), the realified
generator value is forced by the actual `O^◃` `rho` of its image.  No
inhabitant of the cover is asserted in this file. -/
noncomputable def S2505GeneratorRho
    (cover : S2500UniversalCoverRequired p) (i : cover.proSystem.Index) : ℝ :=
  S2505Rho p (cover.toODiamond i (cover.oTriangleGenerator i))

end LeanFormal.IUT.XiFPaper.S2505RhoVActual
end
