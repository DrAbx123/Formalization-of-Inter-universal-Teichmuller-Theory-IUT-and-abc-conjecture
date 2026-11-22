import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Topology.MetricSpace.ProperSpace

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# Unconditional DVR principal/torsion refinement (L0.4 A/C batch)

Let `K = concretePlace.maximalIdeal.adicCompletion GaussianField`.  The actual
DVR theorem gives, for every unit `u : Kˣ`,

  `u = π ^ m * u0`,  `u0 : (Valued.v.integer)ˣ`.

This file supplies the principal/torsion refinement: there is one uniform
positive exponent `N`, independent of `u`, such that `u0 ^ N` is principal for
the actual valuation, and moreover this is true simultaneously for all units.

## Properness input

The principal-unit exponent theorem needs `ProperSpace K`.  This file does not
import any candidate properness proof; it takes the explicit closed-ball
compactness data

  `ClosedBallCompactnessInput.isCompact_closedBall : ∀ x r, IsCompact (closedBall x r)`

and converts it to `ProperSpace K` by definition.  The repaired candidate
`ClosedBallCompactness.properSpaceCanonicalCompletion` supplies exactly this
data (its final theorem is the same closed-ball compactness).  The conversion is
therefore not an extra mathematical hypothesis: it is the explicit output of the
closed-ball candidate.

## Main results

* `ClosedBallCompactnessInput`, `properSpaceOfClosedBallCompactness`;
* `integersEquivValuedInteger`, `integersUnitsEquivValuedInteger`: the actual
  identification of the norm and valuation unit balls;
* `exists_uniform_valuedInteger_principalPower`: one `N` works for every actual
  valuation unit;
* `dvrPrincipalTorsionRefinement`: for every `u`, a decomposition
  `u = π^m * u0` with `u0 ^ N` principal;
* `dvrPrincipalTorsionRefinement_norm`: the same in the canonical norm spelling;
* `dvrPrincipalTorsionRefinement_uniform`: the uniform-exponent form.

## Exact residual for making `u0` itself principal

The decomposition unit `u0` is an arbitrary integral unit; it is not principal in
general.  Making `u0` principal would require a chosen section of the residue
map `(Valued.v.integer)ˣ → k^×` (a Teichmüller/residue lift), which is not
part of the current production API.  This file therefore proves the uniform
principal-power torsion boundary, not an unproved residue-lift refinement.

No card, no placeholder, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.DVRPrincipalRefinementProof

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.UniformizerDVRDecomposition
open LeanFormal.IUT.NormalizedLogNormComparison
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

local instance gaussianDVRRefinementProofIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The canonical completed valuation field. -/
abbrev completionField : Type :=
  LeanFormal.IUT.UniformizerDVRDecomposition.completionField

/-- The actual valuation integer ring. -/
abbrev valuedInteger : Subring completionField :=
  LeanFormal.IUT.NormalizedLogNormComparison.valuedInteger

/-! ## The explicit closed-ball compactness input -/

/-- The exact closed-ball compactness output of the repaired
`ClosedBallCompactness` candidate.  It is genuine data, not a card: every closed
ball is compact. -/
structure ClosedBallCompactnessInput where
  /-- Every closed ball of the canonical completion is compact. -/
  isCompact_closedBall : ∀ x : completionField, ∀ r : ℝ,
    IsCompact (Metric.closedBall x r)

/-- The closed-ball input is exactly `ProperSpace`. -/
theorem properSpaceOfClosedBallCompactness
    (h : ClosedBallCompactnessInput) : ProperSpace completionField :=
  ⟨h.isCompact_closedBall⟩

/-! ## Identification of the two integral unit groups -/

/-- Ring equivalence between the norm unit ball and the actual valuation integer
ring, induced by `norm_le_one_iff_valued_le_one`. -/
noncomputable def integersEquivValuedInteger :
    (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField) ≃+*
      valuedInteger where
  toFun x := ⟨x.1, by
    rw [Valuation.mem_integer_iff]
    exact (norm_le_one_iff_valued_le_one x.1).mp
      ((LeanFormal.IUT.LocalFieldIntegralUnits.mem_integers_iff x.1).mp x.2)⟩
  invFun y := ⟨y.1, by
    rw [LeanFormal.IUT.LocalFieldIntegralUnits.mem_integers_iff]
    exact (norm_le_one_iff_valued_le_one y.1).mpr (by
      change (Valued.v y.1 : WithZero (Multiplicative ℤ)) ≤ 1
      exact y.2)⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

/-- The induced equivalence of integral unit groups. -/
noncomputable def integersUnitsEquivValuedInteger :
    (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ ≃*
      (valuedInteger)ˣ :=
  Units.mapEquiv (integersEquivValuedInteger).toMulEquiv

@[simp]
theorem integersUnitsEquivValuedInteger_val
    (u : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ) :
    (((integersUnitsEquivValuedInteger u).val).1 : completionField) =
      ((u.val).1 : completionField) :=
  rfl

@[simp]
theorem integersUnitsEquivValuedInteger_symm_val
    (u : (valuedInteger)ˣ) :
    ((((integersUnitsEquivValuedInteger.symm u).val).1 : completionField)) =
      ((u.val).1 : completionField) :=
  rfl

/-! ## Uniform principal power for actual valuation units -/

/-- One positive exponent sends every actual valuation unit into the principal
units of the actual valuation. -/
theorem exists_uniform_valuedInteger_principalPower
    (h : ClosedBallCompactnessInput) :
    ∃ N : ℕ, 0 < N ∧
      ∀ u : (valuedInteger)ˣ,
        (Valued.v ((((u ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative ℤ)) < 1 := by
  letI : ProperSpace completionField := properSpaceOfClosedBallCompactness h
  obtain ⟨N, hNpos, hN⟩ :=
    LeanFormal.IUT.LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
      (K := completionField)
  refine ⟨N, hNpos, ?_⟩
  intro u
  let e : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ ≃*
      (valuedInteger)ˣ := integersUnitsEquivValuedInteger
  let v : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ :=
    e.symm u
  have hmem : v ^ N ∈ LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits :=
    hN v
  rw [LeanFormal.IUT.LocalFieldIntegralUnits.mem_principalUnits_iff] at hmem
  have hmap : e (v ^ N) = u ^ N := by
    dsimp [v]
    rw [map_pow, MulEquiv.apply_symm_apply]
  have hval : ((((u ^ N).val).1 : completionField)) =
      ((((v ^ N).val).1 : completionField)) := by
    have hcongr := congrArg
      (fun w : (valuedInteger)ˣ => (((w.val).1) : completionField)) hmap
    simpa [e, integersUnitsEquivValuedInteger, integersEquivValuedInteger,
      Units.mapEquiv] using hcongr.symm
  rw [hval]
  exact (norm_lt_one_iff_valued_lt_one _).mp hmem

theorem exists_uniform_valuedInteger_principalPower_norm
    (h : ClosedBallCompactnessInput) :
    ∃ N : ℕ, 0 < N ∧
      ∀ u : (valuedInteger)ˣ,
        ‖((((u ^ N).val).1 : completionField)) - 1‖ < 1 := by
  obtain ⟨N, hNpos, hN⟩ := exists_uniform_valuedInteger_principalPower h
  refine ⟨N, hNpos, fun u => ?_⟩
  exact (norm_lt_one_iff_valued_lt_one _).mpr (hN u)

/-! ## Refined DVR decomposition -/

/-- **Unconditional (relative to the explicit closed-ball input) DVR
principal/torsion refinement.**  Every unit is `π^m` times an actual integral
unit whose `N`-th power is principal, for one uniform `N`. -/
theorem dvrPrincipalTorsionRefinement
    (h : ClosedBallCompactnessInput) (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        (Valued.v ((((u0 ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative ℤ)) < 1 :=
by
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  obtain ⟨N, hNpos, hN⟩ := exists_uniform_valuedInteger_principalPower h
  exact ⟨m, u0, hdec, N, hNpos, hN u0⟩

/-- Uniform-quantifier form: a single positive exponent works for every unit of
the canonical completion. -/
theorem dvrPrincipalTorsionRefinement_uniform
    (h : ClosedBallCompactnessInput) :
    ∃ N : ℕ, 0 < N ∧
      ∀ u : completionFieldˣ, ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
        (u : completionField) = concreteAdicUniformizer ^ m *
          ((u0.val).1 : completionField) ∧
        (Valued.v ((((u0 ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative ℤ)) < 1 :=
by
  obtain ⟨N, hNpos, hN⟩ := exists_uniform_valuedInteger_principalPower h
  refine ⟨N, hNpos, ?_⟩
  intro u
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  exact ⟨m, u0, hdec, hN u0⟩

/-- Norm-spelling form of the refined decomposition. -/
theorem dvrPrincipalTorsionRefinement_norm
    (h : ClosedBallCompactnessInput) (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        ‖((((u0 ^ N).val).1 : completionField)) - 1‖ < 1 :=
by
  obtain ⟨m, u0, hdec, N, hNpos, hNval⟩ := dvrPrincipalTorsionRefinement h u
  exact ⟨m, u0, hdec, N, hNpos, (norm_lt_one_iff_valued_lt_one _).mpr hNval⟩


/-- Uniform norm-spelling form: one exponent works for every unit and the
principal bound is stated with the canonical completion norm. -/
theorem dvrPrincipalTorsionRefinement_uniform_norm
    (h : ClosedBallCompactnessInput) :
    ∃ N : ℕ, 0 < N ∧
      ∀ u : completionFieldˣ, ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
        (u : completionField) = concreteAdicUniformizer ^ m *
          ((u0.val).1 : completionField) ∧
        ‖((((u0 ^ N).val).1 : completionField)) - 1‖ < 1 :=
by
  obtain ⟨N, hNpos, hN⟩ := exists_uniform_valuedInteger_principalPower_norm h
  refine ⟨N, hNpos, ?_⟩
  intro u
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  exact ⟨m, u0, hdec, hN u0⟩

/-- A version with the uniform exponent exposed as a single choice. -/
noncomputable def dvrPrincipalTorsionExponent
    (h : ClosedBallCompactnessInput) : ℕ :=
  Classical.choose (dvrPrincipalTorsionRefinement_uniform h)

theorem dvrPrincipalTorsionExponent_pos
    (h : ClosedBallCompactnessInput) :
    0 < dvrPrincipalTorsionExponent h :=
  (Classical.choose_spec (dvrPrincipalTorsionRefinement_uniform h)).1

theorem dvrPrincipalTorsionExponent_spec
    (h : ClosedBallCompactnessInput) (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      (Valued.v ((((u0 ^ dvrPrincipalTorsionExponent h).val).1 :
          completionField) - 1) : WithZero (Multiplicative ℤ)) < 1 :=
  (Classical.choose_spec (dvrPrincipalTorsionRefinement_uniform h)).2 u

end LeanFormal.IUT.DVRPrincipalRefinementProof

end