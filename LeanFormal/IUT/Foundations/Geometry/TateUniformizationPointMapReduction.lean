/-
  Reductions of the point-valued Tate uniformization gap to pair-level conditions.

  `TateUniformizationPointMap` defines the orbit-quotient point map from the candidate
  Weierstrass pair and records the remaining gap `TateUniformizationPointMapGap` as
  injectivity plus surjectivity onto the nonzero affine points.  This file proves that
  the gap is *exactly equivalent* to two conditions stated purely on the pole-excluded
  parameter domain, with no quotient and no point-nonsingularity bookkeeping:

  * `tatePairCoordinatesSeparateOrbits` -- equal `X`- and `Y`-coordinates force the same
    `q^ℤ`-orbit;
  * `tateCoordinatesCoverNonzeroPoints` -- every nonsingular affine point is the image of
    a domain parameter.

  Both equivalences only unfold definitions and use the already-proved value-at-a-
  representative lemmas; the analytic (theta) input that proves either pair-level
  condition is not touched and is not claimed here.  The consumer is the gap statement
  `TateUniformizationPointMapGap` itself: after these reductions, the remaining analytic
  obligation can be attacked at the coordinate level.
-/

import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMap

namespace LeanFormal.IUT.TateCurve

noncomputable section

open WeierstrassCurve

variable {K : Type*} [NormedField K] [CharZero K] {q : K}

/-! ## The pair-level conditions -/

/-- The series pair separates `q^ℤ`-orbits on the pole-excluded domain: two parameters
with equal `X`- and `Y`-coordinates lie in the same orbit.  This is the pair-level form
of injectivity of the quotient point map. -/
def tatePairCoordinatesSeparateOrbits (q : K) : Prop :=
  ∀ u v : ↥(coordinateParameterDomain q),
    tateWeierstrassX q (u : K) = tateWeierstrassX q (v : K) →
    tateWeierstrassY q (u : K) = tateWeierstrassY q (v : K) →
    tateParameterOrbitRel q u v

/-- The series coordinates realize every nonzero point of the canonical curve: every
nonsingular affine point is the pair of coordinates of a pole-excluded parameter.  This
is the pair-level form of surjectivity of the quotient point map. -/
def tateCoordinatesCoverNonzeroPoints (q : K) : Prop :=
  ∀ (x y : K), (weierstrassCurve K q).toAffine.Nonsingular x y →
    ∃ u : ↥(coordinateParameterDomain q),
      tateWeierstrassX q (u : K) = x ∧ tateWeierstrassY q (u : K) = y

/-! ## The two equivalences -/

/-- Injectivity of the quotient point map is equivalent to the pair-level separation
condition.  The forwards direction extracts the coordinates through
`WeierstrassCurve.Affine.Point.some.injEq` and then uses `Quotient.exact`; the backwards
direction inducts on the two quotient classes. -/
theorem tateQuotientPoint_injective_iff_pairCoordinatesSeparateOrbits
    (q : K) (parameterNeZero : q ≠ 0) (hdata : TateWeierstrassPointData q) :
    Function.Injective (tateQuotientPoint q parameterNeZero hdata) ↔
      tatePairCoordinatesSeparateOrbits q := by
  constructor
  · intro hinjective u v hX hY
    have hpoints :
        tateQuotientPoint q parameterNeZero hdata (Quotient.mk _ u) =
          tateQuotientPoint q parameterNeZero hdata (Quotient.mk _ v) := by
      rw [tateQuotientPoint_mk, tateQuotientPoint_mk]
      change WeierstrassCurve.Affine.Point.some (tateWeierstrassX q (u : K))
          (tateWeierstrassY q (u : K)) (hdata u) =
        WeierstrassCurve.Affine.Point.some (tateWeierstrassX q (v : K))
          (tateWeierstrassY q (v : K)) (hdata v)
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hX, hY⟩
    exact Quotient.exact (hinjective hpoints)
  · intro hseparates w₁ w₂ hw
    revert hw
    refine Quotient.inductionOn w₁ ?_
    intro u
    refine Quotient.inductionOn w₂ ?_
    intro v hw
    rw [tateQuotientPoint_mk, tateQuotientPoint_mk] at hw
    change WeierstrassCurve.Affine.Point.some (tateWeierstrassX q (u : K))
        (tateWeierstrassY q (u : K)) (hdata u) =
      WeierstrassCurve.Affine.Point.some (tateWeierstrassX q (v : K))
        (tateWeierstrassY q (v : K)) (hdata v) at hw
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hw
    exact Quotient.sound (hseparates u v hw.1 hw.2)

/-- Surjectivity of the quotient point map onto the nonzero points is equivalent to the
pair-level coverage condition.  The forwards direction applies surjectivity to a
nonsingular `some`-point; the backwards direction unpacks the point with `cases`. -/
theorem tateQuotientPoint_surjective_iff_coordinatesCoverNonzeroPoints
    (q : K) (parameterNeZero : q ≠ 0) (hdata : TateWeierstrassPointData q) :
    (∀ P : (weierstrassCurve K q).toAffine.Point, P ≠ 0 →
        ∃ w : TateParameterQuotient q parameterNeZero,
          tateQuotientPoint q parameterNeZero hdata w = P) ↔
      tateCoordinatesCoverNonzeroPoints q := by
  constructor
  · intro hsurjective x y hns
    obtain ⟨w, hw⟩ :=
      hsurjective (WeierstrassCurve.Affine.Point.some x y hns)
        (by intro hzero; cases hzero)
    revert hw
    refine Quotient.inductionOn w ?_
    intro u hw
    rw [tateQuotientPoint_mk] at hw
    change WeierstrassCurve.Affine.Point.some (tateWeierstrassX q (u : K))
        (tateWeierstrassY q (u : K)) (hdata u) =
      WeierstrassCurve.Affine.Point.some x y hns at hw
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hw
    exact ⟨u, hw.1, hw.2⟩
  · intro hcover P hne
    cases P with
    | zero => exact absurd rfl hne
    | some x y hns =>
      obtain ⟨u, hX, hY⟩ := hcover x y hns
      refine ⟨Quotient.mk _ u, ?_⟩
      rw [tateQuotientPoint_mk]
      change WeierstrassCurve.Affine.Point.some (tateWeierstrassX q (u : K))
          (tateWeierstrassY q (u : K)) (hdata u) =
        WeierstrassCurve.Affine.Point.some x y hns
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hX, hY⟩

/-! ## The gap restated in pair language -/

/-- The named gap of `TateUniformizationPointMap` is exactly the conjunction of the two
pair-level conditions; `hdata` is needed only to translate coordinates into points, and
the pair-level conditions themselves do not mention it. -/
theorem tateUniformizationPointMapGap_iff_pairConditions
    (q : K) (parameterNeZero : q ≠ 0) (hdata : TateWeierstrassPointData q) :
    TateUniformizationPointMapGap q parameterNeZero hdata ↔
      tatePairCoordinatesSeparateOrbits q ∧ tateCoordinatesCoverNonzeroPoints q := by
  constructor
  · intro hgap
    exact ⟨(tateQuotientPoint_injective_iff_pairCoordinatesSeparateOrbits
          q parameterNeZero hdata).mp hgap.1,
        (tateQuotientPoint_surjective_iff_coordinatesCoverNonzeroPoints
          q parameterNeZero hdata).mp hgap.2⟩
  · intro hpair
    exact ⟨(tateQuotientPoint_injective_iff_pairCoordinatesSeparateOrbits
          q parameterNeZero hdata).mpr hpair.1,
        (tateQuotientPoint_surjective_iff_coordinatesCoverNonzeroPoints
          q parameterNeZero hdata).mpr hpair.2⟩

end

end LeanFormal.IUT.TateCurve