import tmp.sheaf.xif.paper.S1621ZSMulPointInductionFullActual
import tmp.sheaf.xif.paper.S1620ZSMulPointInductionActual
import tmp.sheaf.xif.paper.S1617SmulAddFromDraftActual
import tmp.sheaf.xif.paper.S1615AddXAddYFromDraftActual
import tmp.sheaf.xif.paper.S1602PhiNeZeroActual
import tmp.sheaf.xif.paper.S1605PointedCurveCoeffActual

/-!
# S1622: the strong-induction step of the universal point formula

This file ports the step of TauCeti's
`WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY`
(tmp/TauCeti/TauCeti/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/ZSMul.lean,
the `Int.negInduction` block; the earlier draft is _PRZSMul.lean:315-355) to the
local S1619 point `s1619Point` and to the local chord identities S1615/S1617/S1602.

The base cases `n = 1` and `n = 2` are the already checked S1620 and S1621
statements.  The inductive step writes `(n + 3) • P` as `(n + 2) • P + 1 • P`,
reads the latter sum through Mathlib's `Affine.Point.add_of_X_ne`, matches the
X-coordinate with `addX_eq_addX_negY_sub` against `s1617_smulX_add`, and matches
the Y-coordinate through `addY_sub_negY_addY` against `s1617_smulY_add_sub_negY`.
The last match uses the elementary injectivity of `z ↦ z - W.negY x z`, ported
as the private lemma below exactly as TauCeti states it.

No statement of the unverified draft is imported as an axiom; every local
ingredient is a checked declaration of the S16 layer.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1622ZSMulInductionStepActual

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1615AddXAddYFromDraftActual
open LeanFormal.IUT.XiFPaper.S1617SmulAddFromDraftActual
open LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual
open LeanFormal.IUT.XiFPaper.S1620ZSMulPointInductionActual
open LeanFormal.IUT.XiFPaper.S1621ZSMulPointInductionFullActual

/-! ### The vertical-gap injectivity used for the Y-coordinate -/

/-- `z ↦ z - W.negY x z` is injective: it is `z ↦ 2z + a₁x + a₃`.

Stated over an opaque affine curve so that the concrete coefficients of
`pointedCurve.toAffine` are not unfolded during the induction.  This is the
private lemma of the TauCeti proof; it is not a new mathematical assumption. -/
private lemma s1622_eq_of_sub_negY_eq {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (W : WeierstrassCurve.Affine F) {x z₁ z₂ : F}
    (h : z₁ - W.negY x z₁ = z₂ - W.negY x z₂) : z₁ = z₂ := by
  simp only [Affine.negY] at h
  have h2z : (2 : F) * z₁ = 2 * z₂ := by linear_combination h
  exact mul_left_cancel₀ h2 h2z

/-! ### Characteristic zero and the negative-index sign rule -/

/-- The universal field has characteristic zero at `2`: this is the only
characteristic-zero fact used by the induction step.  The instance is not
currently synthesized by typeclass search because `Universal.Ring` is a
nested `AdjoinRoot`; it is proved here from injectivity of the two structure
maps rather than postulated.

This is the first genuine gap the ported induction step exposes: TauCeti uses
`two_ne_zero` at `Universal.Field` directly, and the local layer has neither
`CharZero Universal.Field` nor `NeZero (2 : Universal.Field)` as an instance. -/
private lemma s1622_two_ne_zero_field : (2 : Universal.Field) ≠ 0 := by
  intro h
  have h' : algebraMap Universal.Ring Universal.Field (2 : Universal.Ring) =
      algebraMap Universal.Ring Universal.Field 0 := by
    rw [map_ofNat, map_zero]
    exact h
  have hR : (2 : Universal.Ring) = 0 :=
    IsFractionRing.injective Universal.Ring Universal.Field h'
  have hof : AdjoinRoot.of curve.toAffine.polynomial
      (2 : Polynomial (MvPolynomial Coeff ℤ)) = 0 := by
    rw [map_ofNat]
    exact hR
  have hdeg : curve.toAffine.polynomial.degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.degree_polynomial]
    norm_num
  have hinj : Function.Injective (AdjoinRoot.of curve.toAffine.polynomial) :=
    AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  have h2 : (2 : Polynomial (MvPolynomial Coeff ℤ)) = 0 :=
    hinj (by simpa using hof)
  have hC2 : (2 : Polynomial (MvPolynomial Coeff ℤ)) =
      Polynomial.C (2 : MvPolynomial Coeff ℤ) := by
    rw [map_ofNat (Polynomial.C : MvPolynomial Coeff ℤ →+*
      Polynomial (MvPolynomial Coeff ℤ)) 2]
  have hMv : (2 : MvPolynomial Coeff ℤ) ≠ 0 := by
    have hC2' : (2 : MvPolynomial Coeff ℤ) = MvPolynomial.C (2 : ℤ) := by
      rw [map_ofNat (MvPolynomial.C : ℤ →+* MvPolynomial Coeff ℤ) 2]
    rw [hC2']
    exact MvPolynomial.C_ne_zero.mpr (by norm_num : (2 : ℤ) ≠ 0)
  exact (Polynomial.C_ne_zero.mpr hMv) (hC2 ▸ h2)

/-- `smulY (-n)` is the `negY` of `(smulX n, smulY n)` for `n ≠ 0`.

TauCeti obtains this as its `smulY_neg` sign rule (from the `ω_neg` sign
rule).  The local layer states the corresponding target only as the proposition
`S1597SmulYNeg`; S1597 proves the `ω` identity `S1597UniversalOmegaNeg`, not the
`smulY` rule itself.  So here the rule is derived from the already checked
vertical-gap formula `s1605_smulY_sub_negY` at `n` and at `-n`: the two gaps
are negatives of each other, and `z ↦ z - W.negY x z` is `z ↦ 2z + a₁x + a₃`,
which is injective in characteristic zero (the previous lemma). -/
private lemma s1622_smulY_neg (n : ℤ) (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  have h1 := s1605_smulY_sub_negY (-n) (by omega)
  have h2 := s1605_smulY_sub_negY n h0
  have hψ : ψᵤ (2 * (-n)) / (ψᵤ (-n)) ^ 4 = -(ψᵤ (2 * n) / (ψᵤ n) ^ 4) := by
    have h2n : ψᵤ (-(2 * n)) = -ψᵤ (2 * n) := by
      simp only [ψᵤ, WeierstrassCurve.ψ_neg, map_neg polyToField]
    have hn : ψᵤ (-n) = -ψᵤ n := by
      simp only [ψᵤ, WeierstrassCurve.ψ_neg, map_neg polyToField]
    have h4 : (-ψᵤ n) ^ 4 = (ψᵤ n) ^ 4 :=
      Even.neg_pow (by decide : Even 4) (ψᵤ n)
    rw [show 2 * (-n) = -(2 * n) by ring, h2n, hn, h4]
    exact neg_div _ _
  rw [smulX_neg, hψ] at h1
  rw [← h2] at h1
  simp only [Affine.negY] at h1
  have hsum : smulY (-n) + smulY n +
      ((pointedCurve.toAffine).a₁ * smulX n + (pointedCurve.toAffine).a₃) = 0 := by
    have h : (2 : Field) * (smulY (-n) + smulY n +
        ((pointedCurve.toAffine).a₁ * smulX n + (pointedCurve.toAffine).a₃)) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp h).resolve_left s1622_two_ne_zero_field
  simp only [Affine.negY]
  linear_combination hsum

/-! ### The strong induction -/

/-- **The universal point formula.**  For every nonzero integer `n`, the point
`n • s1619Point` is the affine point whose coordinates are `(smulX n, smulY n)`.

This is the local form of TauCeti's `zsmul_point_eq_smulX_smulY`: the strong
induction on the natural part uses the S1620 base at `1` and the S1621 base at
`2`, and the sign part uses `neg_smul` and `Affine.Point.neg_some`. -/
theorem s1622ZSMulPointFormula : S1620ZSMulPointFormula := by
  intro n
  induction n using Int.negInduction with
  | nat n =>
    refine Nat.strong_induction_on n ?_
    intro n ih h0
    obtain _ | _ | _ | n := n
    · exact (h0 rfl).elim
    · exact ⟨s1619Nonsingular, s1620OneZSMul⟩
    · exact s1621TwoZSMul
    set n2 := n + 1 + 1 with hn2
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 :=
      s1602SmulX_ne_smulX n2 1 (by omega) (by omega)
    obtain ⟨ns, eq⟩ :
        ∃ h : (pointedCurve.toAffine).Nonsingular (smulX 1) (smulY 1),
          (1 : ℤ) • s1619Point = Affine.Point.some (smulX 1) (smulY 1) h :=
      ⟨s1619Nonsingular, s1620OneZSMul⟩
    simp_rw [show ((n + 1 : ℕ) : ℤ) = (n2 : ℤ) + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    rw [eq2, eq, Affine.Point.neg_some, Affine.Point.add_of_X_ne ne,
      Affine.Point.some.injEq] at eq1
    let U := pointedCurve.toAffine
    let L := U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX ((n2 : ℤ) + 1) = U.addX (smulX n2) (smulX 1) L := by
      rw [s1617_smulX_add 1 n2 one_ne_zero (by omega) (by omega) (by omega),
        Affine.addX_eq_addX_negY_sub (W := U) (smulY n2) (smulY 1) ne,
        sub_eq_add_neg (n2 : ℤ), ← eq1.1]
    have hfact₁ :=
      s1617_smulY_add_sub_negY 1 n2 one_ne_zero (by omega) (by omega) (by omega)
    have hfact₂ := U.addY_sub_negY_addY (x₁ := smulX n2) (x₂ := smulX 1)
      (smulY n2) (smulY 1) ne
    have Y_eq : smulY ((n2 : ℤ) + 1) = U.addY (smulX n2) (smulX 1) (smulY n2) L :=
      s1622_eq_of_sub_negY_eq s1622_two_ne_zero_field U (x := U.addX (smulX n2) (smulX 1) L) <| by
        simp only at hfact₂
        rw [X_eq] at hfact₁
        rw [hfact₁, hfact₂]
    rw [show ((n + 1 + 1 + 1 : ℕ) : ℤ) = (n2 : ℤ) + 1 by omega, X_eq, Y_eq,
      add_zsmul, eq, eq2]
    exact ⟨Affine.nonsingular_add ns2 ns fun h => ne h.1,
      Affine.Point.add_of_X_ne ne⟩
  | neg ih n =>
    rw [neg_ne_zero]
    intro h0
    obtain ⟨ns, eq⟩ := ih n h0
    simp_rw [smulX_neg, s1622_smulY_neg n h0, neg_smul, eq, Affine.Point.neg_some]
    exact ⟨(Affine.nonsingular_neg ..).mpr ns, trivial⟩

end LeanFormal.IUT.XiFPaper.S1622ZSMulInductionStepActual
end
