import tmp.sheaf.xif.paper.S1605PointedCurveCoeffActual
import tmp.sheaf.xif.paper.S1606SlopeDoublingActual
import tmp.sheaf.xif.paper.S1611PolynomialXRearrangeActual
import tmp.sheaf.xif.paper.S1613C_Psi3Actual

/-!
# S1615: tangent doubling in X and Y from the TauCeti ZSMul draft

This file ports the two point-level tangent-doubling identities of the TauCeti
Universal.Affine ZSMul draft to the names of the current production layer, and
proves the targets S1612AddXSmulOne and S1612AddYSmulOne from S1612.

The draft names are mapped as follows.

* C_Ψ₃_eq            -> s1613_C_Ψ₃
* polyToField_ψ₂Sq   -> s1613_polyToField_Ψ₂Sq
* polyToField_polynomial -> the local s1615_polyToField_polynomial
* ω                  -> WeierstrassCurve.ω with WeierstrassCurve.ω_def
* redInvarDenom_two  -> WeierstrassCurve.reducedInvarDenom_two
* compl₂EDSAux_two   -> WeierstrassCurve.complEDS₂Aux_two

The imported production nodes are S1605, S1606, S1611 and S1613 (S1613 itself
transitively supplies S1612 and the earlier universal-curve layer).  No statement
from the unverified draft is used as an axiom; the two field identities that the
draft isolates as private auxiliary lemmas are proved here by field_simp and ring.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1615AddXAddYFromDraftActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open LeanFormal.IUT.XiFPaper.S1611PolynomialXRearrangeActual
open LeanFormal.IUT.XiFPaper.S1612ZSMulPointFinalActual
open LeanFormal.IUT.XiFPaper.S1613C_Psi3Actual

/-! ### The Weierstrass polynomial in the universal field -/

/-- The universal Weierstrass polynomial vanishes in the universal field. -/
theorem s1615_polyToField_polynomial :
    polyToField curve.toAffine.polynomial = 0 := by
  rw [polyToField_apply]
  change algebraMap Ring Field (AdjoinRoot.mk curve.toAffine.polynomial
    curve.toAffine.polynomial) = 0
  rw [AdjoinRoot.mk_self, map_zero]

/-! ### The value of ψ₂ in the universal field -/

/-- polyToField of polynomialY is ψᵤ 2. -/
theorem s1615_polyToField_polynomialY :
    polyToField curve.toAffine.polynomialY = ψᵤ 2 := by
  change polyToField curve.toAffine.ψ₂ = ψᵤ 2
  rw [← WeierstrassCurve.ψ_two]

/-- polyToField of the ψ₂ polynomial is ψᵤ 2. -/
theorem s1615_polyToField_ψ₂ :
    polyToField curve.toAffine.ψ₂ = ψᵤ 2 := by
  rw [← WeierstrassCurve.ψ_two]

/-- The negated Weierstrass polynomial evaluates to the field negation formula. -/
theorem s1615_polyToField_negPolynomial :
    polyToField curve.toAffine.negPolynomial =
      -smulY 1 - (pointedCurve.toAffine.a₁ * smulX 1 + pointedCurve.toAffine.a₃) := by
  rw [← Affine.Y_sub_polynomialY]
  rw [map_sub polyToField]
  rw [← smulY_one, s1615_polyToField_polynomialY]
  have h := s1606_smulY_one_sub_negY
  simp only [Affine.negY] at h
  linear_combination h

/-! ### The value of ω 2 -/

/-- The value of ω 2 in the universal field, with the Weierstrass-polynomial
summands already killed by s1615_polyToField_polynomial. -/
theorem s1615_polyToField_ω_two :
    polyToField (curve.toAffine.ω 2) =
      (polyToField (CC curve.toAffine.a₁) * polyToField curve.toAffine.ψ₂
         - polyToField curve.toAffine.polynomialX) * polyToField (C curve.toAffine.Ψ₃)
      + 0 * polyToField (2 * curve.toAffine.polynomial + C curve.toAffine.Ψ₂Sq)
      + polyToField curve.toAffine.negPolynomial * (polyToField curve.toAffine.ψ₂) ^ 3 := by
  rw [WeierstrassCurve.ω_def, WeierstrassCurve.reducedInvarDenom_two,
    WeierstrassCurve.complEDS₂Aux_two, WeierstrassCurve.ψ_two]
  simp only [map_add polyToField, map_sub polyToField, map_mul polyToField,
    map_pow polyToField, map_ofNat polyToField, one_mul, sub_zero, mul_zero, zero_mul,
    s1615_polyToField_polynomial, s1615_polyToField_ψ₂,
    s1615_polyToField_polynomialY]

/-! ### The Ψ₃ identity in the universal field -/

/-- polyToField of C Ψ₃, in the exact form needed for addX. -/
theorem s1615_polyToField_C_Ψ₃ :
    polyToField (C curve.toAffine.Ψ₃) =
      (3 * smulX 1 + pointedCurve.toAffine.a₂) * (ψᵤ 2) ^ 2
        - (polyToField curve.toAffine.polynomialX) ^ 2
        + pointedCurve.toAffine.a₁ * ψᵤ 2 * polyToField curve.toAffine.polynomialX := by
  have h := congrArg polyToField (s1613_C_Ψ₃ (W := curve.toAffine))
  simp only [map_add polyToField, map_sub polyToField, map_mul polyToField,
    map_pow polyToField, map_ofNat polyToField] at h
  rw [s1615_polyToField_polynomial] at h
  rw [s1613_polyToField_Ψ₂Sq] at h
  rw [← smulX_one, ← s1605_pointedCurve_a1, ← s1606_pointedCurve_a2] at h
  simpa [s1615_polyToField_ψ₂] using h

/-- The same identity written with ψᵤ 3 = polyToField (ψ 3). -/
theorem s1615_C_Ψ₃_eq :
    polyToField (C curve.toAffine.Ψ₃) = ψᵤ 3 := by
  rw [show ψᵤ 3 = polyToField (C curve.toAffine.Ψ₃) from by
    rw [ψᵤ, WeierstrassCurve.ψ_three]]

/-- The Ψ₃ formula with ψᵤ 3 on the left. -/
theorem s1615_ψᵤ_three :
    ψᵤ 3 = (3 * smulX 1 + pointedCurve.toAffine.a₂) * (ψᵤ 2) ^ 2
        - (polyToField curve.toAffine.polynomialX) ^ 2
        + pointedCurve.toAffine.a₁ * ψᵤ 2 * polyToField curve.toAffine.polynomialX := by
  rw [← s1615_C_Ψ₃_eq]
  exact s1615_polyToField_C_Ψ₃

/-! ### The X-coordinate of 2 • (X, Y) -/

private lemma s1615_addX_aux {F : Type*} [Field F] {a₁ a₂ x dx dy : F} (hdy : dy ≠ 0) :
    (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
      (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by
  field_simp
  ring

/-- The tangent-doubling X identity. -/
theorem s1615_addX_eq :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := by
  rw [show smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 from smulX_two]
  rw [Affine.addX]
  rw [show slopeOne = -polyToField curve.toAffine.polynomialX / ψᵤ 2 from s1611_slopeOne_eq]
  have hdy : ψᵤ 2 ≠ 0 := polyToField_ψ_ne_zero 2 (by norm_num)
  have hmain : (-polyToField curve.toAffine.polynomialX / ψᵤ 2) ^ 2
      + pointedCurve.toAffine.a₁ * (-polyToField curve.toAffine.polynomialX / ψᵤ 2)
      - pointedCurve.toAffine.a₂ - smulX 1 - smulX 1 - smulX 1 =
      -ψᵤ 3 / (ψᵤ 2) ^ 2 := by
    rw [s1615_addX_aux (a₁ := pointedCurve.toAffine.a₁) (a₂ := pointedCurve.toAffine.a₂)
      (x := smulX 1) (dx := polyToField curve.toAffine.polynomialX) (dy := ψᵤ 2) hdy,
      s1615_ψᵤ_three]
    ring
  calc (-polyToField curve.toAffine.polynomialX / ψᵤ 2) ^ 2
      + pointedCurve.toAffine.a₁ * (-polyToField curve.toAffine.polynomialX / ψᵤ 2)
      - pointedCurve.toAffine.a₂ - smulX 1 - smulX 1
      = ((-polyToField curve.toAffine.polynomialX / ψᵤ 2) ^ 2
          + pointedCurve.toAffine.a₁ * (-polyToField curve.toAffine.polynomialX / ψᵤ 2)
          - pointedCurve.toAffine.a₂ - smulX 1 - smulX 1 - smulX 1) + smulX 1 := by ring
    _ = -ψᵤ 3 / (ψᵤ 2) ^ 2 + smulX 1 := by rw [hmain]
    _ = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by ring

/-! ### The Y-coordinate of 2 • (X, Y) -/

/-- The tangent-doubling Y identity. -/
theorem s1615_addY_eq :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := by
  rw [show smulY 2 = polyToField (curve.toAffine.ω 2) / (ψᵤ 2) ^ 3 from rfl]
  rw [s1615_polyToField_ω_two]
  rw [← s1605_pointedCurve_a1, s1615_polyToField_ψ₂, s1615_C_Ψ₃_eq,
    s1615_polyToField_negPolynomial]
  unfold Affine.addY
  simp only [Affine.negY, Affine.negAddY]
  rw [s1615_addX_eq]
  rw [show slopeOne = -polyToField curve.toAffine.polynomialX / ψᵤ 2 from s1611_slopeOne_eq]
  rw [show smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 from smulX_two]
  simp only [zero_mul, add_zero]
  have hdy : ψᵤ 2 ≠ 0 := polyToField_ψ_ne_zero 2 (by norm_num)
  field_simp
  ring

/-! ### The S1612 targets -/

/-- The S1612 addX target, proved. -/
theorem s1615_addX_smul_one_smul_one : S1612AddXSmulOne := s1615_addX_eq

/-- The S1612 addY target, proved. -/
theorem s1615_addY_smul_one_smul_one : S1612AddYSmulOne := s1615_addY_eq

end LeanFormal.IUT.XiFPaper.S1615AddXAddYFromDraftActual
end
