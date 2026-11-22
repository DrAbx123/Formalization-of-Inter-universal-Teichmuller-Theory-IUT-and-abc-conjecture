import tmp.sheaf.xif.paper.S2574LocalizedModelActual
import tmp.sheaf.xif.paper.S2003Psi5ModelActual
import tmp.sheaf.xif.paper.S2007F613FbarActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2003Psi5ModelActual
open LeanFormal.IUT.XiFPaper.S2574LocalizedModelActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2007F613FbarActual

namespace LeanFormal.IUT.XiFPaper.S2575LocalizedR10Actual

/-- Localized ring O_F'[1/(2^36*5)]; canonically O_F'[1/10]. -/
abbrev R10 : Type := S2574LocalizedModelActual.R
/-- Scalar-normalized integral model over R10. -/
abbrev f10 : R10[X] := S2574LocalizedModelActual.f

abbrev x10 : NumberField.RingOfIntegers S1720Field :=
  algebraMap ℤ (NumberField.RingOfIntegers S1720Field) S2574LocalizedModelActual.Lc

theorem x10_map_ne_zero :
    algebraMap (NumberField.RingOfIntegers S1720Field) S1720Field x10 ≠ 0 := by
  rw [show algebraMap (NumberField.RingOfIntegers S1720Field) S1720Field x10 =
      algebraMap ℤ S1720Field S2574LocalizedModelActual.Lc from by
    rw [x10, IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers S1720Field) S1720Field]]
  norm_num [S2574LocalizedModelActual.Lc]

noncomputable instance instAlgebraR10 : Algebra R10 S1720Field :=
  (IsLocalization.lift (M := Submonoid.powers x10) (S := R10) (P := S1720Field)
    (by
      intro y
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y.1 x10).mp y.2
      rw [← hn, map_pow]
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero n x10_map_ne_zero))).toAlgebra

noncomputable instance instIsScalarTowerR10 :
    IsScalarTower (NumberField.RingOfIntegers S1720Field) R10 S1720Field :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq])

theorem f10_monic : f10.Monic := S2574LocalizedModelActual.f_monic

theorem S2003Psi5Z_map_F' :
    S2132Psi5Z.map (Int.castRingHom S1720Field) =
      Polynomial.C ((2 : S1720Field) ^ 36) * S2057Psi5F := by
  have h := congrArg (Polynomial.map (algebraMap ℚ S1720Field)) S2003Psi5Z_model
  have hcompQ : (algebraMap ℚ S1720Field).comp (Int.castRingHom ℚ) =
      Int.castRingHom S1720Field := by
    ext z
    simp
  simpa [S2057Psi5F, Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C,
    hcompQ, map_pow] using h

theorem f10_map_scalar :
    f10.map (algebraMap R10 S1720Field) =
      Polynomial.C ((5 : S1720Field)⁻¹) * S2057Psi5F := by
  change (S2574LocalizedModelActual.f.map (algebraMap R10 S1720Field)) =
    Polynomial.C ((5 : S1720Field)⁻¹) * S2057Psi5F
  unfold S2574LocalizedModelActual.f
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map]
  have hcompO : (algebraMap R10 S1720Field).comp (algebraMap ℤ R10) =
      Int.castRingHom S1720Field := by
    ext z
    simp
  rw [hcompO, S2003Psi5Z_map_F']
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  set x : NumberField.RingOfIntegers S1720Field := algebraMap ℤ (NumberField.RingOfIntegers S1720Field) S2574LocalizedModelActual.Lc with hx
  have hmulR : algebraMap (NumberField.RingOfIntegers S1720Field) R10 x *
      IsLocalization.Away.invSelf x = 1 :=
    IsLocalization.Away.mul_invSelf (S := R10) (x := x)
  have hmulF := congrArg (algebraMap R10 S1720Field) hmulR
  simp only [map_mul, map_one] at hmulF
  have hxF : algebraMap R10 S1720Field (algebraMap (NumberField.RingOfIntegers S1720Field) R10 x) =
      (2 : S1720Field) ^ 36 * 5 := by
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers S1720Field) R10 S1720Field]
    change algebraMap (NumberField.RingOfIntegers S1720Field) S1720Field
      (algebraMap ℤ (NumberField.RingOfIntegers S1720Field) S2574LocalizedModelActual.Lc) = _
    rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers S1720Field) S1720Field]
    norm_num [S2574LocalizedModelActual.Lc]
  have hB : algebraMap R10 S1720Field (IsLocalization.Away.invSelf x) =
      ((2 : S1720Field) ^ 36 * 5)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    simpa [hxF] using hmulF
  rw [hB]
  field_simp

#check f10_monic
#check f10_map_scalar
#print axioms f10_monic
#print axioms f10_map_scalar
end LeanFormal.IUT.XiFPaper.S2575LocalizedR10Actual
end