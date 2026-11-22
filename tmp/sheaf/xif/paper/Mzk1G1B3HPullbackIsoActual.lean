/- B3 S3a (grace, taken over from S8): generic P1 statement O(d) ≅ h^*O(1) at Cech level.
   Cover: A0 = Away h, A1 = P1Overlap = Away λ, A01 = P1Overlap[1/h].
   Units: t' = h-image (h^*O(1)), t = λ^d (O(d)), coboundary a0 = h (unit in A0), a1 = λ^d (unit in A1).
   Engine: TwoChartCech.Cover.lineBundle_iso_of_mul. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1TwoChartCechLineBundleIsoActual
import tmp.sheaf.xif.paper.Mzk1G1B3CoverActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3HPullbackIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B3CoverActual

/-- A01 = (Away λ) 在 h 的像处局部化。 -/
abbrev A01H (h : Polynomial ℚ) : Type :=
  Localization.Away (algebraMap (Polynomial ℚ) P1Overlap h)

/-- ℚ[λ] → A01（经 Away λ 再局部化）。 -/
noncomputable def baseToA01 (h : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] A01H h :=
  (IsScalarTower.toAlgHom ℚ P1Overlap (A01H h)).comp
    (IsScalarTower.toAlgHom ℚ (Polynomial ℚ) P1Overlap)

theorem baseToA01_h_isUnit (h : Polynomial ℚ) : IsUnit (baseToA01 h h) := by
  have hh := IsLocalization.Away.algebraMap_isUnit (S := A01H h)
    (x := algebraMap (Polynomial ℚ) P1Overlap h)
  simpa [baseToA01] using hh

/-- A0 = Away h → A01。 -/
noncomputable def hRho0 (h : Polynomial ℚ) : Localization.Away h →ₐ[ℚ] A01H h :=
  IsLocalization.Away.liftAlgHom (x := h) (f := baseToA01 h) (baseToA01_h_isUnit h)

/-- A1 = Away λ → A01。 -/
noncomputable def hRho1 (h : Polynomial ℚ) : P1Overlap →ₐ[ℚ] A01H h :=
  IsScalarTower.toAlgHom ℚ P1Overlap (A01H h)

/-- P¹ 的 h-refined Čech cover。 -/
noncomputable def p1HCover (h : Polynomial ℚ) : TwoChartCech.Cover ℚ where
  A0 := Localization.Away h
  A1 := P1Overlap
  A01 := A01H h
  ρ0 := hRho0 h
  ρ1 := hRho1 h

noncomputable def hUnitA0 (h : Polynomial ℚ) : (Localization.Away h)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) (x := h)).unit

noncomputable def xUnitA1 (h : Polynomial ℚ) : P1Overlapˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := P1Overlap)
    (x := (Polynomial.X : Polynomial ℚ))).unit

noncomputable def xUnitA01 (h : Polynomial ℚ) : (A01H h)ˣ :=
  Units.map (algebraMap P1Overlap (A01H h)).toMonoidHom (xUnitA1 h)

noncomputable def hUnitA01 (h : Polynomial ℚ) : (A01H h)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := A01H h)
    (x := algebraMap (Polynomial ℚ) P1Overlap h)).unit

noncomputable def odUnit (h : Polynomial ℚ) (d : Nat) : (A01H h)ˣ := xUnitA01 h ^ d

/-- h^*O(1) 的过渡单元就是 h 的像。 -/
theorem hUnitA01_val (h : Polynomial ℚ) :
    (hUnitA01 h : A01H h) = algebraMap P1Overlap (A01H h)
      (algebraMap (Polynomial ℚ) P1Overlap h) := rfl

/-- ρ0(h) = h 的像（局部化 lift 求值）。 -/
theorem hRho0_hUnitA0_val (h : Polynomial ℚ) :
    (Units.map (hRho0 h).toMonoidHom (hUnitA0 h) : A01H h) = (hUnitA01 h : A01H h) := by
  rw [Units.coe_map, hUnitA01_val]
  have h1 : (hUnitA0 h : Localization.Away h) =
      algebraMap (Polynomial ℚ) (Localization.Away h) h := rfl
  rw [h1]
  change (hRho0 h) ((algebraMap (Polynomial ℚ) (Localization.Away h)) h) = _
  rw [show hRho0 h =
    IsLocalization.Away.liftAlgHom h (f := baseToA01 h) (baseToA01_h_isUnit h) from rfl]
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- ρ1(λ) = λ 的像。 -/
theorem hRho1_xUnitA1_val (h : Polynomial ℚ) :
    (Units.map (hRho1 h).toMonoidHom (xUnitA1 h) : A01H h) = (xUnitA01 h : A01H h) := rfl

#print axioms baseToA01_h_isUnit
#print axioms hRho0_hUnitA0_val
#print axioms hRho1_xUnitA1_val
/-- ρ1(λ) = λ 的像（元素形式）。 -/
theorem hRho1_xUnitA1_apply (h : Polynomial ℚ) :
    (hRho1 h) ((xUnitA1 h : P1Overlapˣ) : P1Overlap) = (xUnitA01 h : A01H h) := rfl
/- NOTE: the canonical generic P1 statement O(natDegree h) ≅ h^*O(1) is DONE in
   Mzk1G1B3HPullbackActual (S8 subagent, 22:47:08Z, trio) with b3_h_pullbackO1_iso.
   This file keeps the earlier stage-1 construction (cover + units + rho evaluation lemmas)
   which was DONE at 22:44:08Z; the later duplicate attempt was removed. -/
end LeanFormal.IUT.XiFPaper.Mzk1G1B3HPullbackIsoActual