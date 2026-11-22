/-
Title: algebraic foundation of line-bundle isomorphisms for the two-chart Cech model.

The two-chart Cech model `TwoChartCech` attaches to a unit `t` of `A01` a `Sections`
object `lineBundle t` with `r0 = rho0` and `r1 = t . rho1`.  Two such objects are
isomorphic as soon as the two trivializations differ by a Cech coboundary: there are units
`a0 : A0^x`, `a1 : A1^x` with `t' = rho0 a0 * t * (rho1 a1)^{-1}`.

This file provides that statement:

* `SectionsIso` : isomorphisms of `Sections` objects over the same cover;
* `coboundary_val` : the unit coboundary relation, evaluated in `A01`;
* `lineBundle_iso_of_unit_val` : the coboundary criterion in element form;
* `lineBundle_iso_of_mul` : the coboundary criterion in multiplicative form
  `t' * rho1 a1 = rho0 a0 * t` in `A01^x`;
* `lineBundle_iso_of_unit` : the criterion `t' = rho0 a0 * t * (rho1 a1)^{-1}`;
* `lineBundle_iso_refl` : reflexivity.

Everything is proved from the definitions; no extra hypotheses are introduced.
-/
import Mathlib.Algebra.Module.Equiv.Basic
import tmp.sheaf.xif.paper.AG_FLT_TwoChartCechActual

set_option autoImplicit false

noncomputable section

universe u v w

namespace TwoChartCech

/-! ### Isomorphisms of `Sections` objects -/

/-- An isomorphism between two objects of the two-chart Cech complex over the same cover:
linear equivalences of the three modules which commute with both restriction maps. -/
structure SectionsIso {R : Type u} [CommRing R] {U : Cover.{u, v} R}
    (S T : Sections.{u, v, w} U) where

  e0 : S.M0 ≃ₗ[U.A0] T.M0

  e1 : S.M1 ≃ₗ[U.A1] T.M1

  e01 : S.M01 ≃ₗ[U.A01] T.M01

  comm0 : ∀ m : S.M0, e01 (S.r0 m) = T.r0 (e0 m)

  comm1 : ∀ m : S.M1, e01 (S.r1 m) = T.r1 (e1 m)

namespace Cover

variable {R : Type u} [CommRing R] (U : Cover.{u, v} R)

/-! ### The coboundary criterion -/

/-- Reduction of the unit-level coboundary relation to a relation between elements of `A01`:
from `t' * rho1 a1 = rho0 a0 * t` in `A01^x` we get `t' * rho1 a1 = rho0 a0 * t` in `A01`. -/
theorem coboundary_val (t t' : U.A01ˣ) (a0 : U.A0ˣ) (a1 : U.A1ˣ)
    (h : t' * Units.map (U.ρ1 : U.A1 →* U.A01) a1 =
      Units.map (U.ρ0 : U.A0 →* U.A01) a0 * t) :
    (t' : U.A01) * U.ρ1 (a1 : U.A1) = U.ρ0 (a0 : U.A0) * (t : U.A01) := by
  have h' : (↑t' : U.A01) * (↑(Units.map (U.ρ1 : U.A1 →* U.A01) a1) : U.A01) =
      (↑(Units.map (U.ρ0 : U.A0 →* U.A01) a0) : U.A01) * (↑t : U.A01) := by
    rw [← Units.val_mul, ← Units.val_mul, h]
  rw [Units.coe_map, Units.coe_map] at h'
  rw [AlgHom.coe_toMonoidHom, AlgHom.coe_toMonoidHom] at h'
  exact h'

/-- **Coboundary criterion, element form.**  If the two trivializations satisfy
`t' * rho1 a1 = rho0 a0 * t` in `A01`, then the two line bundles are isomorphic.

The isomorphism is given by multiplication by the units `a0`, `a1` and `rho0 a0` on the three
modules; the relation above is exactly what is needed for the two commuting squares. -/
theorem lineBundle_iso_of_unit_val (t t' : U.A01ˣ) (a0 : U.A0ˣ) (a1 : U.A1ˣ)
    (h : (t' : U.A01) * U.ρ1 (a1 : U.A1) = U.ρ0 (a0 : U.A0) * (t : U.A01)) :
    Nonempty (SectionsIso (U.lineBundle t) (U.lineBundle t')) := by
  let u0 : U.A01ˣ :=
    ⟨U.ρ0 (a0 : U.A0), U.ρ0 ((a0⁻¹ : U.A0ˣ) : U.A0),
      by rw [← map_mul, Units.mul_inv, map_one],
      by rw [← map_mul, Units.inv_mul, map_one]⟩
  have hcoe0 : (u0 : U.A01) = U.ρ0 (a0 : U.A0) := rfl
  let e0 : (U.lineBundle t).M0 ≃ₗ[U.A0] (U.lineBundle t').M0 :=
    a0.mulLeftLinearEquiv U.A0 U.A0
  let e1 : (U.lineBundle t).M1 ≃ₗ[U.A1] (U.lineBundle t').M1 :=
    a1.mulLeftLinearEquiv U.A1 U.A1
  let e01 : (U.lineBundle t).M01 ≃ₗ[U.A01] (U.lineBundle t').M01 :=
    u0.mulLeftLinearEquiv U.A01 U.A01
  have hcomm0 : ∀ m : (U.lineBundle t).M0,
      e01 ((U.lineBundle t).r0 m) = (U.lineBundle t').r0 (e0 m) := by
    intro m
    show (u0 : U.A01) * U.ρ0 (m : U.A0) = U.ρ0 ((a0 : U.A0) * m)
    rw [hcoe0, map_mul]
  have hcomm1 : ∀ m : (U.lineBundle t).M1,
      e01 ((U.lineBundle t).r1 m) = (U.lineBundle t').r1 (e1 m) := by
    intro m
    show (u0 : U.A01) * ((t : U.A01) * U.ρ1 (m : U.A1)) =
      (t' : U.A01) * U.ρ1 ((a1 : U.A1) * m)
    rw [hcoe0, map_mul]
    calc (U.ρ0 (a0 : U.A0)) * ((t : U.A01) * U.ρ1 (m : U.A1))
        = (U.ρ0 (a0 : U.A0) * (t : U.A01)) * U.ρ1 (m : U.A1) := (mul_assoc _ _ _).symm
      _ = ((t' : U.A01) * U.ρ1 (a1 : U.A1)) * U.ρ1 (m : U.A1) := by rw [h]
      _ = (t' : U.A01) * (U.ρ1 (a1 : U.A1) * U.ρ1 (m : U.A1)) := mul_assoc _ _ _
  exact ⟨e0, e1, e01, hcomm0, hcomm1⟩

/-- **Coboundary criterion, multiplicative form.**  If the two trivializations differ by the
Cech coboundary `(rho0 a0, rho1 a1)`, written multiplicatively in `A01^x` as
`t' * rho1 a1 = rho0 a0 * t`, then the two line bundles are isomorphic. -/
theorem lineBundle_iso_of_mul (t t' : U.A01ˣ) (a0 : U.A0ˣ) (a1 : U.A1ˣ)
    (h : t' * Units.map (U.ρ1 : U.A1 →* U.A01) a1 =
      Units.map (U.ρ0 : U.A0 →* U.A01) a0 * t) :
    Nonempty (SectionsIso (U.lineBundle t) (U.lineBundle t')) :=
  lineBundle_iso_of_unit_val U t t' a0 a1 (coboundary_val U t t' a0 a1 h)

/-- **Coboundary criterion, unit form.**  Two line bundles whose trivializations differ by a
Cech coboundary `t' = rho0 a0 * t * (rho1 a1)^{-1}` are isomorphic. -/
theorem lineBundle_iso_of_unit (t t' : U.A01ˣ)
    (h : ∃ a0 : U.A0ˣ, ∃ a1 : U.A1ˣ,
      t' = Units.map (U.ρ0 : U.A0 →* U.A01) a0 * t *
        (Units.map (U.ρ1 : U.A1 →* U.A01) a1)⁻¹) :
    Nonempty (SectionsIso (U.lineBundle t) (U.lineBundle t')) := by
  obtain ⟨a0, a1, h⟩ := h
  refine lineBundle_iso_of_mul U t t' a0 a1 ?_
  rw [h, mul_assoc, inv_mul_cancel, mul_one]

/-- Every line bundle is isomorphic to itself. -/
theorem lineBundle_iso_refl (t : U.A01ˣ) :
    Nonempty (SectionsIso (U.lineBundle t) (U.lineBundle t)) :=
  ⟨LinearEquiv.refl U.A0 _, LinearEquiv.refl U.A1 _, LinearEquiv.refl U.A01 _,
    fun _ => rfl, fun _ => rfl⟩

end Cover

end TwoChartCech

/-! ### Axiom checks -/

#print axioms TwoChartCech.Cover.coboundary_val
#print axioms TwoChartCech.Cover.lineBundle_iso_of_unit_val
#print axioms TwoChartCech.Cover.lineBundle_iso_of_mul
#print axioms TwoChartCech.Cover.lineBundle_iso_of_unit
#print axioms TwoChartCech.Cover.lineBundle_iso_refl
