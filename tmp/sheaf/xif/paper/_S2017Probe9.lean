import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs

set_option maxHeartbeats 1600000
noncomputable section

namespace ProbeTransfer

variable {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]

noncomputable def verlagerung : Abelianization G →* Abelianization H :=
  Abelianization.lift (MonoidHom.transfer (Abelianization.of (G := H)))

theorem verlagerung_of (g : G) :
    verlagerung H (Abelianization.of g) =
      MonoidHom.transfer (Abelianization.of (G := H)) g := rfl

theorem map_subtype_verlagerung_of (g : G) :
    Abelianization.map H.subtype (verlagerung H (Abelianization.of g)) =
      Abelianization.of (g ^ H.index) := by
  classical
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [verlagerung_of, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  simp only [map_prod, Abelianization.map_of, Subgroup.coe_subtype]
  have hfactor : ∀ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
      Abelianization.of ((Quotient.out q.out)⁻¹ * g ^
          Function.minimalPeriod (fun x => g • x) q.out * Quotient.out q.out) =
        Abelianization.of (g ^ Function.minimalPeriod (fun x => g • x) q.out) := by
    intro q
    simp only [map_mul, map_inv, map_pow]
    rw [mul_comm (Abelianization.of (Quotient.out q.out))⁻¹, mul_assoc,
      inv_mul_cancel, mul_one]
  simp_rw [hfactor]
  calc
    ∏ x : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
        Abelianization.of (g ^ Function.minimalPeriod (fun y => g • y) x.out)
        = ∏ x : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
            (Abelianization.of g) ^ Function.minimalPeriod (fun y => g • y) x.out := by
          apply Finset.prod_congr rfl
          intro x _
          rw [map_pow]
    _ = (Abelianization.of g) ^ H.index := by
          rw [Finset.prod_pow_eq_pow_sum, ← H.index_eq_sum_minimalPeriod]
    _ = Abelianization.of (g ^ H.index) := by rw [map_pow]

noncomputable def powIndexHom : G →* Abelianization G where
  toFun g := Abelianization.of (g ^ H.index)
  map_one' := by simp
  map_mul' g h := by
    rw [map_pow, map_mul, mul_pow, map_pow, map_pow]

theorem map_subtype_comp_verlagerung_apply (x : Abelianization G) :
    Abelianization.map H.subtype (verlagerung H x) =
      Abelianization.lift (powIndexHom H) x :=
  Abelianization.lift_unique (powIndexHom H)
    ((Abelianization.map H.subtype).comp (verlagerung H))
    (fun g => map_subtype_verlagerung_of H g)

theorem map_subtype_comp_verlagerung :
    (Abelianization.map H.subtype).comp (verlagerung H) =
      Abelianization.lift (powIndexHom H) :=
  MonoidHom.ext (fun x => map_subtype_comp_verlagerung_apply H x)

end ProbeTransfer
