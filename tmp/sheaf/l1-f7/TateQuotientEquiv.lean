import LeanFormal.IUT.Foundations.Geometry.TateCoordinateNormalization
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMap
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Units.Hom

namespace LeanFormal.IUT.TateCurve

noncomputable section

universe u

variable {K : Type u} [Field K]

def tateParameterUnit (q : K) (hq0 : q ≠ 0)
    (u : ↥(coordinateParameterDomain q)) : Kˣ :=
  Units.mk0 (u : K) u.2.1

noncomputable def tateParameterClass (q : K) (hq0 : q ≠ 0) :
    TateParameterQuotient q hq0 →
      Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0) :=
  Quotient.lift
    (fun u => QuotientGroup.mk' _ (tateParameterUnit q hq0 u))
    (by
      intro u v huv
      obtain ⟨m, hm⟩ := huv
      have hunit : tateParameterUnit q hq0 v =
          tateParameterUnit q hq0 u * (Units.mk0 q hq0) ^ m := by
        apply Units.ext
        simp only [tateParameterUnit, Units.val_mk0, Units.val_mul,
          Units.val_zpow_eq_zpow_val]
        exact hm.symm.trans (mul_comm (q ^ m) (u : K))
      rw [hunit, map_mul, map_zpow]
      have hmem : Units.mk0 q hq0 ∈ Subgroup.zpowers (Units.mk0 q hq0) :=
        Subgroup.mem_zpowers _
      have hpow : (Units.mk0 q hq0) ^ m ∈ Subgroup.zpowers (Units.mk0 q hq0) :=
        (Subgroup.zpowers (Units.mk0 q hq0)).zpow_mem hmem m
      have hzero : ((QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 q hq0))
          (Units.mk0 q hq0) :
            Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0)) ^ m) = 1 := by
        rw [← map_zpow (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 q hq0)))
          (Units.mk0 q hq0) m]
        exact (QuotientGroup.eq_one_iff _).mpr hpow
      rw [hzero]
      exact (mul_one (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 q hq0))
        (tateParameterUnit q hq0 u))).symm)

noncomputable def tateOptionToQuotient (q : K) (hq0 : q ≠ 0) :
    Option (TateParameterQuotient q hq0) →
      Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0)
  | none => 1
  | some w => tateParameterClass q hq0 w


theorem tateOptionToQuotient_none (q : K) (hq0 : q ≠ 0) :
    tateOptionToQuotient q hq0 none = 1 := rfl


theorem tateParameterUnit_mem_zpowers_of_pole (q : K) (hq0 : q ≠ 0)
    {u : Kˣ} {n : ℤ} (hn : q ^ n * (u : K) = 1) :
    u ∈ Subgroup.zpowers (Units.mk0 q hq0) := by
  have hu_eq : u = (Units.mk0 q hq0) ^ (-n) := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_zpow_eq_zpow_val]
    exact (eq_inv_of_mul_eq_one_right hn).trans (by rw [← zpow_neg])
  rw [hu_eq]
  exact (Subgroup.zpowers (Units.mk0 q hq0)).zpow_mem
    (Subgroup.mem_zpowers _) (-n)

theorem tateOptionToQuotient_surjective (q : K) (hq0 : q ≠ 0) :
    Function.Surjective (tateOptionToQuotient q hq0) := by
  intro x
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    (Subgroup.zpowers (Units.mk0 q hq0)) x
  by_cases hmem : u ∈ Subgroup.zpowers (Units.mk0 q hq0)
  · refine ⟨none, ?_⟩
    rw [tateOptionToQuotient_none, ← hu]
    exact ((QuotientGroup.eq_one_iff u).mpr hmem).symm
  · let udom : ↥(coordinateParameterDomain q) :=
      ⟨(u : K), ⟨u.ne_zero, by
        intro n hn
        exact hmem (tateParameterUnit_mem_zpowers_of_pole q hq0 hn)⟩⟩
    refine ⟨some (Quotient.mk _ udom), ?_⟩
    rw [← hu]
    change (QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 q hq0))
      (tateParameterUnit q hq0 udom) =
        QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 q hq0)) u)
    congr 1
    exact Units.ext rfl

theorem tateOptionToQuotient_injective (q : K) (hq0 : q ≠ 0) :
    Function.Injective (tateOptionToQuotient q hq0) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some w =>
      exfalso
      induction w using Quotient.inductionOn with
      | h u =>
        have hmem : tateParameterUnit q hq0 u ∈ Subgroup.zpowers (Units.mk0 q hq0) :=
          (QuotientGroup.eq_one_iff (N := Subgroup.zpowers (Units.mk0 q hq0))
            (tateParameterUnit q hq0 u)).mp
            (by simpa [tateOptionToQuotient, tateParameterClass] using hab.symm)
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hval : q ^ m = (u : K) := by
          simpa only [tateParameterUnit, Units.val_mk0, Units.val_zpow_eq_zpow_val] using
            congrArg (fun z : Kˣ => (z : K)) hm
        have hcontr : q ^ (-m) * (u : K) = 1 := by
          rw [← hval, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero]
        exact u.property.2 (-m) hcontr
  | some w =>
    cases b with
    | none =>
      exfalso
      induction w using Quotient.inductionOn with
      | h u =>
        have hmem : tateParameterUnit q hq0 u ∈ Subgroup.zpowers (Units.mk0 q hq0) :=
          (QuotientGroup.eq_one_iff (N := Subgroup.zpowers (Units.mk0 q hq0))
            (tateParameterUnit q hq0 u)).mp
            (by simpa [tateOptionToQuotient, tateParameterClass] using hab)
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hval : q ^ m = (u : K) := by
          simpa only [tateParameterUnit, Units.val_mk0, Units.val_zpow_eq_zpow_val] using
            congrArg (fun z : Kˣ => (z : K)) hm
        have hcontr : q ^ (-m) * (u : K) = 1 := by
          rw [← hval, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero]
        exact u.property.2 (-m) hcontr
    | some w' =>
      induction w using Quotient.inductionOn with
      | h u =>
        induction w' using Quotient.inductionOn with
        | h v =>
          have hq : QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 q hq0))
              (tateParameterUnit q hq0 u) =
              QuotientGroup.mk' (Subgroup.zpowers (Units.mk0 q hq0))
                (tateParameterUnit q hq0 v) := hab
          obtain ⟨z, hzN, hz⟩ := (QuotientGroup.mk'_eq_mk' (N := Subgroup.zpowers (Units.mk0 q hq0))).mp hq
          obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzN
          have hzu : (u : K) * q ^ m = (v : K) := by
            have hzK : (z : K) = q ^ m := by
              simpa only [Units.val_mk0, Units.val_zpow_eq_zpow_val] using
                (congrArg (fun z : Kˣ => (z : K)) hm).symm
            have hz' := congrArg (fun z : Kˣ => (z : K)) hz
            simpa only [Units.val_mul, tateParameterUnit, Units.val_mk0, hzK] using hz'
          apply congrArg some
          apply Quotient.sound
          refine ⟨m, ?_⟩
          rw [mul_comm, hzu]

noncomputable def unitsQuotientEquivOption (q : K) (hq0 : q ≠ 0) :
    (Kˣ ⧸ Subgroup.zpowers (Units.mk0 q hq0)) ≃
      Option (TateParameterQuotient q hq0) :=
  (Equiv.ofBijective (tateOptionToQuotient q hq0)
    ⟨tateOptionToQuotient_injective q hq0, tateOptionToQuotient_surjective q hq0⟩).symm

end

end LeanFormal.IUT.TateCurve
