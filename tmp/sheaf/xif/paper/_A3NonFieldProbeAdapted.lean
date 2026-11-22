import Mathlib

noncomputable section
open Polynomial

namespace A3NonFieldProbe

def c0 : ℤ := 463856467968
def Dval : ℤ :=
  4345305365083382316090978154266740962137056508754049584537562001452629669347552693333318628339444576241125166305517397135246066050452111172703998714925023232000000000000000000000000
noncomputable def Cden : ℤ := c0 * Dval
lemma Cden_ne_zero : Cden ≠ 0 := by unfold Cden c0 Dval; norm_num
abbrev R : Type := Localization (Submonoid.powers Cden)

def q : ℕ := 11
instance : Fact q.Prime := ⟨by decide⟩

lemma Cden_mod_q : ((Cden : ℤ) : ZMod q) ≠ 0 := by
  unfold q Cden c0 Dval
  decide

noncomputable def hg : ∀ y : Submonoid.powers (Cden : ℤ),
    IsUnit ((Int.castRingHom (ZMod q)) (y : ℤ)) := by
  intro y
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (y : ℤ) Cden).mp y.2
  rw [← hn, map_pow]
  refine IsUnit.pow n ?_
  rw [isUnit_iff_ne_zero]
  simpa using Cden_mod_q

noncomputable def h : R →+* ZMod q :=
  IsLocalization.lift (M := Submonoid.powers (Cden : ℤ)) (g := Int.castRingHom (ZMod q)) hg

lemma h_apply (x : ℤ) : h (algebraMap ℤ R x) = (x : ZMod q) :=
  IsLocalization.lift_eq hg x

example : h (algebraMap ℤ R 11) = (0 : ZMod q) := by
  rw [h_apply]
  decide

example : ¬ IsField R := by
  intro hf
  letI := hf.toField
  have hne : algebraMap ℤ R 11 ≠ 0 := by
    intro h0
    have hz : (11 : ℤ) = 0 := IsLocalization.injective R
      (M := Submonoid.powers (Cden : ℤ))
      (by rw [Submonoid.powers_le]; exact mem_nonZeroDivisors_of_ne_zero Cden_ne_zero)
      (by simpa using h0)
    norm_num at hz
  have hunit : IsUnit (algebraMap ℤ R 11) := isUnit_iff_ne_zero.mpr hne
  have hunit0 : IsUnit (h (algebraMap ℤ R 11)) := hunit.map h
  have hzero : h (algebraMap ℤ R 11) = 0 := by rw [h_apply]; decide
  rw [hzero] at hunit0
  exact not_isUnit_zero hunit0

end A3NonFieldProbe
