import tmp.sheaf.xif.paper.S2660R10ModelActual
import tmp.sheaf.xif.paper.S2656Residue1249Actual
import tmp.sheaf.xif.paper.S2493UnitScalingActual
import tmp.sheaf.xif.paper.S2531Mod1249FactorDegreesActual

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2660R10ModelActual
open LeanFormal.IUT.XiFPaper.S2548Prime1249Actual
open LeanFormal.IUT.XiFPaper.S2656Residue1249Actual
open LeanFormal.IUT.XiFPaper.S2493UnitScalingActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2531Mod1249FactorDegreesActual

namespace LeanFormal.IUT.XiFPaper.S2661Away10Prime1249Actual

lemma phi1249_ten_ne_zero : phi1249 (10 : A) ≠ 0 := by
  have h : (10 : A) = algebraMap ℤ A (10 : ℤ) := by norm_num
  rw [h, phi1249_int]
  norm_num

lemma phi1249_ten_unit : IsUnit (phi1249 (10 : A)) :=
  isUnit_iff_ne_zero.mpr phi1249_ten_ne_zero

theorem psiR_exists : ∃ g : R →+* ZMod 1249,
    ∀ a : A, g (algebraMap A R a) = phi1249 a := by
  refine ⟨IsLocalization.lift (M := M) (S := R) (g := phi1249) ?_, ?_⟩
  · intro y hy
    obtain ⟨n, rfl⟩ := hy
    rw [map_pow]
    exact IsUnit.pow n phi1249_ten_unit
  · intro a
    exact IsLocalization.lift_eq (M := M) (S := R) (g := phi1249)
      (fun y hy => by
        obtain ⟨n, rfl⟩ := hy
        rw [map_pow]
        exact IsUnit.pow n phi1249_ten_unit) a

noncomputable def psiR : R →+* ZMod 1249 :=
  Classical.choose psiR_exists

theorem psiR_algebraMap (a : A) : psiR (algebraMap A R a) = phi1249 a :=
  (Classical.choose_spec psiR_exists a)

theorem psiR_surjective : Function.Surjective psiR := by
  intro x
  obtain ⟨a, rfl⟩ := phi1249_surjective x
  exact ⟨algebraMap A R a, psiR_algebraMap a⟩

def p1249R : Ideal R := RingHom.ker psiR

lemma p1249R_isMaximal : p1249R.IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective psiR psiR_surjective

noncomputable def residueEquivR : R ⧸ p1249R ≃+* ZMod 1249 :=
  psiR.quotientKerEquivOfSurjective psiR_surjective

@[simp] theorem residueEquivR_mk (x : R) :
    residueEquivR (Ideal.Quotient.mk p1249R x) = psiR x := rfl

#check psiR
#check p1249R
#check residueEquivR
#print axioms p1249R_isMaximal

end LeanFormal.IUT.XiFPaper.S2661Away10Prime1249Actual
end