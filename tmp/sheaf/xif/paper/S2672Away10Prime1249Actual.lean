import tmp.sheaf.xif.paper.S2669Kummer1249Actual
import tmp.sheaf.xif.paper.S2537ConcreteLocalizationActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2672Away10Prime1249Actual

open LeanFormal.IUT.XiFPaper.S2669Kummer1249Actual
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

theorem S2672_ten_not_mem (p : Ideal A) [p.IsPrime]
    (hp : p.LiesOver (Ideal.span {(1249 : ℤ)})) : (10 : A) ∉ p := by
  intro h10
  have h10z : (10 : ℤ) ∈ p.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using h10
  have hspan : (10 : ℤ) ∈ Ideal.span {(1249 : ℤ)} := by
    rw [hp.over]
    exact h10z
  have hdiv : (1249 : ℤ) ∣ 10 := Ideal.mem_span_singleton.mp hspan
  norm_num at hdiv

theorem S2672_quotient_equiv (p : Ideal A) [p.IsPrime]
    (hp : p.LiesOver (Ideal.span {(1249 : ℤ)}))
    (e : A ⧸ p ≃+* ZMod 1249) :
    ∃ PR : Ideal R, PR.IsPrime ∧ PR.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      Nonempty (R ⧸ PR ≃+* ZMod 1249) := by
  haveI hmax0 : (Ideal.span {(1249 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 1249
  haveI : p.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal p (Ideal.span {(1249 : ℤ)})
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  have h10ne : algebraMap A (A ⧸ p) (10 : A) ≠ 0 := by
    intro h
    exact S2672_ten_not_mem p hp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hunit : ∀ y : M, IsUnit (Ideal.Quotient.mk p (y : A)) := by
    intro y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (y : A) (10 : A)).mp y.2
    have hval : Ideal.Quotient.mk p (y : A) = (algebraMap A (A ⧸ p) (10 : A)) ^ n := by
      rw [← hn]
      simp only [map_pow]
      rfl
    rw [hval]
    exact (isUnit_iff_ne_zero.mpr h10ne).pow n
  let ψ0 : R →+* A ⧸ p :=
    IsLocalization.lift (M := M) (g := Ideal.Quotient.mk p) hunit
  let ψ : R →+* ZMod 1249 := e.toRingHom.comp ψ0
  have hψ_surj : Function.Surjective ψ := by
    intro x
    obtain ⟨z, rfl⟩ := e.surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨algebraMap A R a, ?_⟩
    change e (ψ0 (algebraMap A R a)) = e (Ideal.Quotient.mk p a)
    congr 1
    exact IsLocalization.lift_eq (M := M) (S := R)
      (g := Ideal.Quotient.mk p) hunit a
  let PR : Ideal R := RingHom.ker ψ
  have hPRp : PR.IsPrime := RingHom.ker_isPrime ψ
  have hPRmax : PR.IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hψ_surj
  have hcomp : ψ.comp (algebraMap A R) = e.toRingHom.comp (Ideal.Quotient.mk p) := by
    ext a
    change e (ψ0 (algebraMap A R a)) = e (Ideal.Quotient.mk p a)
    congr 1
    exact IsLocalization.lift_eq (M := M) (S := R)
      (g := Ideal.Quotient.mk p) hunit a
  have hunderA : PR.under A = p := by
    change RingHom.ker (ψ.comp (algebraMap A R)) = p
    rw [hcomp]
    ext a
    change e ((Ideal.Quotient.mk p) a) = 0 ↔ a ∈ p
    constructor
    · intro h
      exact Ideal.Quotient.eq_zero_iff_mem.mp (e.injective (by simpa using h))
    · intro h
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
  have hlies : PR.LiesOver (Ideal.span {(1249 : ℤ)}) := by
    refine ⟨?_⟩
    change Ideal.span {(1249 : ℤ)} = PR.under ℤ
    have h : PR.under ℤ = (PR.under A).under ℤ :=
      (Ideal.under_under (A := ℤ) (B := A) (𝔓 := PR)).symm
    rw [h, hunderA]
    exact hp.over
  exact ⟨PR, hPRp, hlies, ⟨ψ.quotientKerEquivOfSurjective hψ_surj⟩⟩

theorem S2672_prime1249_away10 :
    ∃ PR : Ideal R, PR.IsPrime ∧ PR.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      Nonempty (R ⧸ PR ≃+* ZMod 1249) := by
  obtain ⟨p, hp, hplies, hdeg, ⟨e⟩, P, hP, hPp, hPover, hPS⟩ := S2669_exists_primeDegreeOne
  haveI : p.IsPrime := hp
  exact S2672_quotient_equiv p hplies e

#check S2672_prime1249_away10
#print axioms S2672_prime1249_away10

end LeanFormal.IUT.XiFPaper.S2672Away10Prime1249Actual
end
