import tmp.sheaf.xif.paper.S2670Conductor1249Actual
import tmp.sheaf.xif.paper.S2537ConcreteLocalizationActual
import tmp.sheaf.xif.paper.S2592GenericLocalizedResidueIsoActual
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

noncomputable section
set_option maxHeartbeats 16000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S2669Kummer1249Actual
open LeanFormal.IUT.XiFPaper.S2670Conductor1249Actual
open LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual

namespace LeanFormal.IUT.XiFPaper.S2599cP1249Actual

abbrev O : Type := S2537ConcreteLocalizationActual.A
abbrev OL : Type := S2537ConcreteLocalizationActual.C
abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S

noncomputable def r1249 : ZMod 1249 :=
  Classical.choose S2669LinearFactor1249_proof

lemma hr1249 : (S2669minpolyMod S2579Theta).IsRoot r1249 :=
  Classical.choose_spec S2669LinearFactor1249_proof

noncomputable def p1249C : Ideal O :=
  Classical.choose (S2669_linearFactor_prime S2579Theta
    S2670_conductor1249 hr1249)

lemma p1249C_spec :
    p1249C.IsPrime ∧ p1249C.LiesOver (Ideal.span {(1249 : ℤ)}) ∧
      p1249C.inertiaDeg ℤ = 1 :=
  Classical.choose_spec (S2669_linearFactor_prime S2579Theta
    S2670_conductor1249 hr1249)

lemma p1249C_prime : p1249C.IsPrime := p1249C_spec.1
lemma p1249C_lies : p1249C.LiesOver (Ideal.span {(1249 : ℤ)}) := p1249C_spec.2.1
lemma p1249C_inertia : p1249C.inertiaDeg ℤ = 1 := p1249C_spec.2.2

lemma p1249C_ne_bot : p1249C ≠ ⊥ := by
  intro h
  have hle : (1249 : ℤ) ∈ p1249C.under ℤ := by
    rw [← p1249C_lies.over]
    exact Ideal.mem_span_singleton_self 1249
  rw [h, Ideal.under_bot] at hle
  have h0 : (1249 : ℤ) = 0 := Ideal.mem_bot.mp hle
  norm_num at h0

lemma ten_not_mem_p1249C : (10 : O) ∉ p1249C := by
  intro h10
  have h10' : algebraMap ℤ O (10 : ℤ) ∈ p1249C := by simpa using h10
  have hu : (10 : ℤ) ∈ p1249C.under ℤ :=
    (Ideal.mem_under O p1249C).mpr h10'
  rw [← p1249C_lies.over] at hu
  have hdvd : (1249 : ℤ) ∣ 10 := Ideal.mem_span_singleton.mp hu
  norm_num at hdvd

lemma hdisj : Disjoint (Submonoid.powers (10 : O) : Set O)
    (p1249C : Set O) := by
  rw [Set.disjoint_left]
  intro x hx hxp
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x (10 : O)).mp hx
  exact ten_not_mem_p1249C (p1249C_prime.mem_of_pow_mem n hxp)

noncomputable def p1249R : Ideal R10 :=
  p1249C.map (algebraMap O R10)

lemma p1249R_prime : p1249R.IsPrime := by
  haveI : p1249C.IsPrime := p1249C_prime
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (M := Submonoid.powers (10 : O)) R10 p1249C p1249C_prime hdisj

lemma p1249R_lies : p1249R.LiesOver p1249C := by
  haveI : p1249C.IsPrime := p1249C_prime
  exact IsLocalization.liesOver_map_of_isPrime_disjoint
    (M := Submonoid.powers (10 : O)) R10 hdisj

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

lemma p1249C_max : p1249C.IsMaximal := by
  haveI : (Ideal.span {(1249 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 1249
  haveI : p1249C.IsPrime := p1249C_prime
  haveI : p1249C.LiesOver (Ideal.span {(1249 : ℤ)}) := p1249C_lies
  exact Ideal.IsMaximal.of_liesOver_isMaximal
    (p := Ideal.span {(1249 : ℤ)}) (P := p1249C)

lemma p1249R_max : p1249R.IsMaximal := by
  haveI : (p1249R.under O).IsMaximal := by
    change (Ideal.under O (Ideal.map (algebraMap O R10) p1249C)).IsMaximal
    rw [IsLocalization.under_map_of_isPrime_disjoint
      (M := Submonoid.powers (10 : O)) R10 p1249C_prime hdisj]
    exact p1249C_max
  exact Ideal.IsMaximal.of_isLocalization_of_disjoint
    (M := Submonoid.powers (10 : O)) (S := R10) (J := p1249R)

#check p1249C
#check p1249R_prime
#check p1249R_max
#print axioms p1249R_max
noncomputable def P0 : Ideal OL := by
  haveI : p1249C.IsMaximal := p1249C_max
  exact Classical.choose (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := O) (S := OL) (P := p1249C))

lemma P0_spec : P0.IsMaximal ∧ P0.LiesOver p1249C := by
  haveI : p1249C.IsMaximal := p1249C_max
  exact Classical.choose_spec (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := O) (S := OL) (P := p1249C))

lemma P0_max : P0.IsMaximal := P0_spec.1
lemma P0_lies : P0.LiesOver p1249C := P0_spec.2

lemma P0_ne_bot : P0 ≠ ⊥ := by
  intro hbot
  have hunder : p1249C = (⊥ : Ideal O) := by
    calc p1249C = P0.under O := P0_lies.over
      _ = (⊥ : Ideal O) := by rw [hbot, Ideal.under_bot]
  exact p1249C_ne_bot hunder

lemma ten_not_mem_P0 : (10 : OL) ∉ P0 := by
  intro h10
  have h10' : algebraMap O OL (10 : O) ∈ P0 := by
    have hmap : algebraMap O OL (10 : O) = (10 : OL) := by
      rw [show (10 : O) = ((10 : ℕ) : O) by norm_num]
      exact map_natCast (algebraMap O OL) 10
    rw [hmap]
    exact h10
  have hu : (10 : O) ∈ P0.under O :=
    (Ideal.mem_under O P0).mpr h10'
  rw [← P0_lies.over] at hu
  exact ten_not_mem_p1249C hu

lemma hdisjOL : Disjoint (Algebra.algebraMapSubmonoid OL
    (Submonoid.powers (10 : O)) : Set OL) (P0 : Set OL) := by
  rw [Set.disjoint_left]
  intro x hx hxp
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a (10 : O)).mp ha
  rw [← hn, map_pow] at hxp
  exact ten_not_mem_P0 ((P0_max.isPrime).mem_of_pow_mem n hxp)

noncomputable def P1249T : Ideal T10 :=
  P0.map (algebraMap OL T10)

lemma P1249T_prime : P1249T.IsPrime := by
  haveI : P0.IsPrime := P0_max.isPrime
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : O)))
    T10 P0 P0_max.isPrime hdisjOL

lemma P1249T_lies : P1249T.LiesOver p1249R := by
  haveI : P0.IsMaximal := P0_max
  haveI : P1249T.IsPrime := P1249T_prime
  have hmax : (Ideal.map (algebraMap O R10) (P0.under O)).IsMaximal := by
    rw [← P0_lies.over]
    exact p1249R_max
  have hne : P0.map (algebraMap OL T10) ≠ ⊤ :=
    P1249T_prime.ne_top
  have h := Ideal.under_map_eq_map_under (A := O) (B := OL)
    (C := R10) (D := T10) (P := P0) hmax hne
  refine ⟨?_.symm⟩
  change p1249R = (Ideal.map (algebraMap OL T10) P0).under R10
  rw [h]
  exact (P0_lies.over).symm ▸ rfl

lemma P1249T_max : P1249T.IsMaximal := by
  haveI : p1249R.IsMaximal := p1249R_max
  haveI : P1249T.IsPrime := P1249T_prime
  haveI : P1249T.LiesOver p1249R := P1249T_lies
  haveI : IsIntegralClosure T10 R10 S2537ConcreteLocalizationActual.L :=
    S2537_isIntegralClosure
  haveI : Algebra.IsIntegral R10 T10 :=
    IsIntegralClosure.isIntegral_algebra R10 S2537ConcreteLocalizationActual.L
  exact Ideal.IsMaximal.of_liesOver_isMaximal (p := p1249R) (P := P1249T)

noncomputable instance fintype_quot_O_p1249C : Fintype (O ⧸ p1249C) := by
  haveI : Ring.HasFiniteQuotients O :=
    Ring.HasFiniteQuotients.of_module_finite (R := ℤ) O
  haveI : Finite (O ⧸ p1249C) :=
    Ring.HasFiniteQuotients.finiteQuotient p1249C_ne_bot
  exact Fintype.ofFinite _

instance decEq_quot_O_p1249C : DecidableEq (O ⧸ p1249C) := Classical.decEq _

lemma p1249R_under : p1249R.comap (algebraMap O R10) = p1249C := by
  haveI : p1249C.IsPrime := p1249C_prime
  have h := IsLocalization.under_map_of_isPrime_disjoint
    (M := Submonoid.powers (10 : O)) R10 p1249C_prime hdisj
  simpa [p1249R, Ideal.under] using h

noncomputable def eR : (O ⧸ p1249C) ≃+* (R10 ⧸ p1249R) := by
  haveI : p1249C.IsMaximal := p1249C_max
  haveI : p1249R.IsPrime := p1249R_prime
  exact localizedResidueEquiv (M := Submonoid.powers (10 : O))
    (I := p1249C) (P := p1249R) p1249R_under

noncomputable instance fintype_quot_R10_p1249R : Fintype (R10 ⧸ p1249R) :=
  Fintype.ofEquiv (O ⧸ p1249C) eR

instance decEq_quot_R10_p1249R : DecidableEq (R10 ⧸ p1249R) := Classical.decEq _

lemma P1249T_under : P1249T.comap (algebraMap OL T10) = P0 := by
  haveI : P0.IsPrime := P0_max.isPrime
  have h := IsLocalization.under_map_of_isPrime_disjoint
    (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : O)))
    T10 P0_max.isPrime hdisjOL
  simpa [P1249T, Ideal.under] using h

noncomputable def eT : (OL ⧸ P0) ≃+* (T10 ⧸ P1249T) := by
  haveI : P0.IsMaximal := P0_max
  haveI : P1249T.IsPrime := P1249T_prime
  exact localizedResidueEquiv
    (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : O)))
    (I := P0) (P := P1249T) P1249T_under

noncomputable instance fintype_quot_OL_P0 : Fintype (OL ⧸ P0) := by
  haveI : Ring.HasFiniteQuotients OL :=
    Ring.HasFiniteQuotients.of_module_finite (R := ℤ) OL
  haveI : Finite (OL ⧸ P0) :=
    Ring.HasFiniteQuotients.finiteQuotient P0_ne_bot
  exact Fintype.ofFinite _

instance decEq_quot_OL_P0 : DecidableEq (OL ⧸ P0) := Classical.decEq _

noncomputable instance fintype_quot_T10_P1249T : Fintype (T10 ⧸ P1249T) :=
  Fintype.ofEquiv (OL ⧸ P0) eT

instance decEq_quot_T10_P1249T : DecidableEq (T10 ⧸ P1249T) := Classical.decEq _

#check eR
#check eT
#synth Fintype (R10 ⧸ p1249R)
#synth Fintype (T10 ⧸ P1249T)
#synth DecidableEq (R10 ⧸ p1249R)
#synth DecidableEq (T10 ⧸ P1249T)

#check P0
#check P1249T_prime
#check P1249T_lies
#check P1249T_max
#print axioms P1249T_max

end LeanFormal.IUT.XiFPaper.S2599cP1249Actual
end