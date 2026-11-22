import tmp.sheaf.xif.paper.S2661P10Actual
import tmp.sheaf.xif.paper.S2595LResidueEquivActual
import tmp.sheaf.xif.paper.S2588FbarIrreducibleActual

noncomputable section
set_option maxHeartbeats 8000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2661P10Actual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2595LResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2588FbarIrreducibleActual

namespace LeanFormal.IUT.XiFPaper.S2663P10PrimeActual

abbrev O : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev SC : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev OL : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.C
abbrev T10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S

noncomputable def D (W : S2584PrimeDegreeOneWitness) : S2587LocalizedResidueDataS :=
  S2587ResidueDataOfWitness W
    (S2588FbarIrreducibleActual.S2587FbarIrreducibleRequired_holds W)

theorem D_p_eq (W : S2584PrimeDegreeOneWitness) : (D W).p = W.P :=
  rfl

theorem h613_mem_P (W : S2584PrimeDegreeOneWitness) :
    (algebraMap ℤ SC) (613 : ℤ) ∈ W.P := by
  have hL : W.P.under ℤ = Ideal.span ({(613 : ℤ)} : Set ℤ) :=
    W.P_liesOver.over.symm
  have h : (613 : ℤ) ∈ W.P.under ℤ := by
    rw [hL]
    exact Ideal.mem_span_singleton_self 613
  rwa [Ideal.mem_under] at h

theorem h613 (W : S2584PrimeDegreeOneWitness) :
    (algebraMap ℤ SC) (613 : ℤ) ∈ (D W).p := by
  rw [D_p_eq W]
  exact h613_mem_P W

noncomputable def q (W : S2584PrimeDegreeOneWitness) : Ideal O :=
  (D W).p.comap (algebraMap O SC)

theorem q_eq (W : S2584PrimeDegreeOneWitness) : q W = W.p := by
  unfold q
  rw [D_p_eq W]
  exact W.P_liesOver_p.over.symm

noncomputable def P0 (W : S2584PrimeDegreeOneWitness) : Ideal OL :=
  S2595P0 (D W) (h613 W)

theorem P0_prime (W : S2584PrimeDegreeOneWitness) : (P0 W).IsPrime :=
  (S2595P0_max (D W) (h613 W)).isPrime

theorem P0_lies (W : S2584PrimeDegreeOneWitness) :
    (P0 W).LiesOver (q W) :=
  S2595P0_lies (D W) (h613 W)

theorem h10_not_mem_P0 (W : S2584PrimeDegreeOneWitness) :
    (algebraMap O OL (10 : O)) ∉ P0 W := by
  intro h
  have h10under : (10 : O) ∈ (P0 W).under O :=
    (Ideal.mem_under O (P0 W)).mpr h
  rw [← (P0_lies W).over] at h10under
  have hq : (10 : O) ∈ q W := h10under
  rw [q_eq W] at hq
  exact h10_not_mem W hq

noncomputable def P10 (W : S2584PrimeDegreeOneWitness) : Ideal T10 :=
  (P0 W).map (algebraMap OL T10)

theorem hdisj (W : S2584PrimeDegreeOneWitness) :
    Disjoint (Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : O)) : Set OL)
      (P0 W : Set OL) := by
  rw [Set.disjoint_left]
  intro x hx hxp
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff a (10 : O)).mp ha
  subst hn
  cases n with
  | zero =>
      exact (P0_prime W).ne_top
        (Ideal.eq_top_iff_one (P0 W) |>.mpr (by simpa using hxp))
  | succ n =>
      rw [map_pow] at hxp
      exact h10_not_mem_P0 W ((P0_prime W).mem_of_pow_mem (n + 1) hxp)

theorem P10_prime (W : S2584PrimeDegreeOneWitness) : (P10 W).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : O)))
    T10 (P0 W) (P0_prime W) (hdisj W)

#check P10_prime
theorem P10_lies_p10 (W : S2584PrimeDegreeOneWitness) :
    (P10 W).LiesOver (p10 W) := by
  have hp10 : Ideal.map (algebraMap O R10) ((P0 W).under O) = p10 W := by
    rw [← (P0_lies W).over]
    rw [q_eq W]
    rfl
  have hmax : (Ideal.map (algebraMap O R10) ((P0 W).under O)).IsMaximal := by
    rw [hp10]
    exact p10_isMaximal W
  have hne : Ideal.map (algebraMap OL T10) (P0 W) ≠ ⊤ :=
    (P10_prime W).ne_top
  have h := Ideal.under_map_eq_map_under (A := O) (B := OL)
    (C := R10) (D := T10) (P := P0 W) hmax hne
  refine ⟨?_.symm⟩
  change p10 W = Ideal.under R10
    (Ideal.map (algebraMap OL T10) (P0 W))
  rw [h, hp10]

#check P10_lies_p10
theorem P10_isMaximal (W : S2584PrimeDegreeOneWitness) :
    (P10 W).IsMaximal := by
  haveI hint : Algebra.IsIntegral R10 T10 := by
    haveI : Algebra.IsIntegral O OL := inferInstance
    have h : (IsLocalization.map T10 (algebraMap O OL)
        (show Submonoid.powers (10 : O) ≤
          (Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : O))).comap
            (algebraMap O OL) from Submonoid.le_comap_map _)).IsIntegral :=
      isIntegral_localization (R := O) (S := OL)
        (M := Submonoid.powers (10 : O)) (Rₘ := R10) (Sₘ := T10)
    rw [Algebra.isIntegral_def]
    intro x
    exact h x
  haveI : (P10 W).IsPrime := P10_prime W
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
    (R := R10) (S := T10) (I := P10 W) ?_
  rw [show (P10 W).comap (algebraMap R10 T10) = p10 W from
    (P10_lies_p10 W).over.symm]
  exact p10_isMaximal W

#check P10_isMaximal

#check P10_lies_p10
#check P10_prime
end LeanFormal.IUT.XiFPaper.S2663P10PrimeActual
end
