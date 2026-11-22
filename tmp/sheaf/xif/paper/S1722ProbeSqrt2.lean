import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeSqrt2

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

abbrev F := S1720Field

theorem S1687P_ne_zero' : S1687P ≠ 0 := by
  intro h
  have hdeg : S1687P.natDegree = 3 := by unfold S1687P; compute_degree!
  rw [h, Polynomial.natDegree_zero] at hdeg
  norm_num at hdeg

theorem H_eq_comp : S1687H = S1687P.comp (X ^ 2) := by
  unfold S1687H S1687P
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.X_pow_comp]
  ring_nf

theorem sqrt_splits (c : S1687P.rootSet F) :
    ((X ^ 2 - C (c : F)) : F[X]).Splits := by
  have hH : (S1687H.map (algebraMap ℚ F)).Splits := S1687H_splits_in_F'
  have hHne : (S1687H.map (algebraMap ℚ F)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℚ F).injective]
    exact S1687H_ne_zero
  have hc : aeval (c : F) S1687P = 0 :=
    (Polynomial.mem_rootSet_of_ne S1687P_ne_zero').mp c.2
  have hlin : (X - C (c : F)) ∣ S1687P.map (algebraMap ℚ F) :=
    Polynomial.dvd_iff_isRoot.mpr (by
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hc)
  have hcomp : ((X - C (c : F)).comp (X ^ 2)) ∣
      ((S1687P.map (algebraMap ℚ F)).comp (X ^ 2)) := by
    rcases hlin with ⟨q, hq⟩
    refine ⟨q.comp (X ^ 2), ?_⟩
    rw [hq, Polynomial.mul_comp]
  have hleft : (X - C (c : F)).comp (X ^ 2) = X ^ 2 - C (c : F) := by
    simp [Polynomial.sub_comp]
  have hright : (S1687P.map (algebraMap ℚ F)).comp (X ^ 2) =
      S1687H.map (algebraMap ℚ F) := by
    rw [H_eq_comp, Polynomial.map_comp]
    simp
  rw [hleft, hright] at hcomp
  exact Polynomial.Splits.of_dvd hH hHne hcomp

theorem sqrt_exists (c : S1687P.rootSet F) :
    ∃ r : F, r ^ 2 = (c : F) := by
  have hs := sqrt_splits c
  have hmonic : ((X ^ 2 - C (c : F)) : F[X]).Monic :=
    monic_X_pow_sub_C (c : F) (by norm_num : (2:ℕ) ≠ 0)
  have hdeg : ((X ^ 2 - C (c : F)) : F[X]).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, natDegree_X_pow_sub_C]
    norm_num
  let r := Polynomial.rootOfSplits hs hdeg
  have hr : Polynomial.eval r (X ^ 2 - C (c : F)) = 0 :=
    Polynomial.eval_rootOfSplits hs hdeg
  refine ⟨r, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  linear_combination hr

end ProbeSqrt2
