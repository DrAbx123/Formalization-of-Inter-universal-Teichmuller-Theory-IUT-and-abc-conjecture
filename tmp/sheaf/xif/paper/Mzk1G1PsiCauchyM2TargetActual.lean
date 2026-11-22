/- B1-B (kurt): cheap rational-branch case of the analytic target.

If every complex point of the finite branch set is rational and 0 is not in the branch,
the M1 base case (mzk1Lemma24Target_of_zero) directly yields M2AnalyticTarget.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2ProducerActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyM2TargetActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2ProducerActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- aeval of a rational polynomial at a rational point is the rational evaluation. -/
theorem aeval_algebraMap_eval (x : ℚ) (q : Polynomial ℚ) :
    Polynomial.aeval (algebraMap ℚ ℂ x) q = algebraMap ℚ ℂ (Polynomial.eval x q) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_apply]

/-- The cheap rational-branch case of the B1 analytic target. -/
theorem m2AnalyticTarget_of_rationalBranch (Branch : Finset ℂ)
    (hBranch : ∀ z ∈ Branch, ∃ x : ℚ, algebraMap ℚ ℂ x = z)
    (h0 : (0 : ℂ) ∉ Branch) : M2AnalyticTarget Branch := by
  classical
  set f : ℂ → P1Point ℚ := fun z =>
    if h : z ∈ Branch then P1Point.ofFinite (Classical.choose (hBranch z h))
    else P1Point.ofFinite 0 with hf
  set S : Finset (P1Point ℚ) := Branch.image f with hS
  have hfmem : ∀ z (hz : z ∈ Branch), f z =
      P1Point.ofFinite (Classical.choose (hBranch z hz)) := by
    intro z hz
    rw [hf]
    exact dif_pos hz
  have hβ : P1Point.ofFinite (0 : ℚ) ∉ S := by
    intro hmem
    rw [hS] at hmem
    obtain ⟨z, hz, hfz⟩ := Finset.mem_image.mp hmem
    rw [hfmem z hz] at hfz
    have hx0 : Classical.choose (hBranch z hz) = 0 := Option.some.inj hfz
    have hz0 : z = 0 := by
      rw [← Classical.choose_spec (hBranch z hz), hx0]
      simp
    exact h0 (by rwa [hz0] at hz)
  obtain ⟨q, hdeg, hSmap, hβout, -, hcvaway⟩ :=
    mzk1Lemma24Target_of_zero S (P1Point.ofFinite (0 : ℚ)) hβ
  have hmemS : ∀ z (hz : z ∈ Branch), f z ∈ S := by
    intro z hz
    rw [hS]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  refine ⟨q, hdeg, ?_, ?_, ?_⟩
  · intro z hz
    have hx := Classical.choose_spec (hBranch z hz)
    have hsp := hSmap (f z) (hmemS z hz)
    rw [hfmem z hz] at hsp
    have hev : Polynomial.eval (Classical.choose (hBranch z hz)) q = 0 ∨
        Polynomial.eval (Classical.choose (hBranch z hz)) q = 1 :=
      (polyEvalP1_ofFinite_mem_specialSet_iff q _).mp hsp
    have haz := aeval_algebraMap_eval (Classical.choose (hBranch z hz)) q
    rw [hx] at haz
    rw [haz]
    rcases hev with h | h
    · simp [h]
    · simp [h]
  · intro z hz
    by_contra hnot
    exact hcvaway z hnot hz
  · intro hmem
    rw [aeval_zero_eq] at hmem
    have hev : (↑(Polynomial.eval (0 : ℚ) q) : ℂ) = 0 ∨
        (↑(Polynomial.eval (0 : ℚ) q) : ℂ) = 1 := by
      simpa using hmem
    have hev' : Polynomial.eval (0 : ℚ) q = 0 ∨ Polynomial.eval (0 : ℚ) q = 1 := by
      rcases hev with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    have hsp : polyEvalP1 q (P1Point.ofFinite (0 : ℚ)) ∈ specialSet ℚ := by
      rw [show polyEvalP1 q (P1Point.ofFinite (0 : ℚ)) =
        P1Point.ofFinite (Polynomial.eval (0 : ℚ) q) from rfl]
      rcases hev' with h | h
      · rw [h]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_iff.mpr (Or.inl rfl))
      · rw [h]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_iff.mpr (Or.inr rfl))
    exact hβout hsp

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyM2TargetActual
end