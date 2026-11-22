import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Group.Submonoid.Basic

/-!
# S807: no-go probe for higher-order cancellation tools (Task W)

Task W asks whether oscillatory-integral / Gauss-sum / decoupling / polynomial-method /
entropy tools can produce the paper inequality -|log Theta| >= -|log q| or the paper
least lambda-O hull (IUT III, Remark 3.9.5, (i); Corollary 3.12).

This file isolates the two formal facts that decide the question independently of any
particular estimate:

* norm_add_eq_left_of_norm_lt, norm_sum_eq_of_unique_max, norm_thetaSum_Icc_eq:
  in a nonarchimedean field the norm of a finite sum with a unique strict maximum is
  exactly the maximum norm.  For the theta family r ^ (j ^ 2) with norm r < 1 the sum
  over the labels is dominated by j = 1, so there is no p-adic cancellation at all.
* sum_mem_ball_not_image_subset: a ball of radius norm t contains the sum 1 + (-1) but
  not the image set {1, -1}.  Hence membership or bounds for a sum cannot imply
  containment of the possible-image set, which is what the paper hull is computed from.
* sum_mem_iInf, mem_iInf_of_mem_closure: additive combinations of possible images stay
  inside every candidate region, hence inside the least hull; sums cannot force a
  smaller hull either.

No project imports, no paper-specific object, no axiom, no sorry.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S807CancellationNoGoActual

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Strict ultrametric domination: if norm y < norm x then norm (x + y) = norm x. -/
theorem norm_add_eq_left_of_norm_lt {x y : K} (h : ‖y‖ < ‖x‖) :
    ‖x + y‖ = ‖x‖ := by
  have hna : IsNonarchimedean (fun z : K => ‖z‖) :=
    IsUltrametricDist.isNonarchimedean_norm
  have hne : ‖x‖ ≠ ‖y‖ := ne_of_gt h
  have hmax := IsNonarchimedean.add_eq_max_of_ne'
    (fun z : K => ‖z‖) hna (fun a => (norm_neg (a := a)).symm) hne
  rw [hmax, max_eq_left (le_of_lt h)]

/-- A finite sum with a unique strict maximum norm has norm exactly that maximum.
This is the formal form of no p-adic cancellation: the sum is dominated by its
largest term, so no phase cancellation can lower its valuation. -/
theorem norm_sum_eq_of_unique_max {ι : Type*} (s : Finset ι) (f : ι → K) (i0 : ι)
    (hi0 : i0 ∈ s) (hf0 : f i0 ≠ 0)
    (h : ∀ i ∈ s, i ≠ i0 → ‖f i‖ < ‖f i0‖) :
    ‖∑ i ∈ s, f i‖ = ‖f i0‖ := by
  classical
  have hlt : ‖∑ i ∈ s.erase i0, f i‖ < ‖f i0‖ := by
    rcases (s.erase i0).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]
      exact norm_pos_iff.mpr hf0
    · refine lt_of_le_of_lt (b := (s.erase i0).sup' hne (fun i => ‖f i‖)) ?_ ?_
      · exact IsNonarchimedean.apply_sum_le_sup (f := fun z : K => ‖z‖)
          IsUltrametricDist.isNonarchimedean_norm hne (l := f)
      · rw [Finset.sup'_lt_iff]
        intro i hi
        exact h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  rw [← Finset.insert_erase hi0, Finset.sum_insert (Finset.notMem_erase i0 s)]
  have hne' : ‖f i0‖ ≠ ‖∑ i ∈ s.erase i0, f i‖ := ne_of_gt hlt
  have hmax := IsNonarchimedean.add_eq_max_of_ne'
    (fun z : K => ‖z‖) IsUltrametricDist.isNonarchimedean_norm
    (fun a => (norm_neg (a := a)).symm) hne'
  rw [hmax, max_eq_left (le_of_lt hlt)]

/-- The theta sum sum_{j=1..n} r^(j^2) is dominated by its j = 1 term whenever
norm r < 1 and r is nonzero.  So its p-adic norm is exactly norm r: there is no
cancellation, and the log of the sum is the log of the top theta value. -/
theorem norm_thetaSum_Icc_eq (r : K) (hr : ‖r‖ < 1) (hr0 : r ≠ 0) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖∑ j ∈ Finset.Icc 1 n, r ^ (j ^ 2)‖ = ‖r‖ := by
  have hside : ∀ j ∈ Finset.Icc 1 n, j ≠ 1 → ‖r ^ (j ^ 2)‖ < ‖r ^ (1 ^ 2)‖ := by
    intro j hj hne
    simp only [Finset.mem_Icc] at hj
    have h2 : 2 ≤ j := by omega
    have h4 : 1 < j ^ 2 := by nlinarith
    have hlt : ‖r‖ ^ (j ^ 2) < ‖r‖ :=
      pow_lt_self_of_lt_one₀ (norm_pos_iff.mpr hr0) hr h4
    simpa [norm_pow] using hlt
  have h := norm_sum_eq_of_unique_max (s := Finset.Icc 1 n)
    (f := fun j : ℕ => r ^ (j ^ 2)) (i0 := 1) (by simp [hn]) (by simpa using hr0) hside
  simpa using h

/-- A ball of radius norm t (for norm t < 1) contains the sum 1 + (-1) but not the
image set {1, -1}.  So a containment or bound for a sum gives no containment of the
possible-image set in a strictly smaller region: the inference pattern that a
cancellation-based argument would need is false. -/
theorem sum_mem_ball_not_image_subset (t : K) (ht : ‖t‖ < 1) :
    ∃ R : Set K, (1 + -1 : K) ∈ R ∧ ¬ ({1, -1} : Set K) ⊆ R := by
  refine ⟨{z : K | ‖z‖ ≤ ‖t‖}, ?_, ?_⟩
  · simp
  · intro hsub
    have h1 : (1 : K) ∈ ({1, -1} : Set K) := by simp
    have hle : ‖(1 : K)‖ ≤ ‖t‖ := hsub h1
    rw [norm_one] at hle
    linarith

/-- Intersection of additive subgroups is closed under addition: any additive
combination of possible images lies in every candidate region. -/
theorem sum_mem_iInf {M : Type*} [AddCommGroup M] {ι : Type*}
    (S : ι → AddSubgroup M) {x y : M}
    (hx : x ∈ ⨅ i, S i) (hy : y ∈ ⨅ i, S i) : x + y ∈ ⨅ i, S i := by
  simp only [AddSubgroup.mem_iInf] at hx hy ⊢
  exact fun i => (S i).add_mem (hx i) (hy i)

/-- If every candidate region contains the possible-image set P, then every element
of the additive closure of P lies in the least hull.  Sums of possible images
therefore cannot escape the hull; combined with sum_mem_ball_not_image_subset, sum
control is orthogonal to hull determination. -/
theorem mem_iInf_of_mem_closure {M : Type*} [AddCommGroup M] {ι : Type*}
    (S : ι → AddSubgroup M) {P : Set M} (hP : ∀ i, P ⊆ S i) {x : M}
    (hx : x ∈ AddSubmonoid.closure P) : x ∈ ⨅ i, S i := by
  refine AddSubmonoid.closure_induction (motive := fun y _ => y ∈ ⨅ i, S i)
    ?_ ?_ ?_ hx
  · intro y hy
    exact AddSubgroup.mem_iInf.mpr fun i => hP i hy
  · exact AddSubgroup.mem_iInf.mpr fun i => (S i).zero_mem
  · intro y z hy hz ihy ihz
    exact sum_mem_iInf S ihy ihz

#print axioms norm_add_eq_left_of_norm_lt
#print axioms norm_sum_eq_of_unique_max
#print axioms norm_thetaSum_Icc_eq
#print axioms sum_mem_ball_not_image_subset
#print axioms mem_iInf_of_mem_closure

end LeanFormal.IUT.XiFPaper.S807CancellationNoGoActual

end
