import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Factors

open Equiv

namespace Probe2217

theorem cycleType_eq_fiber_sizes
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm α) (p : α → β) (d : β → ℕ)
    (hinv : ∀ x, p (σ x) = p x)
    (hcard : ∀ b, Fintype.card {x // p x = b} = d b)
    (htrans : ∀ b (x y : α), p x = b → p y = b → σ.SameCycle x y) :
    σ.cycleType = (Finset.univ.filter (fun b => 2 ≤ d b)).val.map d := by
  classical
  let T : Finset β := Finset.univ.filter (fun b => 2 ≤ d b)
  let fib : β → Set α := fun b => {x | p x = b}
  have hfibInv : ∀ b x, fib b (σ x) ↔ fib b x := by
    intro b x
    change p (σ x) = b ↔ p x = b
    rw [hinv x]
  let cyc : β → Equiv.Perm α := fun b => (σ.subtypePerm (hfibInv b)).ofSubtype
  have hcyc_apply_mem : ∀ b (x : α), p x = b → cyc b x = σ x := by
    intro b x hx
    change (Equiv.Perm.ofSubtype (σ.subtypePerm (hfibInv b))) x = σ x
    rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fib b) (ha := hx)]
    rw [Equiv.Perm.subtypePerm_apply]
  have hcyc_apply_not_mem : ∀ b (x : α), p x ≠ b → cyc b x = x := by
    intro b x hx
    change (Equiv.Perm.ofSubtype (σ.subtypePerm (hfibInv b))) x = x
    exact Equiv.Perm.ofSubtype_apply_of_not_mem (p := fib b) (f := σ.subtypePerm (hfibInv b)) hx
  have hon : ∀ b, σ.IsCycleOn (fib b) := by
    intro b
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact fun x hx => (hfibInv b x).mpr hx
    · exact fun x hx y hy hxy => σ.injective hxy
    · intro y hy
      refine ⟨σ⁻¹ y, ?_, σ.apply_symm_apply y⟩
      apply (hfibInv b (σ⁻¹ y)).mp
      have h2 : σ (σ⁻¹ y) = y := σ.apply_symm_apply y
      rw [h2]
      exact hy
    · intro y hy z hz
      exact htrans b y z hy hz
  have hfib_nontriv : ∀ b, 2 ≤ d b → (fib b).Nontrivial := by
    intro b hb
    have hc : 1 < Fintype.card {x // p x = b} := by rw [hcard]; omega
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hc
    exact ⟨x.1, by simp [fib], y.1, by simp [fib], fun h => hxy (Subtype.ext h)⟩
  have hcyc_cycle : ∀ b, 2 ≤ d b → (cyc b).IsCycle := by
    intro b hb
    have hsub : (σ.subtypePerm (hfibInv b)).IsCycle :=
      (hon b).isCycle_subtypePerm (hfib_nontriv b hb)
    rw [← Equiv.Perm.card_cycleType_eq_one, Equiv.Perm.cycleType_ofSubtype, hsub.cycleType]
    simp
  have hcyc_support : ∀ b, 2 ≤ d b → (cyc b).support = (fib b).toFinset := by
    intro b hb
    ext x
    rw [Equiv.Perm.mem_support]
    constructor
    · intro hx
      rw [Set.mem_toFinset]
      by_contra hxb
      exact hx (hcyc_apply_not_mem b x hxb)
    · intro hx
      rw [Set.mem_toFinset] at hx
      rw [hcyc_apply_mem b x hx]
      exact (hon b).apply_ne (hfib_nontriv b hb) hx
  have hcyc_support_card : ∀ b, 2 ≤ d b → (cyc b).support.card = d b := by
    intro b hb
    rw [hcyc_support b hb, Set.toFinset_card]
    change Fintype.card {x // p x = b} = d b
    exact hcard b
  have hdisjoint : (T : Set β).Pairwise
      (fun b b' => Equiv.Perm.Disjoint (cyc b) (cyc b')) := by
    intro b hb b' hb' hne
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    rw [hcyc_support b (Finset.mem_filter.mp hb).2] at hx
    rw [hcyc_support b' (Finset.mem_filter.mp hb').2] at hx'
    rw [Set.mem_toFinset] at hx hx'
    exact hne (hx.symm.trans hx')
  have hcomm : (T : Set β).Pairwise
      (fun b b' => Commute (cyc b) (cyc b')) :=
    hdisjoint.imp (fun _ _ h => h.commute)
  have hprod_aux : ∀ (s : Finset β)
      (hs : (s : Set β).Pairwise (fun b b' => Commute (cyc b) (cyc b'))),
      ∀ x : α, s.noncommProd cyc hs x = if p x ∈ s then σ x else x := by
    intro s hs x
    induction s using Finset.induction_on generalizing x with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
        simp only [Equiv.Perm.mul_apply]
        rw [ih]
        by_cases hpa : p x = a
        · have hnotmem : p x ∉ s := by rw [hpa]; exact ha
          rw [if_neg hnotmem, hcyc_apply_mem a x hpa]
          simp [hpa]
        · by_cases hxs : p x ∈ s
          · rw [if_pos hxs, hcyc_apply_not_mem a (σ x) (by rw [hinv x]; exact hpa)]
            rw [if_pos (by simp [hpa, hxs])]
          · rw [if_neg hxs, hcyc_apply_not_mem a x hpa]
            rw [if_neg (by simp [hpa, hxs])]
  have hprod : T.noncommProd cyc hcomm = σ := by
    ext x
    rw [hprod_aux T hcomm x]
    by_cases hxT : p x ∈ T
    · rw [if_pos hxT]
    · rw [if_neg hxT]
      have hlt : d (p x) < 2 := by
        by_contra h
        exact hxT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      have hsub : Subsingleton {y // p y = p x} := by
        rw [← Fintype.card_le_one_iff_subsingleton, hcard]
        omega
      have hmem : (⟨x, rfl⟩ : {y // p y = p x}) = ⟨σ x, hinv x⟩ := Subsingleton.elim _ _
      have hval : σ x = x := by
        have := congrArg Subtype.val hmem
        simpa using this.symm
      exact hval.symm
  calc σ.cycleType = (T.noncommProd cyc hcomm).cycleType := by rw [hprod]
    _ = T.sum (fun b => (cyc b).cycleType) :=
        Equiv.Perm.Disjoint.cycleType_noncommProd hdisjoint hcomm
    _ = T.sum (fun b => ({d b} : Multiset ℕ)) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [(hcyc_cycle b (Finset.mem_filter.mp hb).2).cycleType,
          hcyc_support_card b (Finset.mem_filter.mp hb).2]
    _ = T.val.map d := by
        induction T using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, ih, Finset.insert_val_of_notMem ha, Multiset.map_cons]
            simp

end Probe2217
