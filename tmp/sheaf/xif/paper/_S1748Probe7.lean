import Mathlib.Algebra.Algebra.Pi
import Mathlib.FieldTheory.SeparableClosure

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
variable {I : Type} [Fintype I] {L : I → Type} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]

theorem test_factor (f : (∀ i, L i) →ₐ[K] Ω) :
    ∃ (i₀ : I) (u : L i₀ →ₐ[K] Ω), f = u.comp (Pi.evalAlgHom K L i₀) := by
  classical
  have hsingle : ∀ (i : I) (x : L i),
      (Pi.single i x : ∀ j, L j) = (Pi.single i 1 : ∀ j, L j) * Pi.single i x := by
    intro i x
    ext j
    by_cases h : j = i <;> simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
  have hsum : ∀ a : ∀ j, L j, a = ∑ i, Pi.single i (a i) := by
    intro a
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hidem : ∀ i, f (Pi.single i (1 : L i)) * f (Pi.single i 1) = f (Pi.single i 1) := by
    intro i
    rw [← map_mul]
    congr 1
    ext j
    by_cases h : j = i <;> simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
  have hkey : ∀ i, f (Pi.single i (1 : L i)) = 0 ∨ f (Pi.single i (1 : L i)) = 1 := by
    intro i
    have h := hidem i
    have h2 : f (Pi.single i (1 : L i)) * (f (Pi.single i 1) - 1) = 0 := by
      rw [mul_sub, h, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by rw [sub_eq_zero] at h'; exact h')
  have hsum_one : (∑ i, f (Pi.single i (1 : L i))) = 1 := by
    rw [← map_sum, ← map_one (f := f)]
    congr 1
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hex : ∃ i₀, f (Pi.single i₀ (1 : L i₀)) = 1 := by
    by_contra h
    push Not at h
    have hzero : ∀ i, f (Pi.single i (1 : L i)) = 0 := fun i => (hkey i).resolve_right (h i)
    rw [Finset.sum_congr rfl (fun i _ => hzero i)] at hsum_one
    simp at hsum_one
  obtain ⟨i₀, hi₀⟩ := hex
  have hzero : ∀ i, i ≠ i₀ → f (Pi.single i (1 : L i)) = 0 := by
    intro i hi
    rcases hkey i with h | h
    · exact h
    · exfalso
      have h0 : (Pi.single i (1 : L i) : ∀ j, L j) * Pi.single i₀ (1 : L i₀) = 0 := by
        ext j
        by_cases h1 : j = i <;> simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
      have h3 := congrArg f h0
      rw [map_mul, h, hi₀, one_mul, map_zero] at h3
      exact one_ne_zero h3
  refine ⟨i₀, ?_, ?_⟩
  · refine
      { toFun := fun x => f (Pi.single i₀ x)
        map_one' := ?_
        map_mul' := ?_
        map_zero' := ?_
        map_add' := ?_
        commutes' := ?_ }
    · rw [← map_one (f := f), ← hi₀]
      congr 1
      ext j
      by_cases h : j = i₀ <;> simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
    · intro x y
      rw [← map_mul]
      congr 1
      ext j
      by_cases h : j = i₀ <;> simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
    · rw [← map_zero (f := f)]
      congr 1
      ext j
      by_cases h : j = i₀ <;> simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
    · intro x y
      rw [← map_add]
      congr 1
      ext j
      by_cases h : j = i₀ <;> simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
    · intro k
      rw [← AlgHom.commutes f k]
      congr 1
      ext j
      by_cases h : j = i₀ <;> simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
  · ext a
    simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply]
    conv_lhs => rw [hsum a]
    rw [map_sum, Finset.sum_eq_single i₀]
    · rfl
    · intro i _ hi
      rw [hsingle i (a i), map_mul, hzero i hi, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
