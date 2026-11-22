import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ABCBridge.LocalRingAlgebraAut

noncomputable section

universe u

variable {S : Type u} [CommRing S] [IsLocalRing S]

/-- An idempotent in a local commutative ring is `0` or `1`. -/
theorem local_idempotent_eq_zero_or_one {e : S} (he : e * e = e) : e = 0 ∨ e = 1 := by
  have hsum : e + (1 - e) = 1 := by ring
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := e) (b := 1 - e)
    (by rw [hsum]; exact isUnit_one) with hu | hu
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    exact Or.inr (by
      calc e = e * (e * v) := by rw [hv, mul_one]
        _ = (e * e) * v := by ring
        _ = e * v := by rw [he]
        _ = 1 := hv)
  · have h1e : (1 - e) * (1 - e) = 1 - e := by
      calc (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
        _ = 1 - e - e + e := by rw [he]
        _ = 1 - e := by ring
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    left
    have h1 : (1 - e) = 1 := by
      calc (1 - e) = (1 - e) * ((1 - e) * v) := by rw [hv, mul_one]
        _ = ((1 - e) * (1 - e)) * v := by ring
        _ = (1 - e) * v := by rw [h1e]
        _ = 1 := hv
    exact (sub_eq_self).mp h1

variable {n : ℕ}

/-- The standard idempotent `e_i` of `Fin n → S`. -/
def standardIdempotent (i : Fin n) : Fin n → S :=
  fun j => if j = i then 1 else 0

@[simp] theorem standardIdempotent_self (i : Fin n) :
    standardIdempotent (S := S) i i = 1 := by
  simp [standardIdempotent]

@[simp] theorem standardIdempotent_of_ne {i j : Fin n} (h : j ≠ i) :
    standardIdempotent (S := S) i j = 0 := by
  simp [standardIdempotent, h]

theorem standardIdempotent_mul (i : Fin n) :
    standardIdempotent (S := S) i * standardIdempotent (S := S) i =
      standardIdempotent (S := S) i := by
  funext j
  by_cases hj : j = i <;> simp [standardIdempotent, hj]

theorem standardIdempotent_ne_zero (i : Fin n) :
    standardIdempotent (S := S) i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [standardIdempotent] at this

variable {σ : (Fin n → S) ≃ₐ[S] (Fin n → S)}

theorem coord_idempotent (i : Fin n) (j : Fin n) :
    (σ (standardIdempotent (S := S) i) j) * (σ (standardIdempotent (S := S) i) j) =
      σ (standardIdempotent (S := S) i) j := by
  have h := congrFun (map_mul σ (standardIdempotent i) (standardIdempotent i)) j
  simpa [standardIdempotent_mul] using h.symm

theorem image_standardIdempotent_apply_eq_zero_or_one (i : Fin n) (j : Fin n) :
    σ (standardIdempotent (S := S) i) j = 0 ∨
      σ (standardIdempotent (S := S) i) j = 1 :=
  local_idempotent_eq_zero_or_one (coord_idempotent (σ := σ) i j)

theorem standardIdempotent_injective : Function.Injective (standardIdempotent (S := S) (n := n)) := by
  intro i j h
  have hi := congrFun h i
  simp only [standardIdempotent, if_pos rfl] at hi
  by_contra hij
  have hji : i ≠ j := fun h' => hij h'
  simp [standardIdempotent, hji] at hi

theorem idempotent_mul_standardIdempotent (i : Fin n) {h : Fin n → S}
    (hh : h * h = h) (hhi : h * standardIdempotent (S := S) i = h) :
    h = 0 ∨ h = standardIdempotent (S := S) i := by
  have hoff : ∀ k, k ≠ i → h k = 0 := by
    intro k hk
    have hcoord := congrFun hhi k
    simpa [Pi.mul_apply, standardIdempotent, hk] using hcoord.symm
  have hii : h i = 0 ∨ h i = 1 := by
    have hcoord := congrFun hh i
    have hidem : h i * h i = h i := by simpa [Pi.mul_apply] using hcoord
    exact local_idempotent_eq_zero_or_one hidem
  rcases hii with hi0 | hi1
  · left
    funext k
    by_cases hk : k = i
    · subst hk; exact hi0
    · exact hoff k hk
  · right
    funext k
    by_cases hk : k = i
    · subst hk; simpa [standardIdempotent] using hi1
    · simpa [standardIdempotent, hk] using hoff k hk

theorem image_standardIdempotent_minimal (i : Fin n) :
    ∀ g : Fin n → S, g * g = g →
      g * σ (standardIdempotent (S := S) i) = g →
      g = 0 ∨ g = σ (standardIdempotent (S := S) i) := by
  intro g hg hgf
  let h : Fin n → S := σ.symm g
  have hh : h * h = h := by
    apply σ.injective
    change σ (σ.symm g * σ.symm g) = σ (σ.symm g)
    rw [map_mul, σ.apply_symm_apply]
    simpa using hg
  have hhi : h * standardIdempotent (S := S) i = h := by
    apply σ.injective
    change σ (σ.symm g * standardIdempotent (S := S) i) = σ (σ.symm g)
    rw [map_mul, σ.apply_symm_apply]
    simpa using hgf
  rcases idempotent_mul_standardIdempotent (S := S) i hh hhi with h0 | hi
  · left
    simpa [h] using congrArg σ h0
  · right
    simpa [h] using congrArg σ hi

theorem image_standardIdempotent_support_nonempty (i : Fin n) :
    ∃ j : Fin n, σ (standardIdempotent (S := S) i) j = 1 := by
  have hne : σ (standardIdempotent (S := S) i) ≠ 0 := by
    intro h
    apply standardIdempotent_ne_zero (S := S) i
    apply σ.injective
    simpa using h
  have hex : ∃ j, σ (standardIdempotent (S := S) i) j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hex
  rcases image_standardIdempotent_apply_eq_zero_or_one (σ := σ) i j with h0 | h1
  · exact absurd h0 hj
  · exact ⟨j, h1⟩

theorem image_standardIdempotent_support_unique (i : Fin n) :
    ∀ j k : Fin n, σ (standardIdempotent (S := S) i) j = 1 →
      σ (standardIdempotent (S := S) i) k = 1 → j = k := by
  intro j k hj hk
  by_contra hjk
  have hmin := image_standardIdempotent_minimal (σ := σ) i
  let g : Fin n → S := standardIdempotent (S := S) j
  have hg : g * g = g := standardIdempotent_mul (S := S) j
  have hgf : g * σ (standardIdempotent (S := S) i) = g := by
    funext l
    by_cases hl : l = j
    · subst hl
      simp [g, standardIdempotent, hj]
    · simp [g, standardIdempotent, hl]
  rcases hmin g hg hgf with h0 | hf
  · exact standardIdempotent_ne_zero (S := S) j h0
  · have hcoord := congrFun hf k
    have hkj : k ≠ j := fun h' => hjk h'.symm
    simp [g, standardIdempotent, hkj, hk] at hcoord

theorem exists_image_standardIdempotent_unique (i : Fin n) :
    ∃! j : Fin n, σ (standardIdempotent (S := S) i) =
      standardIdempotent (S := S) j := by
  obtain ⟨j, hj⟩ := image_standardIdempotent_support_nonempty (σ := σ) i
  have hcoords : σ (standardIdempotent (S := S) i) = standardIdempotent (S := S) j := by
    funext k
    by_cases hk : k = j
    · subst hk; simpa [standardIdempotent] using hj
    · have hkj : j ≠ k := fun h' => hk h'.symm
      have h0 := image_standardIdempotent_apply_eq_zero_or_one (σ := σ) i k
      rcases h0 with h0 | h1
      · simpa [standardIdempotent, hk] using h0
      · exact absurd (image_standardIdempotent_support_unique (σ := σ) i j k hj h1) hkj
  refine ⟨j, hcoords, ?_⟩
  intro k hk
  exact standardIdempotent_injective (S := S) (hk.symm.trans hcoords)

theorem exists_coordinate_permutation :
    ∃ π : Fin n ≃ Fin n, ∀ i : Fin n,
      σ (standardIdempotent (S := S) i) = standardIdempotent (S := S) (π i) := by
  classical
  choose π hπ using fun i => (exists_image_standardIdempotent_unique (σ := σ) i).exists
  have hinj : Function.Injective π := by
    intro i j hij
    have hi := hπ i
    have hj := hπ j
    rw [hij] at hi
    exact standardIdempotent_injective (S := S) (σ.injective (hi.trans hj.symm))
  have hsurj : Function.Surjective π := by
    intro j
    have hpre := exists_image_standardIdempotent_unique (σ := σ.symm) j
    obtain ⟨i, hi, _⟩ := hpre
    refine ⟨i, ?_⟩
    have hmap : σ (standardIdempotent (S := S) i) = standardIdempotent (S := S) j := by
      have := congrArg σ hi
      simpa using this.symm
    have hπi := hπ i
    rw [hmap] at hπi
    exact standardIdempotent_injective (S := S) hπi.symm
  exact ⟨Equiv.ofBijective π ⟨hinj, hsurj⟩, fun i => hπ i⟩

end

end ABCBridge.LocalRingAlgebraAut
