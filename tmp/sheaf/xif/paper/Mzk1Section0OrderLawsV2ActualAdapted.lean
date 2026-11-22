import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
  Mainline: Section-0 ordered-set laws (adjacent pairs, orderwise connectedness).
  Real proofs over the constructed objects; no closure claims.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0OrderLawsV2ActualAdapted

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

theorem adjacent_iff (e e' : ℤ) : Adjacent e e' ↔ e' = e + 1 :=
  Iff.rfl

theorem adjacent_succ (e : ℤ) : Adjacent e (e + 1) :=
  rfl

theorem adjacent_irrefl (e : ℤ) : ¬ Adjacent e e := by
  intro h
  dsimp [Adjacent] at h
  omega

theorem adjacent_injective {e e' : ℤ} (h : Adjacent e = Adjacent e') : e = e' := by
  have hh : e + 1 = e' + 1 := by
    have hh' := congrFun h (e + 1)
    simpa [Adjacent] using hh'
  omega

theorem orderwiseConnected_empty (E : Type u) [Preorder E] :
    OrderwiseConnected (∅ : Set E) := by
  intro c hleft hright
  obtain ⟨a, ha, _⟩ := hleft
  exact absurd ha (by simp)

theorem orderwiseConnected_univ (E : Type u) [Preorder E] :
    OrderwiseConnected (Set.univ : Set E) :=
  fun c _ _ => Set.mem_univ c

theorem countablyOrdered_iff (E : Type u) [Preorder E] :
    CountablyOrdered E ↔
      ∃ E' : Set ℤ, OrderwiseConnected E' ∧ Nonempty (E ≃o ↥E') :=
  Iff.rfl

/-- Integer intervals are orderwise connected. -/
theorem orderwiseConnected_Icc (a b : ℤ) :
    OrderwiseConnected (Set.Icc a b) := by
  intro c hleft hright
  obtain ⟨x, hx, hxc⟩ := hleft
  obtain ⟨y, hy, hcy⟩ := hright
  exact ⟨le_trans hx.1 (le_of_lt hxc), le_trans (le_of_lt hcy) hy.2⟩
end LeanFormal.IUT.XiFPaper.Mzk1Section0OrderLawsV2ActualAdapted