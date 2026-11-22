import tmp.sheaf.xif.paper.Mzk1Cor55OrderLawActual

/-!
# Mzk1Cor55DaggerOrder2Actual — further order laws for L-dagger = WithBot Z
(new theorems from existing Cor55 assets). No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor55DaggerOrder2Actual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

/-- Derived: the formal symbol is below all L-dagger elements. -/
theorem cor55_bot_le_all (x : Cor55Ldagger) : (⊥ : Cor55Ldagger) ≤ x :=
  bot_le

/-- Derived: every L-dagger element is either the formal symbol or an embedded element. -/
theorem cor55_eq_bot_or_some (x : Cor55Ldagger) :
    x = ⊥ ∨ ∃ a : Cor55L, x = (WithBot.some a : Cor55Ldagger) := by
  cases x with
  | bot => exact Or.inl rfl
  | coe a => exact Or.inr ⟨a, rfl⟩

/-- Derived: a bottom element in L-dagger is unique. -/
theorem cor55_bot_unique (x : Cor55Ldagger) (h : ∀ y : Cor55Ldagger, x ≤ y) :
    x = ⊥ := by
  have hx := h ⊥
  exact le_bot_iff.mp hx

/-- Derived: the embedded L is cofinal above the formal symbol. -/
theorem cor55_embed_cofinal (x : Cor55Ldagger) :
    x = ⊥ ∨ ∃ a : Cor55L, x ≤ (WithBot.some a : Cor55Ldagger) := by
  rcases cor55_eq_bot_or_some x with h | ⟨a, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, le_refl _⟩

#check cor55_bot_le_all
#check cor55_eq_bot_or_some
#check cor55_bot_unique
#check cor55_embed_cofinal

end LeanFormal.IUT.XiFPaper.Mzk1Cor55DaggerOrder2Actual
end
