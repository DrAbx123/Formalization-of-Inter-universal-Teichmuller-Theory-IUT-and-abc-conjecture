import Mathlib

/-! # S3131 [GenEll] Def 1.2(ii) BD-class chain tools (class A, provable now) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131BDClassCompositionActual

universe u

/-- BD-class relation `<~`: `f <~ g` if `f <= g + C` for a constant C. -/
def IsBDLe {X : Type u} (f g : X → Real) : Prop :=
  ∃ C : Real, ∀ x : X, f x ≤ g x + C

theorem IsBDLe.refl {X : Type u} (f : X → Real) : IsBDLe f f := by
  refine ⟨0, ?_⟩
  intro x
  simp

/-- Adding the same function to both sides preserves `<~` (same constant). -/
theorem IsBDLe.add_right {X : Type u} {f g h : X → Real}
    (hfg : IsBDLe f g) :
    IsBDLe (fun x => f x + h x) (fun x => g x + h x) := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨C, ?_⟩
  intro x
  have := hC x
  linarith

theorem IsBDLe.trans {X : Type u} {f g h : X → Real}
    (hfg : IsBDLe f g) (hgh : IsBDLe g h) : IsBDLe f h := by
  obtain ⟨C1, h1⟩ := hfg
  obtain ⟨C2, h2⟩ := hgh
  refine ⟨C1 + C2, ?_⟩
  intro x
  have e1 := h1 x
  have e2 := h2 x
  linarith

#check IsBDLe.trans
#check IsBDLe.add_right

end LeanFormal.IUT.XiFPaper.S3131BDClassCompositionActual
end