import tmp.sheaf.xif.paper.S3136BDClassChainToolActual
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.GenEll09BDToolsActual

open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual

/-- BD upper relations are compatible with sums: if f1 <=~ f2 and g1 <=~ g2 then
f1+g1 <=~ f2+g2 (bounded discrepancy adds). -/
theorem isBDLe_add {α : Type*} {F : Set α} {f1 f2 g1 g2 : α → ℝ}
    (hf : IsBDLe f1 f2 F) (hg : IsBDLe g1 g2 F) :
    IsBDLe (fun x => f1 x + g1 x) (fun x => f2 x + g2 x) F := by
  obtain ⟨C1, h1⟩ := hf
  obtain ⟨C2, h2⟩ := hg
  refine ⟨C1 + C2, ?_⟩
  intro x hx
  have hx1 := h1 x hx
  have hx2 := h2 x hx
  linarith

/-- Pointwise domination gives a BD upper relation. -/
theorem isBDLe_of_le {α : Type*} {F : Set α} {f g : α → ℝ}
    (h : ∀ x ∈ F, g x ≤ f x) : IsBDLe f g F := by
  refine ⟨0, ?_⟩
  intro x hx
  linarith [h x hx]

/-- Dropping an additive constant on the left is absorbed (BD-class ignores bounded
terms). -/
theorem isBDLe_add_const_left {α : Type*} {F : Set α} {f g : α → ℝ} (c : ℝ) :
    IsBDLe (fun x => f x + c) g F ↔ IsBDLe f g F := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + c, ?_⟩
    intro x hx
    have := hC x hx
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C - c, ?_⟩
    intro x hx
    have := hC x hx
    linarith

/-- Negating and swapping: f <=~ g iff -g <=~ -f (orientation mirror). -/
theorem isBDLe_neg_swap {α : Type*} {F : Set α} {f g : α → ℝ}
    (h : IsBDLe f g F) : IsBDLe (fun x => -g x) (fun x => -f x) F := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  intro x hx
  have := hC x hx
  linarith

#check isBDLe_add
#check isBDLe_of_le
#check isBDLe_add_const_left
#check isBDLe_neg_swap
end LeanFormal.IUT.XiFPaper.GenEll09BDToolsActual
end
