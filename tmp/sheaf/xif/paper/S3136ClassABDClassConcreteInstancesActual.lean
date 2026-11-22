import tmp.sheaf.xif.paper.S3136BDClassChainToolActual

/-! # Stage-4 host: concrete class-A BD-class instances

Source anchors: [GenEll] Definition 1.2, (ii) (BD-class relations) with the
orientation corrected as in IUT IV Remark 2.3.1, (ii); IUT IV Cor 2.2, (i) chain.

CONSUMER: mainline/lattice BD-class chains. Concrete instances of IsBDLe/IsBDEq:
constants, boundedness from a pointwise inequality, sums and nonnegative scaling,
and the composition pattern used in the Cor 2.2 (i) display. These are the
elementary (class A) facts the IV statement skeleton needs.

LABEL: class A tools. Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136ClassABDClassConcreteInstancesActual

open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual

variable {α : Type*} (F : Set α)

/-- A pointwise inequality gives the BD-class upper relation in the opposite direction. -/
theorem isBDLe_of_pointwise {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    IsBDLe g f F := by
  refine ⟨0, ?_⟩
  intro x hx
  exact sub_nonpos.mpr (h x)

/-- A pointwise inequality with bounded discrepancy constant. -/
theorem isBDLe_of_le_add_const {f g : α → ℝ} {C : ℝ} (h : ∀ x, g x - f x ≤ C) :
    IsBDLe f g F :=
  ⟨C, fun x _ => h x⟩

/-- Two BD-class relations add. -/
theorem isBDLe_add {f1 g1 f2 g2 : α → ℝ}
    (h1 : IsBDLe f1 g1 F) (h2 : IsBDLe f2 g2 F) :
    IsBDLe (fun x => f1 x + f2 x) (fun x => g1 x + g2 x) F := by
  obtain ⟨C1, hC1⟩ := h1
  obtain ⟨C2, hC2⟩ := h2
  refine ⟨C1 + C2, ?_⟩
  intro x hx
  have hx1 := hC1 x hx
  have hx2 := hC2 x hx
  linarith

/-- A bounded difference is a BD equivalence. -/
theorem isBDEq_of_bounded_abs {f g : α → ℝ} {C : ℝ}
    (h : ∀ x ∈ F, |g x - f x| ≤ C) :
    IsBDEq f g F := by
  refine ⟨⟨C, ?_⟩, ⟨C, ?_⟩⟩
  · intro x hx
    have hx' := h x hx
    linarith [abs_le.mp hx']
  · intro x hx
    have hx' := h x hx
    linarith [abs_le.mp hx']

#check isBDLe_of_pointwise
#check isBDLe_of_le_add_const
#check isBDLe_add
#check isBDEq_of_bounded_abs

end LeanFormal.IUT.XiFPaper.S3136ClassABDClassConcreteInstancesActual