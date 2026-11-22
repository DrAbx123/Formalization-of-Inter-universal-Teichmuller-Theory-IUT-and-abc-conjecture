import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Stage-4 host: BD-class comparison tool (GenEll Definition 1.2, (ii))

TEXT: papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt,
Definition 1.2, (ii) (p.220-230): for F subset of X(Q) and alpha, beta : F -> R,
alpha <~_F beta iff beta(x) - alpha(x) <= C for all x in F (some constant C).
[GenEll] Remark cited in IUT IV Remark 2.3.1, (ii) reverses the printed typo:
the convention used here is alpha <~ beta iff beta - alpha bounded above.

This is the CLASS A tool: all BD-class chains in the (c) estimate (e.g. IUT IV
Cor 2.2 (i) 1/6 log q ~ ht_inf ~ ht_omega, and Cor 2.3 reduction) are formal
compositions of these relations.

LABEL: generic reusable tool (class A). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual

/-- BD-class upper relation: alpha <= beta up to a bounded constant on F
(GenEll Def 1.2 (ii), corrected orientation). -/
def IsBDLe {α : Type*} (f g : α → ℝ) (F : Set α) : Prop :=
  ∃ C : ℝ, ∀ x ∈ F, g x - f x ≤ C

/-- BD-class upper relations are reflexive. -/
theorem isBDLe_refl {α : Type*} (f : α → ℝ) (F : Set α) :
    IsBDLe f f F := by
  refine ⟨0, ?_⟩
  intro x hx
  simp

/-- BD-class upper relations compose (the chain rule for bounded discrepancy). -/
theorem isBDLe_trans {α : Type*} {f g h : α → ℝ} {F : Set α}
    (hfg : IsBDLe f g F) (hgh : IsBDLe g h F) :
    IsBDLe f h F := by
  obtain ⟨C1, h1⟩ := hfg
  obtain ⟨C2, h2⟩ := hgh
  refine ⟨C1 + C2, ?_⟩
  intro x hx
  have hx1 := h1 x hx
  have hx2 := h2 x hx
  linarith

/-- Adding a bounded function on the right is absorbed. -/
theorem isBDLe_add_right {α : Type*} {f g h : α → ℝ} {F : Set α}
    (hfg : IsBDLe f g F) (hh : IsBDLe (fun _ => 0) h F) :
    IsBDLe f (fun x => g x + h x) F := by
  obtain ⟨C1, h1⟩ := hfg
  obtain ⟨C2, h2⟩ := hh
  refine ⟨C1 + C2, ?_⟩
  intro x hx
  have hx1 := h1 x hx
  have hx2 := h2 x hx
  simp only [sub_zero] at hx2
  linarith

/-- Scaling by a nonnegative constant preserves the relation. -/
theorem isBDLe_const_mul_nonneg {α : Type*} {f g : α → ℝ} {F : Set α}
    {c : ℝ} (hc : 0 ≤ c) (hfg : IsBDLe f g F) :
    IsBDLe (fun x => c * f x) (fun x => c * g x) F := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨c * C, ?_⟩
  intro x hx
  have hx' := hC x hx
  nlinarith

/-- BD equivalence: both directions. -/
def IsBDEq {α : Type*} (f g : α → ℝ) (F : Set α) : Prop :=
  IsBDLe f g F ∧ IsBDLe g f F

/-- BD equivalence is symmetric. -/
theorem isBDEq_symm {α : Type*} {f g : α → ℝ} {F : Set α}
    (h : IsBDEq f g F) : IsBDEq g f F :=
  ⟨h.2, h.1⟩

/-- BD equivalence composes. -/
theorem isBDEq_trans {α : Type*} {f g h : α → ℝ} {F : Set α}
    (hfg : IsBDEq f g F) (hgh : IsBDEq g h F) : IsBDEq f h F :=
  ⟨isBDLe_trans hfg.1 hgh.1, isBDLe_trans hgh.2 hfg.2⟩

#check IsBDLe
#check isBDLe_trans
#check isBDLe_add_right
#check isBDLe_const_mul_nonneg
#check IsBDEq
#check isBDEq_trans

end LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual