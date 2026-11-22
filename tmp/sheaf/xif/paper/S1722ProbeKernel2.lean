import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeKernel2

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

abbrev F := S1720Field
abbrev G := F ≃ₐ[ℚ] F

variable (r : S1687P.rootSet F → F)
variable (iroot : F)

axiom root_decomp : ∀ {x : F}, x ∈ S1720H.rootSet F →
    (∃ c : S1687P.rootSet F, x = r c ∨ x = - r c) ∨ x = iroot ∨ x = -iroot

theorem eq_of_agrees_on_generators (σ τ : G)
    (h : ∀ c : S1687P.rootSet F, σ (r c) = τ (r c))
    (hi : σ iroot = τ iroot) : σ = τ := by
  have hroot : ∀ x ∈ S1720H.rootSet F, σ x = τ x := by
    intro x hx
    rcases root_decomp r iroot hx with ⟨c, hx' | hx'⟩ | hx' | hx'
    · rw [hx', h c]
    · rw [hx']
      simp [h c]
    · rw [hx', hi]
    · rw [hx']
      simp [hi]
  have hgen : Algebra.adjoin ℚ (S1720H.rootSet F) = ⊤ :=
    Polynomial.SplittingField.adjoin_rootSet (f := S1720H)
  have heq : σ.toAlgHom = τ.toAlgHom :=
    AlgHom.ext_of_adjoin_eq_top hgen (fun x hx => hroot x hx)
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun heq x

end ProbeKernel2
