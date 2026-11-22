/- Route 7.2 analytic input, first batch: root continuity (Mathlib Approximation.lean) specialized
to PadicAlgCl, plus the Krasner wrapper that upgrades a near root to the same field extension. -/
import tmp.sheaf.xif.paper.Mzk1LpFinitenessActual
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalAnalyticInputActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1LpFinitenessActual

variable {p : Nat} [Fact p.Prime]

/-- Continuity of roots over Q_p, in the form used by route 7.2 step 5: if f and g are monic
of the same degree and their coefficients are epsilon-close, then a root of f has a nearby
root of g in the algebraic closure. -/
theorem exists_root_near_of_coeff_close {n : Nat} (hn : 0 < n)
    {f g : Polynomial ℚ_[p]} (hfm : f.Monic) (hgm : g.Monic)
    (hdeg : g.natDegree = n) (hdegf : f.natDegree = n) {eps : ℝ} (heps : 0 < eps)
    (hcoeff : ∀ i : Nat, ‖g.coeff i - f.coeff i‖ < eps)
    {alpha : PadicAlgCl p} (halpha : f.aeval alpha = 0) :
    ∃ beta : PadicAlgCl p, (g.map (algebraMap ℚ_[p] (PadicAlgCl p))).IsRoot beta ∧
      ‖alpha - beta‖ < ((n + 1 : Nat) * eps) ^ ((n : ℝ)⁻¹) * max ‖alpha‖ 1 := by
  have hdeg' : g.natDegree = f.natDegree := by rw [hdeg, hdegf]
  obtain ⟨beta, hbeta_mem, hbeta_close⟩ :=
    Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (K := ℚ_[p]) (L := PadicAlgCl p)
      heps halpha hfm hgm hdeg' hcoeff (IsAlgClosed.splits _)
  refine ⟨beta, ?_, ?_⟩
  · rw [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact (Polynomial.mem_aroots.mp hbeta_mem).2
  · simpa [hdegf] using hbeta_close

/-- Krasner wrapper: a conjugate near root generating the same extension (route 7.2 step 5). -/
theorem same_extension_of_krasner {x y : PadicAlgCl p}
    (hsep : ∀ x' : PadicAlgCl p, IsConjRoot ℚ_[p] x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖)
    (hconj : IsConjRoot ℚ_[p] x y) :
    IntermediateField.adjoin ℚ_[p] ({x} : Set (PadicAlgCl p)) =
      IntermediateField.adjoin ℚ_[p] ({y} : Set (PadicAlgCl p)) :=
  padic_krasner_same_extension hsep hconj

#print axioms exists_root_near_of_coeff_close
#print axioms same_extension_of_krasner
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalAnalyticInputActual
