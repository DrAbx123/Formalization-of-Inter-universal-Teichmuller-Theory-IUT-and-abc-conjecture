import tmp.sheaf.xif.paper.AG03DivisorsSectionsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# AG03b: functoriality and basic lemmas for O(D) (AG infrastructure)

* restriction along an open inclusion: O(D)(V) is contained in O(D)(U) for U <= V
  (same field elements, restricted membership);
* coefficient monotonicity: D <= E pointwise gives O(D)(U) <= O(E)(U);
* unit sections of Γ(X,U) lie in O(0)(U).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG03bSectionsBasicActual

open AlgebraicGeometry Order TopologicalSpace WithZero
open LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual
open LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual
open LeanFormal.IUT.XiFPaper.AG03DivisorsSectionsActual

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (hDVR : CodimOneDVR X)

/-- Restriction along an open inclusion: O(D)(V) ⊆ O(D)(U) for U <= V. -/
theorem divisorSections_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hUV : U ≤ V) (D : WeilDivisor X) {f : X.functionField}
    (hf : f ∈ divisorSections (X := X) hDVR V D) :
    f ∈ divisorSections (X := X) hDVR U D := by
  rcases hf with h0 | hf
  · exact Or.inl h0
  · refine Or.inr ?_
    intro x hx hx1
    exact hf x (hUV hx) hx1

/-- Coefficient monotonicity: D <= E pointwise gives O(D)(U) ⊆ O(E)(U). -/
theorem divisorSections_mono_coeff (U : X.Opens) [Nonempty U]
    {D E : WeilDivisor X}
    (hDE : ∀ z : AGCodimOnePoint X, D z ≤ E z) {f : X.functionField}
    (hf : f ∈ divisorSections (X := X) hDVR U D) :
    f ∈ divisorSections (X := X) hDVR U E := by
  rcases hf with h0 | hf
  · exact Or.inl h0
  · refine Or.inr ?_
    intro x hx hx1
    have hD := hf x hx hx1
    have hcoeff : weilDivisorCoeffAt D x ≤ weilDivisorCoeffAt E x := by
      simp [weilDivisorCoeffAt, hx1]
      exact hDE ⟨x, hx1⟩
    linarith

/-- Unit sections of Γ(X,U) lie in O(0)(U). -/
theorem unit_germ_mem_divisorSections_zero (U : X.Opens) [Nonempty U]
    {u : Γ(X, U)} (hu : IsUnit u) :
    X.germToFunctionField U u ∈
      divisorSections (X := X) hDVR U (0 : WeilDivisor X) := by
  refine Or.inr ?_
  intro x hx hx1
  have hord : X.ord (X.germToFunctionField U u) x = 0 :=
    Scheme.ord_of_isUnit hu hx
  rw [hord]
  simp [weilDivisorCoeffAt, hx1]

end LeanFormal.IUT.XiFPaper.AG03bSectionsBasicActual

end
