import tmp.sheaf.xif.paper.AG02bPrincipalDivisorActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# AG03: divisors, O(D), and section modules (AG infrastructure, first layer)

Weil divisor coefficients on codimension-one points (AG02b).  For an open U and a
divisor D we define

  Γ(U, O(D)) := { f : K(X) | f = 0 or (ord_x(f) + D_x >= 0 for every codim-one x in U) }

as a Submodule of the function field over the section ring Γ(X,U) (the algebra
structure of Mathlib's functionField is reused).  The smooth-curve context is the
explicit hypothesis that every codimension-one stalk is a discrete valuation ring
(needed for the additivity of the order of vanishing); it is a hypothesis here,
not an assumption hidden in a structure.

Zero, addition and scalar multiplication closure are proved; functoriality along
open inclusions and coefficient-monotonicity of O(D) are proved in AG03b.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG03DivisorsSectionsActual

open AlgebraicGeometry Order TopologicalSpace WithZero
open LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual
open LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The coefficient of a divisor at an arbitrary point (zero outside codimension one). -/
def weilDivisorCoeffAt (D : WeilDivisor X) (x : X) : ℤ :=
  if h : coheight x = 1 then D ⟨x, h⟩ else 0

/-- Smooth-curve context at codimension-one points: every such stalk is a DVR.
This is an explicit hypothesis (used only for additivity of ord). -/
def CodimOneDVR (X : Scheme.{u}) [IsIntegral X] : Prop :=
  ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x)

variable (hDVR : CodimOneDVR X)
variable (U : X.Opens) [Nonempty U]

/-- Γ(U, O(D)): rational functions whose principal divisor plus D is nonnegative on U;
the zero function is included.  A Γ(X,U)-submodule of K(X). -/
def divisorSections (D : WeilDivisor X) : Submodule Γ(X, U) X.functionField where
  carrier :=
    {f | f = 0 ∨ ∀ x ∈ U, coheight x = 1 → 0 ≤ X.ord f x + weilDivisorCoeffAt D x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    by_cases hfg : f + g = 0
    · exact Or.inl hfg
    refine Or.inr ?_
    intro x hx hx1
    haveI : IsDiscreteValuationRing (X.presheaf.stalk x) := hDVR x hx1
    by_cases hf0 : f = 0
    · have hgf : f + g = g := by rw [hf0]; simp
      rw [hgf]
      rcases hg with h | h
      · exact absurd (by rw [hf0, h]; simp) hfg
      · exact h x hx hx1
    by_cases hg0 : g = 0
    · have hfg' : f + g = f := by rw [hg0]; simp
      rw [hfg']
      rcases hf with h | h
      · exact absurd h hf0
      · exact h x hx hx1
    have hf' : 0 ≤ X.ord f x + weilDivisorCoeffAt D x := by
      rcases hf with h | h
      · exact absurd h hf0
      · exact h x hx hx1
    have hg' : 0 ≤ X.ord g x + weilDivisorCoeffAt D x := by
      rcases hg with h | h
      · exact absurd h hg0
      · exact h x hx hx1
    have hmin := Scheme.ord_add (X := X) (x := x) (f := f) (g := g) hfg
    have hlow : -weilDivisorCoeffAt D x ≤ min (X.ord f x) (X.ord g x) := by
      apply le_min
      · linarith
      · linarith
    linarith
  smul_mem' := by
    intro a f hf
    by_cases ha : a = 0
    · refine Or.inl ?_
      simp [ha]
    by_cases hf0 : f = 0
    · refine Or.inl ?_
      simp [hf0]
    refine Or.inr ?_
    intro x hx hx1
    have hf' : 0 ≤ X.ord f x + weilDivisorCoeffAt D x := by
      rcases hf with h | h
      · exact absurd h hf0
      · exact h x hx hx1
    have hle := Scheme.ord_le_smul (X := X) (x := x) (U := U) hx (a := a) ha f
    linarith

/-- Membership characterization of O(D)(U). -/
theorem mem_divisorSections_iff (D : WeilDivisor X) (f : X.functionField) :
    f ∈ divisorSections (X := X) hDVR U D ↔
      (f = 0 ∨ ∀ x ∈ U, coheight x = 1 →
        0 ≤ X.ord f x + weilDivisorCoeffAt D x) :=
  Iff.rfl

/-- The zero function lies in every O(D)(U). -/
theorem zero_mem_divisorSections (D : WeilDivisor X) :
    (0 : X.functionField) ∈ divisorSections (X := X) hDVR U D :=
  Or.inl rfl

/-- Scalar multiples: Γ(X,U)-sections act on O(D)(U). -/
theorem smul_mem_divisorSections (D : WeilDivisor X) (a : Γ(X, U))
    {f : X.functionField} (hf : f ∈ divisorSections (X := X) hDVR U D) :
    a • f ∈ divisorSections (X := X) hDVR U D :=
  (divisorSections (X := X) hDVR U D).smul_mem a hf

end LeanFormal.IUT.XiFPaper.AG03DivisorsSectionsActual

end
