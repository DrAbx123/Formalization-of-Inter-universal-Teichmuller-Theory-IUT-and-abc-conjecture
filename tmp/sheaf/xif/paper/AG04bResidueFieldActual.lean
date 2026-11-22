import tmp.sheaf.xif.paper.AG02FunctionFieldActual
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# AG04b: residue fields at points (AG infrastructure, second layer)

The residue field at a point of a scheme (Mathlib IsLocalRing.ResidueField of the
stalk, reused), the residue class map, and the residue of a section at a point of
its open set.  These are the local data used by divisor/order bookkeeping; no
new proof of local ring theory is duplicated.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG04bResidueFieldActual

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The residue field at a point (reused Mathlib ResidueField of the stalk). -/
abbrev AGResidueField (X : Scheme.{u}) (x : X) : Type u :=
  IsLocalRing.ResidueField (X.presheaf.stalk x)

/-- The residue-class map from the stalk at a point to its residue field. -/
def agResidueClass (x : X) :
    X.presheaf.stalk x →+* AGResidueField X x :=
  IsLocalRing.residue (X.presheaf.stalk x)

/-- The residue-class map is the Mathlib residue map (definitional). -/
theorem agResidueClass_apply (x : X) (y : X.presheaf.stalk x) :
    agResidueClass x y = IsLocalRing.residue (X.presheaf.stalk x) y := rfl

/-- The residue field is a field (reused Mathlib instance). -/
def agResidueField_field (x : X) : Field (AGResidueField X x) := inferInstance

/-- The residue of a section at a point of its open set. -/
def agSectionResidue (U : X.Opens) [Nonempty U] (x : U) :
    Γ(X, U) →+* AGResidueField X x.1 :=
  (IsLocalRing.residue (X.presheaf.stalk x.1)).comp
    (X.presheaf.germ U x.1 x.2).hom

/-- The section residue factors through the germ (definitional). -/
theorem agSectionResidue_apply (U : X.Opens) [Nonempty U] (x : U)
    (f : Γ(X, U)) :
    agSectionResidue U x f =
      agResidueClass (X := X) x.1 ((X.presheaf.germ U x.1 x.2) f) :=
  rfl

end LeanFormal.IUT.XiFPaper.AG04bResidueFieldActual

end
