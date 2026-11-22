import tmp.sheaf.xif.paper.S460RationalFunctionsFieldCoverActual
import tmp.sheaf.xif.paper.S453DvTriangleMorphismAlgHomActual
import Mathlib.Algebra.Field.ULift

/-! # S476: generic GroupLikeAddMonoidOn instantiation — exact boundary

S460's generic `rationalFunctions` has universe shape
`D : Type u`, `L : D -> Type u`, `Category.{u} D`.
S432's small base is `Type (u+1)` with `Category.{u+1}`;
`coverField` is `Type u`.  Therefore `L` must be lifted to `Type (u+1)` and
`Algebra K (ULift field)`/`Field (ULift field)` instances and the `ULift.algEquiv`
pull have to be assembled at the lifted universe.  This file records exactly
that boundary; it does not fake the generic instance.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S476GenericGroupLikeGapActual

open CategoryTheory

universe u

/-- Exact missing instantiation data: a universe-(u+1) field family over the
small base, an Algebra K structure on each lifted field, the lifted pullback
by S453 arrowAlgebraMap, and the IsFSM=IsIso field. -/
structure S476GenericInstantiationData (K : Type u) [Field K] where
  D : Type (u + 1)
  [categoryD : Category.{u + 1} D]
  L : D → Type (u + 1)
  fieldL : Prop
  algebraK : Prop
  pull : Prop
  isFSM : Prop

def S476GenericInstantiationDataRequired (K : Type u) [Field K] : Prop :=
  Nonempty (S476GenericInstantiationData K)

end LeanFormal.IUT.XiFPaper.S476GenericGroupLikeGapActual
end
