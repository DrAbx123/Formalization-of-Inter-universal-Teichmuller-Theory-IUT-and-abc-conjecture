import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObject

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace ProbeZero

variable (K : Type) [Field K]

example : Algebra.Etale K PUnit := by infer_instance
example : Module.Finite K PUnit := by infer_instance
example : (CommAlgCat.finiteEtale K) (CommAlgCat.of K PUnit) := by
  constructor <;> infer_instance

-- is there an initial object in FiniteEtale?
example : IsInitial (CommAlgCat.FiniteEtale.of K K) := by
  refine IsInitial.ofUniqueHom ?_ ?_
  · intro X
    exact CommAlgCat.FiniteEtale.ofHom (Algebra.ofId K X.obj)
  · intro X f
    apply InducedCategory.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    exact Subsingleton.elim _ _

-- terminal in FiniteEtale: zero ring?
example : IsTerminal (CommAlgCat.FiniteEtale.of K PUnit) := by
  refine IsTerminal.ofUniqueHom ?_ ?_
  · intro X
    exact CommAlgCat.FiniteEtale.ofHom (Algebra.ofId K PUnit)
  · intro X f
    apply InducedCategory.hom_ext
    apply CommAlgCat.hom_ext
    ext x
    exact Subsingleton.elim _ _

end ProbeZero
