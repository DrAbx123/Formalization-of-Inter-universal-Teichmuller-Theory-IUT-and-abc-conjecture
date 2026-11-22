import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Examples

open CategoryTheory CategoryTheory.Limits

universe u

namespace S1747Probe

variable {K : Type} [Field K]

example (X Y : (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) (i : X ⟶ Y) :
    True := by
  let φ := i.unop.hom.hom
  -- what's the type?
  have h : Y.unop.obj ⟶ X.unop.obj := i.unop.hom
  trivial

#check CommAlgCat.FiniteEtale.ofHom
#check CommAlgCat.FiniteEtale.of
#check CommAlgCat.hom_ext
#check InducedCategory.hom_ext

end S1747Probe
