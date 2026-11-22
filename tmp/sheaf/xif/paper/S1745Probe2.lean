import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.RingTheory.IsTensorProduct

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

#check @CategoryTheory.Limits.hasColimitsOfShape_op_of_hasLimitsOfShape
#check @CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape
#check @CategoryTheory.Discrete.opEquivalence
#check @CategoryTheory.Discrete.equivalence
#check @CategoryTheory.Limits.hasLimitsOfShape_of_equivalence
#check @CategoryTheory.Limits.hasColimitsOfShape_of_equivalence
#check @CategoryTheory.Limits.colimit.isoColimitCocone
#check @CategoryTheory.Limits.limit.isoLimitCone
#check @CategoryTheory.Limits.Cocone.precompose
#check @CategoryTheory.Limits.hasColimit_of_iso
#check @CategoryTheory.Limits.HasColimit.isoOfNatIso
#check @CategoryTheory.Limits.HasFiniteCoproducts
#check @CategoryTheory.ObjectProperty.op
#check @CategoryTheory.ObjectProperty.FullSubcategory
#check @CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_op
#check @CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_op
#check @CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence

namespace S1745

variable (K : Type) [Field K]

theorem finite_isClosedUnderIsomorphisms :
    (CommAlgCat.finite K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderIsomorphisms where
  of_iso e h := Module.Finite.equiv (CommAlgCat.algEquivOfIso e).toLinearEquiv

theorem etale_isClosedUnderIsomorphisms :
    (CommAlgCat.etale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderIsomorphisms where
  of_iso e h := Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso e)

instance instIsClosedUnderIsomorphisms :
    (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro X Y e ⟨hf, he⟩
    exact ⟨Module.Finite.equiv (CommAlgCat.algEquivOfIso e).toLinearEquiv,
      Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso e)⟩

/-- The Pi-algebra is the categorical product in CommAlgCat K. -/
noncomputable def piFan (J : Type) (A : J → CommAlgCat.{0} K) : Fan A :=
  Fan.mk (CommAlgCat.of K (∀ j, (A j : Type))) fun j =>
    CommAlgCat.ofHom (Pi.evalAlgHom K (fun j => (A j : Type)) j)

theorem piFan_isLimit (J : Type) (A : J → CommAlgCat.{0} K) : IsLimit (piFan K J A) := by
  refine Fan.IsLimit.mk _ (fun s => CommAlgCat.ofHom (AlgHom.pi fun j => (s.proj j).hom)) ?_ ?_
  · intro s j
    ext x
    rfl
  · intro s m hm
    ext x
    funext j
    have h := congrArg (fun f => (f : (piFan K J A).pt ⟶ A j).hom x) (hm j)
    simpa using h

end S1745
