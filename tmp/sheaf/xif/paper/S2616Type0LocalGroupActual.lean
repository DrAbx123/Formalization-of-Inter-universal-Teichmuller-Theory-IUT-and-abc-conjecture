import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Algebra.Field.ZMod

noncomputable section
open CategoryTheory

namespace LeanFormal.IUT.XiFPaper.S2616Type0LocalGroupActual

/-- A Type0 local group: a group whose carrier is a Type0 small type. -/
structure Type0LocalGroup where
  carrier : Type
  group : Group carrier

attribute [instance] Type0LocalGroup.group

/-- The one-object category attached to a Type0 local group. -/
abbrev GroupCat (G : Type0LocalGroup) : Type := SingleObj G.carrier

instance groupSmallCategory (G : Type0LocalGroup) : SmallCategory (GroupCat G) :=
  inferInstanceAs (Category.{0, 0} (SingleObj G.carrier))

instance groupEssentiallySmall (G : Type0LocalGroup) :
    EssentiallySmall.{0, 0, 0} (GroupCat G) :=
  ⟨GroupCat G, groupSmallCategory G, ⟨CategoryTheory.Equivalence.refl (C := GroupCat G)⟩⟩

#check Type0LocalGroup
#check groupEssentiallySmall

end LeanFormal.IUT.XiFPaper.S2616Type0LocalGroupActual
end