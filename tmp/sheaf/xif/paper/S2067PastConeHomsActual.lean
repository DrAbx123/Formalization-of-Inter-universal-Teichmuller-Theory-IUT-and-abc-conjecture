import tmp.sheaf.xif.paper.S2066PastLiftToYComponentsActual

/-! # S2067: cast lemmas for the pastCone2 cone morphism

The eqToHom-cast version of `pastCone2Hom.toX` needs the interaction of
`eqToHom` in a hom-category with whiskering.  The two lemmas below provide
that interaction without unfolding any nested `Iso.trans`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2067PastConeHomsActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut

universe u
variable {F : Type u} [Field F]

/-- Whiskering an equality-cast 2-cell on the right. -/
theorem S2067_eqToHom_whiskerRight
    {a b c : EtaleStackPseudofunctor F} {f f' : a ⟶ b} (h : f = f')
    (g : b ⟶ c) :
    Pseudofunctor.StrongTrans.whiskerRight (CategoryTheory.eqToHom h) g =
      CategoryTheory.eqToHom
        (congrArg (fun z => Pseudofunctor.StrongTrans.vcomp z g) h) := by
  cases h
  rw [whiskerRight_id]

/-- Whiskering an equality-cast 2-cell on the left. -/
theorem S2067_eqToHom_whiskerLeft
    {a b c : EtaleStackPseudofunctor F} {g g' : b ⟶ c} (h : g = g')
    (f : a ⟶ b) :
    Pseudofunctor.StrongTrans.whiskerLeft f (CategoryTheory.eqToHom h) =
      CategoryTheory.eqToHom
        (congrArg (fun z => Pseudofunctor.StrongTrans.vcomp f z) h) := by
  cases h
  rw [id_whiskerLeft]

#print axioms S2067_eqToHom_whiskerRight
#print axioms S2067_eqToHom_whiskerLeft

end LeanFormal.IUT.XiFPaper.S2067PastConeHomsActual

end
