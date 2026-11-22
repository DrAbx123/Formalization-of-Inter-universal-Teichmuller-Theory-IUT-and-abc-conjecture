import tmp.sheaf.xif.paper.S2521SchemeRestrictIsoActual
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Category.Cat

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2521SchemeRestrictIsoActual
noncomputable local instance : Field S2490A.K := inferInstance
noncomputable local instance : CommRing S2490A.K := inferInstance
noncomputable local instance : Algebra S2490A.K S2490A.K := Algebra.id S2490A.K
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2522PseudofunctorStrongTrans

abbrev K : Type := S2490A.K
abbrev C := Iut.SchemeOverField K

noncomputable def S2522StrongTrans :
    Pseudofunctor.StrongTrans
      (schemeRestrictScalarsPseudofunctor K K)
      (Pseudofunctor.id (LocallyDiscrete Cᵒᵖ)) where
  app a := Discrete.mk ((S2521RestrictIso.inv.app (Opposite.unop a.as)).op)
  naturality f := eqToIso (by
    apply Discrete.ext
    simp [app])
  naturality_naturality := by intro a b f g η; exact Subsingleton.elim _ _
  naturality_id := by intro a; exact Subsingleton.elim _ _
  naturality_comp := by intro a b c f g; exact Subsingleton.elim _ _
#check S2522StrongTrans
#print axioms S2522StrongTrans
end LeanFormal.IUT.XiFPaper.S2522PseudofunctorStrongTrans
end