import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeActionDataActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)

structure S3127G2FreeActionData : Type where
  action : G → (A ⟶ A)
  action_one : action 1 = 𝟙 A
  action_mul : ∀ g h : G, action (g * h) = action g ≫ action h
  free : ∀ (x : A.obj.left.left) (g : G),
    (action g).hom.left.left x = x → g = 1

noncomputable def S3127G2FreeActionData.of
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1) :
    S3127G2FreeActionData A act where
  action := S3127G2Action A act
  action_one := S3127G2Action_one A act
  action_mul := S3127G2Action_mul A act
  free := hfree

#check S3127G2FreeActionData
#check S3127G2FreeActionData.of
end LeanFormal.IUT.XiFPaper.S3127G2FreeActionDataActual
end
