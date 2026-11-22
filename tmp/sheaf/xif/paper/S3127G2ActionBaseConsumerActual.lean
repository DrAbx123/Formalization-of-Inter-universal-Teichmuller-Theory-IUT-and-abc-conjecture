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
namespace LeanFormal.IUT.XiFPaper.S3127G2ActionBaseConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)

theorem S3127G2ActionBaseConsumer_one_mul :
    S3127G2Action A act (1 : G) = 𝟙 A ∧
    (∀ g h : G,
      S3127G2Action A act (g * h) =
        S3127G2Action A act g ≫ S3127G2Action A act h) :=
  ⟨S3127G2Action_one A act, S3127G2Action_mul A act⟩

theorem S3127G2OverRAction_inv_consumer (g : G) :
    (act.act g).symm.hom ≫ A.obj.hom.left = A.obj.hom.left :=
  S3127OverRAction_inv A act g

#check S3127G2ActionBaseConsumer_one_mul
#check S3127G2OverRAction_inv_consumer
end LeanFormal.IUT.XiFPaper.S3127G2ActionBaseConsumerActual
end
