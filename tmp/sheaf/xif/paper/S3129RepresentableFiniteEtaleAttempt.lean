import tmp.sheaf.xif.paper.S1911RepresentableTwoPullbackActual
import tmp.sheaf.xif.paper.S3128PullbackCoproductActual

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleAttempt

/-- The etale stack over F represented by a scheme. -/
noncomputable def S3129YS (F : Type) [Field F] (S : SchemeOverField F) :
    EtaleStackOverField F where
  fiber := S1742YS (F := F) S
  isStack := inferInstance
  orbicurveSignature := none

/-- The explicit representable finite-etale target: the Yoneda image of a
scheme-level finite etale morphism is a representably finite etale stack map. -/
def S3129RepresentableFiniteEtaleTarget (F : Type) [Field F] : Type 1 :=
  forall {S T : SchemeOverField F} (f : S ⟶ T),
    AlgebraicGeometry.IsFinite f.left ->
    AlgebraicGeometry.Etale f.left ->
    EtaleStackFiniteEtaleMorphism
      (source := S3129YS (F := F) S) (target := S3129YS (F := F) T)
      (S1742StrongTransOfHom (F := F) f)

#check @S3129YS
#check @S3129RepresentableFiniteEtaleTarget
#check @S1911Witness
#check @S1911ConeEssSurj
#check @S1911RepresentableTwoPullbackPullbackSquare
#check @S1911RepresentableTwoPullbackPullbackSquare_proof
#check @S1911_not_representableTwoPullback

end LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleAttempt
end