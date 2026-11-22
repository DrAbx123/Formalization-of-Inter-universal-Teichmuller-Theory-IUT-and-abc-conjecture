import tmp.sheaf.xif.paper.S3127G2GammaInvariantInterfaceActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAlgHomActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2GammaBridgeProbe2ActualAdapted
variable {l : PrimeGeFive} {G : Type} [Group G]
variable {A : S3127FiniteEtaleOverKFull l} (act : S3127OverRAction A G)

theorem S3127G2GammaActionBridge_probe2 (g : G) :
    letI := gammaMulSemiringAction act.act
    letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
    groupActionRingEquiv (Scheme.Γ.obj (Opposite.op A.obj.left.left)) G g =
      gammaAut ((act.act g).symm) := by
  letI := gammaMulSemiringAction act.act
  letI := gammaAlgebraOf A.obj.left.left A.obj.hom.left
  apply RingEquiv.ext
  intro x
  change (gammaActionHom act.act g) x = (gammaAut ((act.act g).symm)) x
  rfl

#check S3127G2GammaActionBridge_probe2
end LeanFormal.IUT.XiFPaper.S3127G2GammaBridgeProbe2ActualAdapted
end
