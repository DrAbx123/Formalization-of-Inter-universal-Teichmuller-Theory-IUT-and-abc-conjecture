import tmp.sheaf.xif.paper.S3127G2UniversalDataOfLiftActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfLiftPreimageActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)
variable (B : S3127FiniteEtaleOverKFull l) (f : A ⟶ B)
variable (hf : ∀ g : G, S3127G2Action A act g ≫ f = f)

noncomputable def S3127G2UniversalDataOfLift_lift :
    (S3127FreeQuotientTargetOf A act hfree hInv).quotientObj ⟶ B :=
  CategoryTheory.Functor.preimage (S3127FullForget (l := l))
    (S3127G2UniversalDataOfLift_raw A act B f hf)

#check S3127G2UniversalDataOfLift_lift