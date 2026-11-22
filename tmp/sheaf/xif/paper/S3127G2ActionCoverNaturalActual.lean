import tmp.sheaf.xif.paper.S3127G2AffineCoverActionActual
import tmp.sheaf.xif.paper.S3127G2CoverIsoActual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2ActionCoverNaturalActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- Naturality of the G2 cover trivialization: the full-forget image of the
anabelian action equals the conjugated raw cover action, hence commutes with the
cover isomorphism `S3127G2CoverIsoA`. -/
theorem S3127G2ActionCoverNatural
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    S3127FullForget.map (S3127G2Action A act g) ≫ (S3127G2CoverIsoA A).hom =
      (S3127G2CoverIsoA A).hom ≫ (S3127G2AffineCoverAction A act g).hom := by
  have hmap := congrArg
    (fun m => m ≫ (S3127G2CoverIsoA A).hom)
    (S3127G2FullForget_map_raw A act g)
  have hfac := congrArg
    (fun m => (S3127G2CoverIsoA A).hom ≫ m)
    (S3127G2AffineCoverAction_hom A act g)
  exact hmap.trans
    ((Iso.hom_inv_id_assoc (S3127G2CoverIsoA A)
      ((S3127G2RawCoverAction A act g).hom ≫
        (S3127G2CoverIsoA A).hom)).symm.trans hfac.symm)

#check S3127G2ActionCoverNatural
end LeanFormal.IUT.XiFPaper.S3127G2ActionCoverNaturalActual
end
