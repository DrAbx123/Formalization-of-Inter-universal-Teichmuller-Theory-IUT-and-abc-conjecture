import tmp.sheaf.xif.paper.S3127G2TargetUnitActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127GammaCompActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT.XiFPaper.S3127G2TargetUnitActual
universe u
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalUnitActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- Explicit data still required for the quotient universal property. -/
structure S3127G2UniversalPhiPackage
    {A : S3127FiniteEtaleOverKFull l} {G : Type} [Group G] [Fintype G]
    (T : S3127FreeQuotientTarget A G) : Type (u+1) where
  lift : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B),
    (∀ g : G, T.action g ≫ f = f) → (T.quotientObj ⟶ B)
  fac : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f),
    T.quotientMap ≫ lift f hf = f
  uniq : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f) (v : T.quotientObj ⟶ B),
    T.quotientMap ≫ v = f → v = lift f hf

theorem S3127QuotientUniversal_of_phi
    {A : S3127FiniteEtaleOverKFull l} {G : Type} [Group G] [Fintype G]
    (T : S3127FreeQuotientTarget A G)
    (P : S3127G2UniversalPhiPackage T) :
    S3127QuotientUniversal T := by
  intro B f hf
  refine ⟨P.lift f hf, P.fac f hf, ?_⟩
  intro v hv
  exact P.uniq f hf v hv

#check S3127QuotientUniversal_of_phi
end LeanFormal.IUT.XiFPaper.S3127G2UniversalUnitActual
end
