import tmp.sheaf.xif.paper.S2540CorrectedObjectMapActual
import tmp.sheaf.xif.paper.S2542FunctorFaithfulActual
import tmp.sheaf.xif.paper.S2540FullBridgeActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.XiFPaper.S2540CorrectedObjectMapActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2540FullBridgeActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2543CorrectedQuotMapActual

/-- Corrected algebra cover map over S2482CoordinateRing: algebra hom A → B
gives a cover map between the S2538-inverse objects, using the equivalence
instead of the F-level S2534Map. -/
noncomputable def S2543AlgCoverMapR {A B : CommAlgCat.FiniteEtale S2482CoordinateRing}
    (f : A ⟶ B) :
    S2538AffineCoverEquiv.inverse.obj (Opposite.op B) ⟶
      S2538AffineCoverEquiv.inverse.obj (Opposite.op A) :=
  S2538AffineCoverEquiv.inverse.map (Quiver.Hom.op f)

/-- Corrected quotient map on orbicurve covers. -/
noncomputable def S2543QuotMapR {A B : CommAlgCat.FiniteEtale S2482CoordinateRing}
    (f : A ⟶ B) :
    S1728CoverMapClass (S2540ObjectMap B) (S2540ObjectMap A) :=
  S2519InvFunctor.map (S2543AlgCoverMapR f)

/-- Exact surjectivity target for the corrected map. -/
def S2543QuotMapRSurjective : Prop :=
  ∀ {A B : CommAlgCat.FiniteEtale S2482CoordinateRing},
    Function.Surjective (S2543QuotMapR (A := A) (B := B))

theorem S2543QuotMapR_eq_functorMap {A B : CommAlgCat.FiniteEtale S2482CoordinateRing}
    (f : A ⟶ B) :
    S2543QuotMapR f = S2540Functor.map (Quiver.Hom.op f) := rfl

#check S2543AlgCoverMapR
#check S2543QuotMapR
#check S2543QuotMapRSurjective

end LeanFormal.IUT.XiFPaper.S2543CorrectedQuotMapActual
end
