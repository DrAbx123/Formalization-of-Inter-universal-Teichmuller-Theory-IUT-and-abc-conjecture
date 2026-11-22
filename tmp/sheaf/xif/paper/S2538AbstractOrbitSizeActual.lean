import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2535LocalizedIntegralClosureActual
import tmp.sheaf.xif.paper.S2532LocalizedDefinitionsActual
import tmp.sheaf.xif.paper.S2532LocalizedAbstractActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2538AbstractOrbitSizeActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual
attribute [local instance] Ideal.Quotient.field
/-- Abstract localized orbit-size statement over a Dedekind domain R and an
integral closure S in L. -/
def AbstractDedekindFrobeniusOrbitSizeStatement
    (R K L S : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [CommRing S] [Algebra R S] [Algebra S L]
    [IsScalarTower R S L] [IsIntegralClosure S R L]
    [MulSemiringAction Gal(L/K) S] [SMulCommClass Gal(L/K) R S]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : R[X]) (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R L)).Splits) : Prop :=
  ∃ sigma : Gal(L/K), IsArithFrobAt R sigma P ∧
    orbitSizeMultiset (rootPermR R K L f hsplit sigma) =
      factorDegrees (f.map (Ideal.Quotient.mk p))
#check AbstractDedekindFrobeniusOrbitSizeStatement
end LeanFormal.IUT.XiFPaper.S2538AbstractOrbitSizeActual
end
