import tmp.sheaf.xif.paper.S3123LeftExplicitActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual

namespace LeanFormal.IUT.XiFPaper.S3123LeftMapActual

variable {l : PrimeGeFive}

noncomputable def S3123LeftMap
    {U V : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : U ⟶ V) :
    S3123LeftObj (l := l) U ⟶ S3123LeftObj (l := l) V :=
  cast (congrArg₂ (fun (A B : Cat) => (A ⟶ B))
    (S3123LeftObj_eq (l := l) U).symm
    (S3123LeftObj_eq (l := l) V).symm)
    ((S3123Left (l := l)).map g)

@[simp] lemma S3123LeftMap_eq_cast
    {U V : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : U ⟶ V) :
    S3123LeftMap (l := l) g =
      cast (congrArg₂ (fun (A B : Cat) => (A ⟶ B))
        (S3123LeftObj_eq (l := l) U).symm
        (S3123LeftObj_eq (l := l) V).symm)
        ((S3123Left (l := l)).map g) := rfl

#check S3123LeftMap
#check S3123LeftMap_eq_cast

end LeanFormal.IUT.XiFPaper.S3123LeftMapActual
end
