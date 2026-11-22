import tmp.sheaf.xif.paper.S3123LeftMapCompActual

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
open LeanFormal.IUT.XiFPaper.S3123LeftMapActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapIdActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapCompActual

namespace LeanFormal.IUT.XiFPaper.S3123LeftExplicit2Actual

variable {l : PrimeGeFive}

instance S3123LeftObjThin
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    Quiver.IsThin (S3123LeftObj (l := l) U) := by
  change Quiver.IsThin (Cat.of (Discrete (Opposite.unop U.as ⟶
    S3123BaseChangedScheme (l := l))))
  exact S3123FiberStrongTransActual.S3123DiscreteThin _

set_option maxHeartbeats 800000 in
noncomputable def S3123LeftExplicit : Iut.EtaleStackPseudofunctor (S1280Arithmetic l).K :=
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
    (fun U => S3123LeftObj (l := l) U)
    (fun {_ _} g => S3123LeftMap (l := l) g)
    (fun U => S3123LeftMapId (l := l) U)
    (fun {_ _ _} f g => S3123LeftMapComp (l := l) f g)
    (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)

#check S3123LeftExplicit

end LeanFormal.IUT.XiFPaper.S3123LeftExplicit2Actual
end
