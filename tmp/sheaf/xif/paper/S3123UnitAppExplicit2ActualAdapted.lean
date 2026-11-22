import tmp.sheaf.xif.paper.S3123UnitNatExplicitActual

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
open LeanFormal.IUT.XiFPaper.S3123LeftExplicit2Actual
open LeanFormal.IUT.XiFPaper.S3123UnitCompExplicitActual
open LeanFormal.IUT.XiFPaper.S3123UnitNatExplicitActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitAppExplicit2ActualAdapted

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123UnitAppExplicit2
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (𝟭 (S3123LeftObj (l := l) U)) ≅
      (S3123FiberAppExplicit (l := l) U ≫
        S3123FiberAppInvExplicit (l := l) U) :=
  CategoryTheory.Cat.Hom.isoMk
    (NatIso.ofComponents
      (fun X => by rcases X with ⟨P⟩; exact S3123UnitCompExplicit (l := l) U P)
      (fun {X Y} f => S3123UnitNatExplicit (l := l) U f))

#check S3123UnitAppExplicit2

end LeanFormal.IUT.XiFPaper.S3123UnitAppExplicit2ActualAdapted
end
