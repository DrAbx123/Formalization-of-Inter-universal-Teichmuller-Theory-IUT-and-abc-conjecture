import tmp.sheaf.xif.paper.S3123UnitActual
import tmp.sheaf.xif.paper.S3123FiberEquivalenceActual

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
open LeanFormal.IUT.XiFPaper.S3123UnitActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitNatOldTypeActual

variable {l : PrimeGeFive}

abbrev S3123UnitNatOldType
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    {X Y : (S3123Left (l := l)).obj U} (f : X ⟶ Y) : Prop :=
  (𝟭 ((S3123Left (l := l)).obj U)).map f ≫
      (S3123UnitComp (l := l) U Y.as).hom =
    (S3123UnitComp (l := l) U X.as).hom ≫
      ((S3123FiberApp (l := l) U ≫
        S3123FiberAppInv (l := l) U).toFunctor.map f)

#check S3123UnitNatOldType

end LeanFormal.IUT.XiFPaper.S3123UnitNatOldTypeActual
end
