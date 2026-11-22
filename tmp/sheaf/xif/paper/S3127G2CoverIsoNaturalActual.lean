import tmp.sheaf.xif.paper.S3127G2CoverIsoActual
import tmp.sheaf.xif.paper.S3127G2GammaAlgHomActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2GammaAlgHomActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2CoverIsoNaturalActual
variable {l : PrimeGeFive}

theorem S3127G2CoverIso_natural {A B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B) :
    let R := S1348CoordinateRing l
    let YA := A.obj.left.left
    let YB := B.obj.left.left
    let homA := A.obj.hom.left
    let homB := B.obj.hom.left
    letI : Algebra R (Scheme.Γ.obj (Opposite.op YA)) := gammaAlgebraOf YA homA
    letI : Algebra R (Scheme.Γ.obj (Opposite.op YB)) := gammaAlgebraOf YB homB
    letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op YA)) :=
      gammaEtaleOf YA homA A.property.2 (by rfl)
    letI : Module.Finite R (Scheme.Γ.obj (Opposite.op YA)) :=
      gammaFiniteOf YA homA A.property.1 (by rfl)
    letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op YB)) :=
      gammaEtaleOf YB homB B.property.2 (by rfl)
    letI : Module.Finite R (Scheme.Γ.obj (Opposite.op YB)) :=
      gammaFiniteOf YB homB B.property.1 (by rfl)
    (S3127G2CoverIsoA A).hom ≫
      affineCoverMapOfAlgHom
        (inferInstance : Algebra.Etale R (Scheme.Γ.obj (Opposite.op YA)))
        (inferInstance : Module.Finite R (Scheme.Γ.obj (Opposite.op YA)))
        (inferInstance : Algebra.Etale R (Scheme.Γ.obj (Opposite.op YB)))
        (inferInstance : Module.Finite R (Scheme.Γ.obj (Opposite.op YB)))
        (gammaAlgHomOfFullHom f) =
      S3127FullForget.map f ≫ (S3127G2CoverIsoA B).hom := by
  let R := S1348CoordinateRing l
  let YA := A.obj.left.left
  let YB := B.obj.left.left
  let homA := A.obj.hom.left
  let homB := B.obj.hom.left
  letI : Algebra R (Scheme.Γ.obj (Opposite.op YA)) := gammaAlgebraOf YA homA
  letI : Algebra R (Scheme.Γ.obj (Opposite.op YB)) := gammaAlgebraOf YB homB
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op YA)) :=
    gammaEtaleOf YA homA A.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op YA)) :=
    gammaFiniteOf YA homA A.property.1 (by rfl)
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op YB)) :=
    gammaEtaleOf YB homB B.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op YB)) :=
    gammaFiniteOf YB homB B.property.1 (by rfl)
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change A.obj.left.left.isoSpec.hom ≫
      Spec.map (Scheme.Hom.appTop (Over.Hom.left (Over.Hom.left f.hom))) =
    Over.Hom.left (Over.Hom.left f.hom) ≫
      B.obj.left.left.isoSpec.hom
  exact Scheme.isoSpec_hom_naturality
    (Over.Hom.left (Over.Hom.left f.hom))

#check S3127G2CoverIso_natural
end LeanFormal.IUT.XiFPaper.S3127G2CoverIsoNaturalActual
end
