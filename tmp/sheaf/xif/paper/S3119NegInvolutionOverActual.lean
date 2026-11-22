import tmp.sheaf.xif.paper.S3119NegInvolutionCoreActual
import tmp.sheaf.xif.paper.S1419AutoProbe
import tmp.sheaf.xif.paper.S3119GeometricCorePrefixAttempt
import tmp.sheaf.xif.paper.S1742HomVcompActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S3119GeometricCorePrefixAttempt
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans

namespace LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual

variable {l : PrimeGeFive}

/-- The negative-point involution as an Over automorphism of the S1348 affine scheme. -/
noncomputable def S3119NegOverHom :
    S1419AffineOver l ⟶ S1419AffineOver l :=
  Probe.auto (l := l) S3119NegInvolutionAlgEquiv

theorem S3119NegAuto_refl :
    Probe.auto (l := l) (AlgEquiv.refl :
      S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l) =
      𝟙 (S1419AffineOver l) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
    (AlgEquiv.refl : S1348CoordinateRing l ≃ₐ[S1348K l]
      S1348CoordinateRing l).toRingEquiv.toRingHom) =
      𝟙 (S1419AffineScheme l)
  rw [show (AlgEquiv.refl : S1348CoordinateRing l ≃ₐ[S1348K l]
      S1348CoordinateRing l).toRingEquiv.toRingHom =
        RingHom.id (S1348CoordinateRing l) from rfl,
    CommRingCat.ofHom_id, Spec.map_id]

theorem S3119NegOverHom_sq :
    S3119NegOverHom (l := l) ≫ S3119NegOverHom =
      𝟙 (S1419AffineOver l) := by
  rw [S3119NegOverHom, Probe.auto_comp]
  rw [show S3119NegInvolutionAlgEquiv.trans S3119NegInvolutionAlgEquiv =
      AlgEquiv.refl from by
    apply AlgEquiv.ext
    intro x
    change S3119NegInvolutionAlgEquiv (S3119NegInvolutionAlgEquiv x) = x
    exact AlgHom.congr_fun (S3119NegQuotientHom_sq (l := l)) x]
  exact S3119NegAuto_refl (l := l)

/-- The elliptic involution on xF, induced by the Over automorphism. -/
noncomputable def S3119NegEllipticInvolution :
    (S1536XF (l := l)).Hom (S1536XF (l := l)) :=
  S3119StackLift (l := l) (S3119NegOverHom (l := l))

/-- Square of the induced stack-level involution. -/
noncomputable def S3119NegEllipticInvolution_squared :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp
        (S3119NegEllipticInvolution (l := l))
        (S3119NegEllipticInvolution (l := l)))
      (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l))) := by
  change Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) (S3119NegOverHom (l := l)))
      (S1742StrongTransOfHom (F := S1348K l) (S3119NegOverHom (l := l))) ≅
    Pseudofunctor.StrongTrans.id
      (S1742YS (F := S1348K l) (S1419AffineOver l))
  have hcomp : S1742HomOfStrongTrans (F := S1348K l)
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1348K l) (S3119NegOverHom (l := l)))
        (S1742StrongTransOfHom (F := S1348K l) (S3119NegOverHom (l := l)))) =
      𝟙 (S1419AffineOver l) := by
    rw [S1742HomOfStrongTrans_vcomp,
      S1742HomOfStrongTrans_strongTransOfHom]
    exact S3119NegOverHom_sq (l := l)
  let A := S1742StrongTransIsoOfHom (F := S1348K l)
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) (S3119NegOverHom (l := l)))
      (S1742StrongTransOfHom (F := S1348K l) (S3119NegOverHom (l := l))))
  let B := S1742StrongTransIsoOfHom (F := S1348K l)
    (Pseudofunctor.StrongTrans.id (S1742YS (F := S1348K l) (S1419AffineOver l)))
  exact (hcomp ▸ A).symm.trans B

#check S3119NegOverHom
#check S3119NegOverHom_sq
#check S3119NegEllipticInvolution
#check S3119NegEllipticInvolution_squared
#print axioms S3119NegOverHom_sq
#print axioms S3119NegEllipticInvolution_squared

end LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
end
