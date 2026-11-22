import tmp.sheaf.xif.paper.S3121SignActionActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S3119NegInvolutionOverActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S3121StrongTransVcompActual
import tmp.sheaf.xif.paper.S3121DiagramActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.n8.closure.RepresentableStackIsStackConstructed
import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual

set_option maxHeartbeats 800000

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S3121SignActionActual

namespace LeanFormal.IUT.XiFPaper.S3121QuotientActual

variable {l : PrimeGeFive}

abbrev S3121F := (S1280Arithmetic l).F

/-- The affine line over F as an object of `SchemeOverField F`. -/
noncomputable def S3121LineOver : Iut.SchemeOverField (S3121F (l := l)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap (S3121F (l := l)) (Polynomial (S3121F (l := l))))))

theorem S3121LineIsStack :
    (Iut.schemeRepresentableEtalePseudofunctor (S3121F (l := l))
      (S3121LineOver (l := l))).IsStack
      (Iut.SchemeOverField.etaleTopology (S3121F (l := l))) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology (S3121F (l := l)))
      (yoneda.obj (S3121LineOver (l := l))) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf
        (F := S3121F (l := l)) (S3121LineOver (l := l)))
  change (discretePseudo (C := Iut.SchemeOverField (S3121F (l := l)))
    (yoneda.obj (S3121LineOver (l := l)))).IsStack
      (Iut.SchemeOverField.etaleTopology (S3121F (l := l)))
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj (S3121LineOver (l := l))) hP

noncomputable def S3121cF : Iut.HyperbolicOrbicurve (S3121F (l := l)) :=
  realizedHyperbolicOrbicurve (S3121F (l := l))
    (Iut.schemeRepresentableEtalePseudofunctor (S3121F (l := l))
      (S3121LineOver (l := l)))
    (S3121LineIsStack (l := l))
    (sourceTypeOneOnePlusMinus)
    (sourceTypeOneOnePlusMinus_hyperbolic)

theorem S3121cF_signature :
    (S3121cF (l := l)).signature = sourceTypeOneOnePlusMinus := rfl

/-- The x-coordinate class in the S1348 coordinate ring. -/
noncomputable def S3121X0 : S1348CoordinateRing l :=
  Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l}) (MvPolynomial.X 0)

/-- The quotient ring map `F[x] -> R`, `x |-> x0`. -/
noncomputable def S3121QRing :
    Polynomial (S3121F (l := l)) →ₐ[S3121F (l := l)] S1348CoordinateRing l :=
  Polynomial.aeval (S3121X0 (l := l))

#check S3121cF
#check S3121cF_signature
#check S3121QRing


/-- The affine morphism `Spec R -> Spec F[x]` induced by `F[x] -> R`, `x |-> x0`. -/
noncomputable def S3121QScheme :
    S1419AffineOver (l := l) ⟶ S3121LineOver (l := l) :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (S3121QRing (l := l)).toRingHom)) (by
    change Spec.map (CommRingCat.ofHom (S3121QRing (l := l)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (S3121F (l := l)) (Polynomial (S3121F (l := l))))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (S3121F (l := l)) (S1348CoordinateRing l)))
    erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact (S3121QRing (l := l)).commutes x)

/-- The stack morphism `X_F -> cF` induced by the x-coordinate quotient map. -/
noncomputable abbrev S3121QuotientMap :
    Pseudofunctor.StrongTrans
      (S1742YS (F := S3121F (l := l)) (S1419AffineOver l))
      (S1742YS (F := S3121F (l := l)) (S3121LineOver (l := l))) :=
  S1742StrongTransOfHom (F := S3121F (l := l)) (S3121QScheme (l := l))

#check S3121QScheme
#check S3121QuotientMap

theorem S3121QRing_neg :
    (S3119NegQuotientHom :
      S1348CoordinateRing l →ₐ[S3121F (l := l)] S1348CoordinateRing l).comp
        (S3121QRing (l := l)) =
      S3121QRing (l := l) := by
  apply Polynomial.algHom_ext
  rw [AlgHom.comp_apply, S3121QRing, Polynomial.aeval_X]
  change S3119NegQuotientHom (S3121X0 (l := l)) = S3121X0 (l := l)
  rw [show S3121X0 (l := l) =
      Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (MvPolynomial.X 0) from rfl]
  rw [S3119NegQuotientHom_mk, S3119NegPolyHom_X0]

theorem S3121QScheme_neg :
    S3119NegOverHom (l := l) ≫ S3121QScheme (l := l) =
      S3121QScheme (l := l) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom
      (S3119NegQuotientHom (l := l)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (S3121QRing (l := l)).toRingHom) =
    Spec.map (CommRingCat.ofHom (S3121QRing (l := l)).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg Spec.map
    (congrArg CommRingCat.ofHom
      (congrArg AlgHom.toRingHom (S3121QRing_neg (l := l))))

theorem S3121QuotientMap_comp_neg :
    Iut.HyperbolicOrbicurve.Hom.comp
        (S3121SignActionActual (l := l)).inversion
        (show (S1536XF (l := l)).Hom (S3121cF (l := l)) from
          S3121QuotientMap (l := l)) =
      (show (S1536XF (l := l)).Hom (S3121cF (l := l)) from
        S3121QuotientMap (l := l)) := by
  have hv : (S3121SignActionActual (l := l)).inversion =
      S1742StrongTransOfHom (F := S3121F (l := l))
        (S3119NegOverHom (l := l)) := rfl
  rw [hv]
  change Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S3121F (l := l)) (S3119NegOverHom (l := l)))
      (S1742StrongTransOfHom (F := S3121F (l := l)) (S3121QScheme (l := l))) =
    S1742StrongTransOfHom (F := S3121F (l := l)) (S3121QScheme (l := l))
  rw [S3121StrongTransOfHom_vcomp, S3121QScheme_neg]

noncomputable def S3121Quotient :
    Iut.OrbicurveSignInvariantMorphism
      (S3121SignActionActual (l := l)) (S3121cF (l := l)) where
  map := show (S1536XF (l := l)).Hom (S3121cF (l := l)) from
    S3121QuotientMap (l := l)
  invariant := by
    change Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp (S3121SignActionActual (l := l)).inversion
        (show (S1536XF (l := l)).Hom (S3121cF (l := l)) from
          S3121QuotientMap (l := l)))
      (show (S1536XF (l := l)).Hom (S3121cF (l := l)) from
        S3121QuotientMap (l := l))
    exact eqToIso (S3121QuotientMap_comp_neg (l := l))
  cocycle := by
    let inv : Pseudofunctor.StrongTrans
        (S1742YS (F := S3121F (l := l)) (S1419AffineOver l))
        (S1742YS (F := S3121F (l := l)) (S1419AffineOver l)) :=
      (S3121SignActionActual (l := l)).inversion
    let eta : Pseudofunctor.StrongTrans
        (S1742YS (F := S3121F (l := l)) (S1419AffineOver l))
        (S1742YS (F := S3121F (l := l)) (S3121LineOver (l := l))) :=
      Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp inv inv)
        (S3121QuotientMap (l := l))
    let theta : Pseudofunctor.StrongTrans
        (S1742YS (F := S3121F (l := l)) (S1419AffineOver l))
        (S1742YS (F := S3121F (l := l)) (S3121LineOver (l := l))) :=
      S3121QuotientMap (l := l)
    haveI := LeanFormal.IUT.XiFPaper.S3121DiagramActual.S3121StrongTransHomSubsingleton
      (F := S3121F (l := l)) (S := S1419AffineOver l)
      (T := S3121LineOver (l := l)) eta theta
    apply Subsingleton.elim (α := eta ⟶ theta)
