import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open CategoryTheory
open AlgebraicGeometry
open Polynomial

noncomputable def S2482AffineInvolutionAlgHom :
    MvPolynomial (Fin 2) F →ₐ[F] MvPolynomial (Fin 2) F :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else -MvPolynomial.X 1)

theorem S2482AffineInvolutionAlgHom_polynomial :
    S2482AffineInvolutionAlgHom S2482AffinePolynomial = S2482AffinePolynomial := by
  simp [S2482AffineInvolutionAlgHom, S2482AffinePolynomial,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial, S2482Curve]

noncomputable def S2482CoordinateRingInvolution :
    S2482CoordinateRing →ₐ[F] S2482CoordinateRing :=
  Ideal.Quotient.liftₐ (Ideal.span {S2482AffinePolynomial})
    ((Ideal.Quotient.mkₐ F (Ideal.span {S2482AffinePolynomial})).comp
      S2482AffineInvolutionAlgHom) (by
      intro a ha
      change Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
        (S2482AffineInvolutionAlgHom a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hmap : Ideal.map S2482AffineInvolutionAlgHom.toRingHom
          (Ideal.span {S2482AffinePolynomial}) ≤
            Ideal.span {S2482AffinePolynomial} := by
        have hpoly : S2482AffineInvolutionAlgHom.toRingHom S2482AffinePolynomial =
            S2482AffinePolynomial := S2482AffineInvolutionAlgHom_polynomial
        rw [Ideal.map_span, Set.image_singleton, hpoly]
      exact hmap (Ideal.mem_map_of_mem _ ha))

noncomputable def S2482AffineInvolution :
    S2482AffineOver ⟶ S2482AffineOver :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom S2482CoordinateRingInvolution.toRingHom))
    (by
      change Spec.map (CommRingCat.ofHom S2482CoordinateRingInvolution.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap F S2482CoordinateRing)) =
        Spec.map (CommRingCat.ofHom (algebraMap F S2482CoordinateRing))
      rw [← Spec.map_comp]
      rw [Spec.map_inj]
      ext r
      all_goals exact S2482CoordinateRingInvolution.commutes _)

noncomputable def S2482EllipticInvolution :
    S2482Orbicurve.Hom S2482Orbicurve :=
  S1742StrongTransOfHom (F := F) S2482AffineInvolution


end LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual

end