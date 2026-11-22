import tmp.sheaf.xif.paper.S2495cFUnconditionalActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S2470SignActionActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2463InvariantQuotientActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2496cFMapActual

/-- The x-coordinate ring map `F[x] -> F[X,Y]/(y^2+x*y-x^3-5)`. -/
noncomputable def S2496phi : MvPolynomial (Fin 1) F →+* S2482CoordinateRing :=
  MvPolynomial.eval₂Hom (algebraMap F S2482CoordinateRing)
    (fun _ => Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0))

noncomputable def S2496f : S2482AffineOver ⟶ S2495FOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom S2496phi)) (by
    have hcomp : S2496phi.comp (MvPolynomial.C : F →+* MvPolynomial (Fin 1) F) =
        algebraMap F S2482CoordinateRing :=
      MvPolynomial.eval₂Hom_comp_C (algebraMap F S2482CoordinateRing)
        (fun _ => Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0))
    dsimp [S2495FOver, S2463cFOver, S2482AffineOver]
    rw [← Spec.map_comp]
    rw [show CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom S2496phi =
        CommRingCat.ofHom (S2496phi.comp (MvPolynomial.C : F →+* MvPolynomial (Fin 1) F)) from rfl]
    rw [hcomp])

noncomputable def S2496StrongTrans := S1742StrongTransOfHom (F := F) S2496f

noncomputable def S2496Map : S2482Orbicurve.Hom S2495cF := by
  change Pseudofunctor.StrongTrans
    (Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver)
    (Iut.schemeRepresentableEtalePseudofunctor F S2495FOver)
  exact S1742StrongTransOfHom (F := F) S2496f

theorem S2496StrongTrans_type :
    Nonempty (Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver)
      (Iut.schemeRepresentableEtalePseudofunctor F S2495FOver)) :=
  ⟨S2496StrongTrans⟩

#print axioms S2496phi
#print axioms S2496f

end LeanFormal.IUT.XiFPaper.S2496cFMapActual
end