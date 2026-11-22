import tmp.sheaf.xif.paper.S1886D9OrbicurveActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

/-! ## 1. The coordinate-ring [-1] of the actual S1726 curve -/

/-- The polynomial endomorphism x |-> x, y |-> -y of the affine Weierstrass
coordinate ring of E'.  (For the S1726 curve a1 = a3 = 0, so the elliptic
negation is exactly (x,y) |-> (x,-y).) -/
noncomputable def S1898PolyEndo :
    MvPolynomial (Fin 2) S1726K →ₐ[S1726K] MvPolynomial (Fin 2) S1726K :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X 0 else -MvPolynomial.X 1)

theorem S1898PolyEndo_X0 :
    S1898PolyEndo (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [S1898PolyEndo]

theorem S1898PolyEndo_X1 :
    S1898PolyEndo (MvPolynomial.X 1) = -MvPolynomial.X 1 := by
  simp [S1898PolyEndo]

theorem S1898Curve_a1 : S1726Curve.a₁ = (0 : S1726K) := S1726Curve_a₁

theorem S1898Curve_a3 : S1726Curve.a₃ = (0 : S1726K) := S1726Curve_a₃

theorem S1898PolyEndo_affinePolynomial :
    S1898PolyEndo S1726AffinePolynomial = S1726AffinePolynomial := by
  rw [S1726AffinePolynomial, weierstrassAffinePolynomial, S1898Curve_a1, S1898Curve_a3]
  simp [S1898PolyEndo]

theorem S1898PolyEndo_mem_ideal :
    Ideal.span {S1726AffinePolynomial} ≤
      Ideal.comap (S1898PolyEndo).toRingHom
        (Ideal.span {S1726AffinePolynomial}) := by
  rw [Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact Ideal.subset_span (by simp [S1898PolyEndo_affinePolynomial])

noncomputable def S1898CoordEndo :
    S1726CoordinateRing →ₐ[S1726K] S1726CoordinateRing :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ (S1726K) _).comp S1898PolyEndo)
    (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (S1898PolyEndo_mem_ideal ha))

theorem S1898CoordEndo_y :
    S1898CoordEndo (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
      (MvPolynomial.X 1)) =
      -Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 1) := by
  simp [S1898CoordEndo, S1898PolyEndo]

theorem S1898AffineEndo_w :
    Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap S1726K S1726CoordinateRing)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap S1726K S1726CoordinateRing)) := by
  erw [← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact S1898CoordEndo.commutes x

noncomputable def S1898AffineEndo : S1726AffineOver ⟶ S1726AffineOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom))
    (by
      show Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap S1726K S1726CoordinateRing)) =
        Spec.map (CommRingCat.ofHom
          (algebraMap S1726K S1726CoordinateRing))
      exact S1898AffineEndo_w)

abbrev S1898Stack : Iut.EtaleStackPseudofunctor S1726K :=
  Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver

noncomputable def S1898App
    (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    S1898Stack.obj U ⟶ S1898Stack.obj U :=
  (Discrete.functor (fun P : Opposite.unop U.as ⟶ S1726AffineOver =>
    Discrete.mk (P ≫ S1898AffineEndo))).toCatHom

#check S1898App
#check S1898Stack
#check S1726Orbicurve.stack.fiber

instance S1898SubsingletonHom₂Discrete {C : Cat.{0, 0}} {A : Type}
    (G H : C ⟶ Cat.of (Discrete A)) : Subsingleton (G ⟶ H) := by
  constructor
  intro x y
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

noncomputable def S1898EllipticInvolutionHom :
    Pseudofunctor.StrongTrans S1898Stack S1898Stack where
  app U := S1898App U
  naturality {a b} f := by
    refine Cat.Hom.isoMk (eqToIso ?_)
    apply CategoryTheory.Functor.ext
    · intro P Q g
      apply ULift.ext
      exact Subsingleton.elim _ _
    · intro P
      obtain ⟨g⟩ := f
      apply Discrete.ext
      simp [S1898App, S1898Stack, Iut.schemeRepresentableEtalePseudofunctor,
        Iut.schemeRepresentableFiberFunctor, Category.assoc]
  naturality_naturality := by
    intro a b f g eta
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _

#check S1898EllipticInvolutionHom
#check @CategoryTheory.Functor.ext
#check @S1898SubsingletonHom₂Discrete

end LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual