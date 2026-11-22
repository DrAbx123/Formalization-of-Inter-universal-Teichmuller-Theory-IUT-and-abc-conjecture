import tmp.sheaf.xif.paper.S1886D9OrbicurveActual
import tmp.sheaf.xif.paper.S1687Torsion23RealizationActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat

/-!
# S1898: the actual [-1] endomorphism of the S1726 orbicurve stack

S1886 reduces the D9 orbicurve to S1886PaperCF, whose first geometric
missing field is the elliptic involution

  S1886EllipticInvolutionMissing l = S1726Orbicurve.Hom S1726Orbicurve.

The tree previously contained only the curve-point involution (S1555/S1633);
no endomorphism of the represented etale stack was constructed.  This file
constructs it from:

* the actual coordinate-ring endomorphism x |-> x, y |-> -y of the affine
  Weierstrass model of E' (the same coordinate-ring method as S1653,
  specialized to the S1726 curve, where a1 = a3 = 0);
* the induced endomorphism of the representing scheme Spec R' over Spec F';
* 2-Yoneda: a morphism of representing schemes induces a strong
  transformation of the represented category-valued pseudofunctors.

The result is an actual term of S1886EllipticInvolutionMissing l.  No stack,
no signature and no morphism is inserted or postulated.  It is also proved
nonidentity: the actual S1687 3-torsion point with nonzero y-coordinate
lifts to F' and distinguishes y from -y.

## What remains after this file

The next missing datum for S1886PaperCF is the coherent sign-action
packaging (Iut.OrbicurveSignAction S1726Orbicurve, in particular its
pseudofunctor diagram and base equivalence) and then the genuine quotient
C_F = X_F/{+-1} of paper type (1,1)^pm with its sign-invariant quotient
morphism and universal property.  The tree has no construction of that
quotient stack.  This file does not assert S1886PaperCF.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

/-! ## 1. The coordinate-ring [-1] of the actual S1726 curve -/

/-- The polynomial endomorphism x |-> x, y |-> -y of the affine Weierstrass
coordinate ring of E'.  For the S1726 curve a1 = a3 = 0, so the elliptic
negation is exactly (x,y) |-> (x,-y). -/
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

theorem S1898PolyEndo_affinePolynomial :
    S1898PolyEndo S1726AffinePolynomial = S1726AffinePolynomial := by
  rw [S1726AffinePolynomial, weierstrassAffinePolynomial,
    S1726Curve_a₁, S1726Curve_a₃]
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

/-- The actual algebra endomorphism of the affine coordinate ring induced by
the elliptic negation [-1]. -/
noncomputable def S1898CoordEndo :
    S1726CoordinateRing →ₐ[S1726K] S1726CoordinateRing :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ (S1726K) _).comp S1898PolyEndo)
    (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (S1898PolyEndo_mem_ideal ha))

/-- The coordinate endomorphism sends the class of y to its negative. -/
theorem S1898CoordEndo_y :
    S1898CoordEndo (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
      (MvPolynomial.X 1)) =
      -Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 1) := by
  simp [S1898CoordEndo, S1898PolyEndo]

/-- The induced endomorphism of the affine scheme Spec R' over Spec F'. -/
noncomputable def S1898AffineEndo : S1726AffineOver ⟶ S1726AffineOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom))
    (by
      show Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap S1726K S1726CoordinateRing)) =
        Spec.map (CommRingCat.ofHom
          (algebraMap S1726K S1726CoordinateRing))
      erw [← Spec.map_comp]
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact S1898CoordEndo.commutes x)

/-! ## 2. 2-Yoneda: a scheme endomorphism induces a stack endomorphism -/

/-- The represented etale pseudofunctor of the actual S1726 affine model. -/
abbrev S1898Stack : Iut.EtaleStackPseudofunctor S1726K :=
  Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver

/-- The 2-Yoneda action on objects: postcomposition with a scheme
endomorphism. -/
noncomputable def S1898App
    (g : S1726AffineOver ⟶ S1726AffineOver)
    (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    S1898Stack.obj U ⟶ S1898Stack.obj U :=
  (Discrete.functor (fun P : Opposite.unop U.as ⟶ S1726AffineOver =>
    Discrete.mk (P ≫ g))).toCatHom

/-- All 2-cells between functors into a discrete category are unique, hence
so are modifications between the corresponding strong transformations. -/
instance S1898SubsingletonHom₂Discrete {C : Cat.{0, 0}} {A : Type}
    (G H : C ⟶ Cat.of (Discrete A)) : Subsingleton (G ⟶ H) := by
  constructor
  intro x y
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext Z
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- 2-Yoneda: a morphism of representing schemes over F' induces a strong
transformation of the represented stack. -/
noncomputable def S1898StackEndoOfSchemeEndo
    (g : S1726AffineOver ⟶ S1726AffineOver) :
    Pseudofunctor.StrongTrans S1898Stack S1898Stack where
  app U := S1898App g U
  naturality {a b} f := by
    refine Cat.Hom.isoMk (eqToIso ?_)
    apply CategoryTheory.Functor.ext
    · intro P Q h
      apply ULift.ext
      exact Subsingleton.elim _ _
    · intro P
      obtain ⟨g'⟩ := f
      apply Discrete.ext
      change g'.unop ≫ P.as ≫ g = g'.unop ≫ P.as ≫ g
      rfl
  naturality_naturality := by
    intro a b f h eta
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext Z
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext Z
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f h
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext Z
    apply ULift.ext
    exact Subsingleton.elim _ _

/-! ## 3. The actual elliptic involution -/

/-- The actual [-1] endomorphism of the S1726 orbicurve stack. -/
noncomputable def S1898EllipticInvolutionHom :
    Pseudofunctor.StrongTrans S1898Stack S1898Stack :=
  S1898StackEndoOfSchemeEndo S1898AffineEndo

/-- **The first missing field of S1886 is filled**: the actual geometric
[-1] endomorphism of the S1726 orbicurve. -/
noncomputable def S1898EllipticInvolution (l : PrimeGeFive) :
    S1886EllipticInvolutionMissing l :=
  S1898EllipticInvolutionHom

/-- The lift is definitionally the 2-Yoneda strong transformation. -/
theorem S1898EllipticInvolution_app
    (l : PrimeGeFive)
    (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    (S1898EllipticInvolution l).app U = S1898App S1898AffineEndo U := rfl

/-- The 2-Yoneda lift evaluated at the identity section of the affine model is
the scheme endomorphism itself. -/
theorem S1898EllipticInvolution_app_affine (l : PrimeGeFive) :
    ((S1898EllipticInvolution l).app
        (LocallyDiscrete.mk (Opposite.op S1726AffineOver))).toFunctor.obj
        (Discrete.mk (𝟙 S1726AffineOver)) = Discrete.mk S1898AffineEndo := by
  rw [S1898EllipticInvolution_app]
  simp [S1898App]

/-- The lift of the S1687 3-torsion point to F'. -/
theorem S1898LiftedPointEquation :
    S1726Curve.toAffine.Equation
      (S1720Lift (S1687Alpha S1687Y)) (S1720Lift S1687Y) := by
  have h : S1687AffineF.Equation (S1687Alpha S1687Y) S1687Y :=
    S1687Y_alpha_equation
  have h' : ((S1667Curve.toAffine).baseChange S1687Field).Equation
      (S1687Alpha S1687Y) S1687Y := by
    simpa [S1687AffineF, S1687CurveF] using h
  have h2 := WeierstrassCurve.Affine.Equation.baseChange
    (W := S1667Curve.toAffine) (f := S1720Lift) h'
  simpa [S1726Curve, S1726Curve_curve] using h2

/-- The lifted 3-torsion point has nonzero y-coordinate. -/
theorem S1898LiftedY_ne_zero : S1720Lift S1687Y ≠ 0 := by
  intro h
  exact S1687Y_ne_zero (S1720Lift.injective (by simpa using h))

/-- The coordinate endomorphism is not the identity: the actual 3-torsion
point with nonzero y-coordinate distinguishes `y` from `-y`. -/
theorem S1898CoordEndo_ne_id :
    S1898CoordEndo ≠ AlgHom.id S1726K S1726CoordinateRing := by
  intro h
  let ψ : S1726CoordinateRing →ₐ[S1726K] S1726K :=
    S1726PointAlgHom (S1720Lift (S1687Alpha S1687Y)) (S1720Lift S1687Y)
      S1898LiftedPointEquation
  have hψ : ψ.comp S1898CoordEndo = ψ := by
    rw [h, AlgHom.comp_id]
  have h2 := congrArg (fun φ : S1726CoordinateRing →ₐ[S1726K] S1726K =>
    φ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
      (MvPolynomial.X 1))) hψ
  rw [AlgHom.comp_apply, S1898CoordEndo_y, map_neg] at h2
  have hy : ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
      (MvPolynomial.X 1)) = S1720Lift S1687Y := by
    simp [ψ]
  rw [hy] at h2
  have h3 : (2 : S1726K) * S1720Lift S1687Y = 0 := by
    linear_combination -h2
  exact S1898LiftedY_ne_zero ((mul_eq_zero.mp h3).resolve_left (by norm_num))

/-- The scheme endomorphism is not the identity. -/
theorem S1898AffineEndo_ne_id : S1898AffineEndo ≠ 𝟙 S1726AffineOver := by
  intro h
  have hleft := congrArg
    (fun f : S1726AffineOver ⟶ S1726AffineOver => f.left) h
  change Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) =
    𝟙 (Spec (CommRingCat.of S1726CoordinateRing)) at hleft
  have hspec : Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) =
      Spec.map (𝟙 (CommRingCat.of S1726CoordinateRing)) := by
    simpa using hleft
  have hringCat : CommRingCat.ofHom S1898CoordEndo.toRingHom =
      𝟙 (CommRingCat.of S1726CoordinateRing) :=
    Spec.map_injective hspec
  have hring : S1898CoordEndo.toRingHom = RingHom.id S1726CoordinateRing :=
    congrArg CommRingCat.Hom.hom hringCat
  apply S1898CoordEndo_ne_id
  ext x
  exact congrArg (fun f : S1726CoordinateRing →+* S1726CoordinateRing => f x) hring

/-- **The actual 2-Yoneda lift is not the identity**: it is the geometric
[-1] involution, not a degenerate choice of an endomorphism. -/
theorem S1898EllipticInvolution_ne_id (l : PrimeGeFive) :
    S1898EllipticInvolution l ≠
      Pseudofunctor.StrongTrans.id S1898Stack := by
  intro h
  have h1 := congrArg
    (fun e : Pseudofunctor.StrongTrans S1898Stack S1898Stack =>
      (e.app (LocallyDiscrete.mk (Opposite.op S1726AffineOver))).toFunctor.obj
        (Discrete.mk (𝟙 S1726AffineOver))) h
  rw [S1898EllipticInvolution_app_affine] at h1
  have hid : (Pseudofunctor.StrongTrans.id S1898Stack).app
      (LocallyDiscrete.mk (Opposite.op S1726AffineOver)) =
      𝟙 (S1898Stack.obj (LocallyDiscrete.mk (Opposite.op S1726AffineOver))) := rfl
  rw [hid, Cat.Hom.id_toFunctor] at h1
  exact S1898AffineEndo_ne_id (congrArg Discrete.as h1)

/-- The exact next missing datum of S1886PaperCF: the coherent sign-action
packaging of the actual involution.  The tree constructs neither the
pseudofunctor diagram nor its base equivalence; this structure records the
precise required object and ties its inversion field to the actual
endomorphism constructed above. -/
structure S1898SignActionPackaging (l : PrimeGeFive) where
  /-- A coherent sign action on the actual S1726 orbicurve. -/
  action : Iut.OrbicurveSignAction S1726Orbicurve
  /-- Its inversion is the actual [-1] endomorphism of this file. -/
  inversion_eq : action.inversion = S1898EllipticInvolution l

/-! ## 4. Axiom footprint -/

#print axioms S1898PolyEndo_affinePolynomial
#print axioms S1898CoordEndo
#print axioms S1898CoordEndo_y
#print axioms S1898AffineEndo
#print axioms S1898StackEndoOfSchemeEndo
#print axioms S1898EllipticInvolutionHom
#print axioms S1898EllipticInvolution
#print axioms S1898EllipticInvolution_app
#print axioms S1898EllipticInvolution_app_affine
#print axioms S1898LiftedPointEquation
#print axioms S1898LiftedY_ne_zero
#print axioms S1898CoordEndo_ne_id
#print axioms S1898AffineEndo_ne_id
#print axioms S1898EllipticInvolution_ne_id

end LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

end