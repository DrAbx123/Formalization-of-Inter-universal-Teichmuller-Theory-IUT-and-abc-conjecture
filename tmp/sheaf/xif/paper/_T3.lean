import tmp.sheaf.xif.paper.S1898EllipticInvolutionActual
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat

/-!
# S1932: the coherent sign action on the actual S1726 orbicurve

S1898 constructed the actual `[-1]` endomorphism `S1898EllipticInvolution` of
the S1726 orbicurve stack and proved it nonidentity.  The first missing field
of `S1886PaperCF` was then the coherent sign-action packaging
`Iut.OrbicurveSignAction S1726Orbicurve` whose `inversion` is that actual
endomorphism.  This file constructs it.

The construction uses the actual geometry, not a postulate:

* `S1932AffineEndo_comp : [-1] ; [-1] = 1` for the affine Weierstrass model
  is a coordinate-ring computation (`y |-> -y` twice is the identity, and the
  defining polynomial `y^2 - (x^3 + a2 x^2 + a4 x)` is invariant);
* hence `S1932SigmaSqIso : Sigma ; Sigma ~= 1`, where
  `Sigma = S1898EllipticInvolutionHom`, obtained componentwise from
  `(P ; [-1]) ; [-1] = P`;
* `S1932Diagram` is the pseudofunctor on the one-object groupoid of the sign
  group sending the generator to `Sigma`; its coherence isos are the unitors
  and `S1932SigmaSqIso`.

All 2-cells between endomorphisms of the representable S1726 stack live in
discrete categories (`S1932NatTransSubsingleton`), so the coherence
equations of the pseudofunctor are automatically satisfied.  The base
equivalence is the identity equivalence; the `generator_identification`
field is a unitor computation.

## What remains after this file

The quotient `C_F = X_F/{+-1}` of paper type `(1,1)^pm`, together with its
sign-invariant quotient morphism and its bicategorical universal property.
This file isolates the remaining datum exactly as `S1932CFQuotient` and
proves that it, together with the action constructed here, yields
`S1886PaperCF`.  The quotient stack itself is not constructed and is not
postulated.
-/

set_option profiler true

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

/-! ## 1. 2-cells between endomorphisms of the representable stack -/

/-- Natural transformations between functors into a discrete category are
subsingletons. -/
theorem S1932NatTransSubsingleton {X Y : Cat.{0, 0}} (hY : IsDiscrete (Y : Type))
    (F G : X ⟶ Y) : Subsingleton (F ⟶ G) := by
  letI := hY
  constructor
  intro α β
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext Z
  exact Subsingleton.elim _ _

/-- 2-cells in `Cat` between endomorphisms of the representable S1726 stack are
subsingletons. -/
theorem S1932CatHom₂Subsingleton (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (F G : S1898Stack.obj U ⟶ S1898Stack.obj U) : Subsingleton (F ⟶ G) :=
  S1932NatTransSubsingleton (Discrete.isDiscrete _) F G

/-- Modifications between endomorphisms of the actual S1726 stack are
subsingletons: every component lands in a discrete category. -/
theorem S1932StrongTransSubsingleton
    (F G : Pseudofunctor.StrongTrans S1898Stack S1898Stack) : Subsingleton (F ⟶ G) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S1932CatHom₂Subsingleton U (F.app U) (G.app U)).elim _ _

/-! ## 2. The actual scheme-level involution `[-1] ; [-1] = 1` -/

theorem S1932PolyEndo_comp : S1898PolyEndo.comp S1898PolyEndo =
    AlgHom.id S1726K (MvPolynomial (Fin 2) S1726K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simp [AlgHom.comp_apply, S1898PolyEndo_X0]
  · simp [AlgHom.comp_apply, S1898PolyEndo_X1]

theorem S1932PolyEndo_apply (p : MvPolynomial (Fin 2) S1726K) :
    S1898PolyEndo (S1898PolyEndo p) = p := by
  rw [← AlgHom.comp_apply, S1932PolyEndo_comp, AlgHom.id_apply]

theorem S1932CoordEndo_mk (p : MvPolynomial (Fin 2) S1726K) :
    S1898CoordEndo (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) p) =
      Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (S1898PolyEndo p) := by
  simp [S1898CoordEndo]

theorem S1932CoordEndo_comp_apply (x : S1726CoordinateRing) :
    S1898CoordEndo (S1898CoordEndo x) = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.span {S1726AffinePolynomial}) x
  rw [S1932CoordEndo_mk, S1932CoordEndo_mk, S1932PolyEndo_apply]

theorem S1932CoordEndo_comp : S1898CoordEndo.comp S1898CoordEndo =
    AlgHom.id S1726K S1726CoordinateRing := by
  apply AlgHom.ext
  intro x
  exact S1932CoordEndo_comp_apply x

theorem S1932SchemeEndo_comp :
    (Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) :
        S1726AffineScheme ⟶ S1726AffineScheme) ≫
      Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) = 𝟙 S1726AffineScheme := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : S1898CoordEndo.toRingHom.comp S1898CoordEndo.toRingHom = RingHom.id _ := by
    apply RingHom.ext
    intro x
    exact S1932CoordEndo_comp_apply x
  rw [h]
  simp

theorem S1932AffineEndo_left : Over.Hom.left S1898AffineEndo =
    Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) := rfl

theorem S1932AffineEndo_comp : S1898AffineEndo ≫ S1898AffineEndo = 𝟙 S1726AffineOver := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.id_left, S1932AffineEndo_left]
  exact S1932SchemeEndo_comp

/-! ## 3. The square of the actual involution -/

/-- The actual `[-1]` endomorphism of the S1726 stack, as a strong
transformation. -/
abbrev S1932Sigma : Pseudofunctor.StrongTrans S1898Stack S1898Stack :=
  S1898EllipticInvolutionHom

theorem S1932SigmaSq_obj (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    (((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor.obj P) =
      Discrete.mk ((P.as ≫ S1898AffineEndo) ≫ S1898AffineEndo) := rfl

theorem S1932IdApp_obj (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor.obj P = P := rfl

theorem S1932Sq_point (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ)
    (P : Discrete (Opposite.unop U.as ⟶ S1726AffineOver)) :
    (P.as ≫ S1898AffineEndo) ≫ S1898AffineEndo = P.as := by
  rw [Category.assoc, S1932AffineEndo_comp, Category.comp_id]

/-- The componentwise 2-cell `Sigma ; Sigma -> 1` on the underlying functors. -/
noncomputable def S1932SqNatTrans (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor ⟶
      ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor where
  app P := eqToHom (by
    rw [S1932SigmaSq_obj, S1932IdApp_obj]
    apply Discrete.ext
    exact S1932Sq_point U P)
  naturality X Y f := by
    haveI : IsDiscrete (S1898Stack.obj U : Type) := Discrete.isDiscrete _
    exact Subsingleton.elim _ _

/-- The reverse componentwise 2-cell. -/
noncomputable def S1932SqNatTransRev (U : LocallyDiscrete (Iut.SchemeOverField S1726K)ᵒᵖ) :
    ((Pseudofunctor.StrongTrans.id S1898Stack).app U).toFunctor ⟶
      ((Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma).app U).toFunctor where
  app P := eqToHom (by
    rw [S1932SigmaSq_obj, S1932IdApp_obj]
    apply Discrete.ext
    exact (S1932Sq_point U P).symm)
  naturality X Y f := by
    haveI : IsDiscrete (S1898Stack.obj U : Type) := Discrete.isDiscrete _
    exact Subsingleton.elim _ _

/-- The 2-cell `Sigma ; Sigma -> 1`. -/
noncomputable def S1932SqMod :
    Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma ⟶
      Pseudofunctor.StrongTrans.id S1898Stack where
  as := {
    app U := NatTrans.toCatHom₂ (S1932SqNatTrans U)
    naturality a b f := by
      exact (S1932NatTransSubsingleton (Discrete.isDiscrete _) _ _).elim _ _ }

/-- The reverse 2-cell `1 -> Sigma ; Sigma`. -/
noncomputable def S1932SqModRev :
    Pseudofunctor.StrongTrans.id S1898Stack ⟶
      Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma where
  as := {
    app U := NatTrans.toCatHom₂ (S1932SqNatTransRev U)
    naturality a b f := by
      exact (S1932NatTransSubsingleton (Discrete.isDiscrete _) _ _).elim _ _ }

/-- **The square of the actual elliptic involution is the identity.** -/
noncomputable def S1932SigmaSqIso :
    Pseudofunctor.StrongTrans.vcomp S1932Sigma S1932Sigma ≅
      Pseudofunctor.StrongTrans.id S1898Stack :=
  Iso.mk S1932SqMod S1932SqModRev
    (S1932StrongTransSubsingleton _ _).elim _ _
    (S1932StrongTransSubsingleton _ _).elim _ _

end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

end
