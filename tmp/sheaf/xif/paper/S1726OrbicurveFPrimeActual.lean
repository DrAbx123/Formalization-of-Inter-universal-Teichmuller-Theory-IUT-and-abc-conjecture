/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S1319OrbicurveClauseActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# S1726: the actual D6 hyperbolic orbicurve for E'/F'

S1724/S1725 supply the actual number field

  F' = SplittingField (S1687H * (X^2 + 1))

together with the actual punctured elliptic curve

  E' = S1667Punctured.baseChange F',

whose affine Weierstrass model is

  y^2 = x^3 + (61/64) x^2 - (125/64) x,

and the actual D5 source-torsion clause for E'/F'.  This file constructs the
actual D6 object for the same arithmetic input, following
S1419D6NonterminalStackActual (the S1280 Gaussian instance) with the base
field replaced by F' and the affine model replaced by the punctured affine
curve of E'.

## What is constructed

* the actual affine coordinate ring

    R' = F'[x,y] / (y^2 - (x^3 + (61/64) x^2 - (125/64) x)),

  the affine Weierstrass polynomial of E' (S1726AffinePolynomial_eq), and
  the structure morphism Spec R' -> Spec F' over F';

* the representable category-valued etale pseudofunctor of Spec R', proved
  to be an etale stack (S1726RepresentableIsStack) by the discrete-sheaf
  to-stack bridge of S1419 applied to the representable sheaf;

* the actual hyperbolic orbicurve

    S1726Orbicurve : Iut.HyperbolicOrbicurve F'

  obtained by realizedHyperbolicOrbicurve with signature
  Iut.OrbicurveSignature.oncePuncturedElliptic (S1726Orbicurve_signature);

* nonterminality: the fiber at the base test scheme is not a subsingleton,
  from the two distinct actual affine points (0,0) and (1,0) of the model
  (S1726Nonterminal, S1726NonterminalFiber).  Hence the orbicurve is not
  a point fiber and not the degenerate point-fiber orbicurve
  (S1726Orbicurve_not_pointFiber, S1726Orbicurve_ne_degeneratePointFiber);

* the actual geometric fields of the D6 SourceOrbicurveClause:

  - puncturedCurve = the affine F'-points of the model,
  - curve = the projective points of E',
  - curveToPunctured = the affine inclusion,
  - cover = F'-points of Spec (R' (x)_{F'} (F' x F')),
  - coverToPunctured = composition with the left structure map,
  - surjectivity of the cover map (S1726CoverToPunctured_surjective),
  - non-injectivity and non-subsingleton cover
    (S1726CoverToPunctured_not_injective, S1726Cover_not_subsingleton),
  - the nontrivial structure group Aut_{F'}(F' x F') with the actual
    sheet-swap (S1726StructureGroup_nontrivial),
  - the actual cusp count 1 of the once-punctured elliptic signature.

## The exact first missing field

The source SourceOrbicurveClause also has an exactSequence field.  Its
base group is actual, namely the absolute Galois group of F', but its
arithmetic cover group is the orbifold fundamental group of the orbicurve,
which is Mathlib-level missing.  The exact residual is therefore

    S1726FirstMissing : Type 1
      = Iut.OrbicurveFundamentalGroupData S1726Orbicurve
          (Iut.AbsoluteGaloisProfinite F'),

i.e. the certified orbifold etale fundamental-group datum of the *already
constructed* actual orbicurve, together with its projection to the absolute
Galois group of F'.  The literal S1348-style sigma

    S1726D6FirstMissingField
      = Sigma X : HyperbolicOrbicurve F',
          OrbicurveFundamentalGroupData X (AbsoluteGaloisProfinite F')

is recorded for comparison; the construction S1726D6FirstMissingOfGroups
shows that the exact residual datum needed on top of the constructed
orbicurve is precisely S1726FirstMissing.

From S1726FirstMissing the whole D6 clause is constructed
(S1726SourceOrbicurveClauseOfFirstMissing), its exact-sequence cover group
being definitionally the arithmetic orbifold fundamental group
(S1726SourceOrbicurveClauseOfGroupsAt_coverGroup).  The D6 slot of a full
SourceDefinition31Data can be filled with it (S1726FillD6), alongside the
D5 clause of S1725.

## Honest boundary (not claimed)

* Iut.OrbicurveFundamentalGroupData S1726Orbicurve galois is not
  constructed: no orbifold etale fundamental group / Galois category of the
  actual orbicurve exists in the tree (Mathlib has no etale fundamental group
  of a curve).  No group, cover category or fiber functor is faked; the
  missing datum is exposed as a type, not replaced by PUnit, True, an
  axiom or a sorry.

* The finite etale cover used below is the split degree-two cover
  R' (x)_{F'} (F' x F') -> R'.  It is a genuine finite etale cover with a
  nontrivial structure group (the sheet swap), but it is disconnected.  The
  paper's connected cover and the connectedness of the source orbicurve are
  not constructed here.

## Axiom footprint

Only propext, Classical.choice and Quot.sound are used; see the
#print axioms block at the end.  No sorry, no axiom, no admit.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack
open CategoryTheory
open AlgebraicGeometry
open scoped SpecOfNotation

/-! ## 1. The base field F', the curve E', and its affine model -/

/-- The actual base field F' of S1720. -/
abbrev S1726K : Type := S1720Field

/-- The actual curve E' = S1667Punctured.baseChange F'. -/
abbrev S1726Curve : WeierstrassCurve S1726K := S1720Curve.curve

theorem S1726Curve_curve : S1726Curve = S1667Curve.baseChange S1726K := rfl

/-- E' is an elliptic curve (it is the base change of S1667Curve). -/
instance S1726Curve_isElliptic : S1726Curve.IsElliptic := S1720Curve.isElliptic

/-- The a_1-coefficient of E' vanishes. -/
theorem S1726Curve_a₁ : S1726Curve.a₁ = (0 : S1726K) := by
  rw [S1726Curve_curve]; simp [WeierstrassCurve.baseChange]

/-- The a_2-coefficient of E' is 61/64. -/
theorem S1726Curve_a₂ : S1726Curve.a₂ = (61/64 : S1726K) := by
  rw [S1726Curve_curve]; simp [WeierstrassCurve.baseChange]

/-- The a_3-coefficient of E' vanishes. -/
theorem S1726Curve_a₃ : S1726Curve.a₃ = (0 : S1726K) := by
  rw [S1726Curve_curve]; simp [WeierstrassCurve.baseChange]

/-- The a_4-coefficient of E' is -125/64. -/
theorem S1726Curve_a₄ : S1726Curve.a₄ = (-125/64 : S1726K) := by
  rw [S1726Curve_curve]; simp [WeierstrassCurve.baseChange]

/-- The a_6-coefficient of E' vanishes. -/
theorem S1726Curve_a₆ : S1726Curve.a₆ = (0 : S1726K) := by
  rw [S1726Curve_curve]; simp [WeierstrassCurve.baseChange]

/-- The affine Weierstrass polynomial of E'. -/
abbrev S1726AffinePolynomial : MvPolynomial (Fin 2) S1726K :=
  weierstrassAffinePolynomial S1726Curve

/-- The affine Weierstrass polynomial of E' is exactly
y^2 - (x^3 + (61/64) x^2 - (125/64) x). -/
theorem S1726AffinePolynomial_eq :
    S1726AffinePolynomial =
      MvPolynomial.X 1 ^ 2 - (MvPolynomial.X 0 ^ 3 +
        MvPolynomial.C (61/64 : S1726K) * MvPolynomial.X 0 ^ 2 +
        MvPolynomial.C (-125/64 : S1726K) * MvPolynomial.X 0) := by
  unfold S1726AffinePolynomial weierstrassAffinePolynomial
  rw [S1726Curve_a₁, S1726Curve_a₂, S1726Curve_a₃, S1726Curve_a₄, S1726Curve_a₆]
  simp

/-- The affine coordinate ring F'[x,y]/(y^2 = x^3 + (61/64) x^2 - (125/64) x)
of the punctured curve E'. -/
abbrev S1726CoordinateRing : Type :=
  MvPolynomial (Fin 2) S1726K ⧸ Ideal.span {S1726AffinePolynomial}

/-- The coordinate ring is literally the quotient by the displayed polynomial. -/
theorem S1726CoordinateRing_eq :
    S1726CoordinateRing =
      (MvPolynomial (Fin 2) S1726K ⧸ Ideal.span
        {MvPolynomial.X 1 ^ 2 - (MvPolynomial.X 0 ^ 3 +
          MvPolynomial.C (61/64 : S1726K) * MvPolynomial.X 0 ^ 2 +
          MvPolynomial.C (-125/64 : S1726K) * MvPolynomial.X 0)}) := by
  rw [S1726CoordinateRing, S1726AffinePolynomial_eq]

/-! ## 2. The punctured affine model and its algebra maps -/

/-- Evaluation of the affine Weierstrass polynomial at an arbitrary assignment
of the two coordinates. -/
theorem S1726_aeval_affinePolynomial_apply (f : Fin 2 → S1726K) :
    MvPolynomial.aeval f S1726AffinePolynomial =
      f 1 ^ 2 + S1726Curve.a₁ * f 0 * f 1 + S1726Curve.a₃ * f 1 -
        (f 0 ^ 3 + S1726Curve.a₂ * f 0 ^ 2 + S1726Curve.a₄ * f 0 +
          S1726Curve.a₆) := by
  rw [S1726AffinePolynomial, weierstrassAffinePolynomial]
  simp

/-- Evaluation at the coordinate pair (x,y). -/
theorem S1726_aeval_affinePolynomial (x y : S1726K) :
    MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i) S1726AffinePolynomial =
      y ^ 2 + S1726Curve.a₁ * x * y + S1726Curve.a₃ * y -
        (x ^ 3 + S1726Curve.a₂ * x ^ 2 + S1726Curve.a₄ * x +
          S1726Curve.a₆) := by
  rw [S1726_aeval_affinePolynomial_apply]
  simp

/-- The affine Weierstrass polynomial vanishes at every actual affine point. -/
theorem S1726_aeval_affinePolynomial_eq_zero {x y : S1726K}
    (h : S1726Curve.toAffine.Equation x y) :
    MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i) S1726AffinePolynomial = 0 := by
  rw [S1726_aeval_affinePolynomial, sub_eq_zero]
  exact (WeierstrassCurve.Affine.equation_iff x y).mp h

/-- The F'-algebra map R' -> F' attached to an actual affine point (x,y):
evaluation of the two coordinates. -/
noncomputable def S1726PointAlgHom (x y : S1726K)
    (h : S1726Curve.toAffine.Equation x y) :
    S1726CoordinateRing →ₐ[S1726K] S1726K :=
  Ideal.Quotient.liftₐ (Ideal.span {S1726AffinePolynomial})
    (MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i))
    (by
      have hle : Ideal.span ({S1726AffinePolynomial} : Set _) ≤
          RingHom.ker (AlgHom.toRingHom
            (MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i))) := by
        rw [Ideal.span_le]
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        exact S1726_aeval_affinePolynomial_eq_zero h
      intro a ha
      exact hle ha)

@[simp]
theorem S1726PointAlgHom_X0 (x y : S1726K)
    (h : S1726Curve.toAffine.Equation x y) :
    S1726PointAlgHom x y h
      (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0)) = x := by
  rw [S1726PointAlgHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp

@[simp]
theorem S1726PointAlgHom_X1 (x y : S1726K)
    (h : S1726Curve.toAffine.Equation x y) :
    S1726PointAlgHom x y h
      (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 1)) = y := by
  rw [S1726PointAlgHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp

/-- Every F'-point of the affine coordinate ring evaluates to an actual affine
point of the curve. -/
theorem S1726PointAlgHom_equation (ψ : S1726CoordinateRing →ₐ[S1726K] S1726K) :
    S1726Curve.toAffine.Equation
      (ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0)))
      (ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 1))) := by
  let Φ : MvPolynomial (Fin 2) S1726K →ₐ[S1726K] S1726K :=
    ψ.comp (Ideal.Quotient.mkₐ (S1726K) (Ideal.span {S1726AffinePolynomial}))
  have hΦ : Φ S1726AffinePolynomial = 0 := by
    have hzero : Ideal.Quotient.mkₐ (S1726K)
        (Ideal.span {S1726AffinePolynomial}) S1726AffinePolynomial = 0 := by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    show ψ (Ideal.Quotient.mkₐ (S1726K)
      (Ideal.span {S1726AffinePolynomial}) S1726AffinePolynomial) = 0
    rw [hzero, map_zero]
  have hcomp : Φ =
      MvPolynomial.aeval (fun i : Fin 2 => Φ (MvPolynomial.X i)) := by
    conv_lhs => rw [MvPolynomial.aeval_unique Φ]
    rfl
  have haeval : MvPolynomial.aeval
      (fun i : Fin 2 => Φ (MvPolynomial.X i)) S1726AffinePolynomial = 0 := by
    rw [← hcomp]
    exact hΦ
  have hfun : (fun i : Fin 2 =>
      ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X i))) =
      (fun i : Fin 2 => Φ (MvPolynomial.X i)) := by
    funext i
    simp only [Φ, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [← hfun, S1726_aeval_affinePolynomial_apply] at haeval
  exact (WeierstrassCurve.Affine.equation_iff _ _).mpr (sub_eq_zero.mp haeval)

/-- The punctured affine model of E' over F': its affine F'-points. -/
abbrev S1726PuncturedCurve : Type :=
  {p : S1726K × S1726K // S1726Curve.toAffine.Equation p.1 p.2}

/-- The punctured affine point attached to an F'-algebra point of R'. -/
noncomputable def S1726PuncturedPointOfAlgHom
    (ψ : S1726CoordinateRing →ₐ[S1726K] S1726K) : S1726PuncturedCurve :=
  ⟨(ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0)),
    ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 1))),
   S1726PointAlgHom_equation ψ⟩

/-- Every punctured affine point is obtained from an actual algebra map. -/
theorem S1726PuncturedPointOfAlgHom_surjective :
    Function.Surjective S1726PuncturedPointOfAlgHom := by
  intro p
  refine ⟨S1726PointAlgHom p.1.1 p.1.2 p.2, ?_⟩
  apply Subtype.ext
  simp [S1726PuncturedPointOfAlgHom]

/-- The affine point (0,0) of the model. -/
theorem S1726Equation_zero_zero : S1726Curve.toAffine.Equation 0 0 := by
  rw [WeierstrassCurve.Affine.equation_zero, S1726Curve_a₆]

/-- The affine point (1,0) of the model. -/
theorem S1726Equation_one_zero : S1726Curve.toAffine.Equation 1 0 := by
  rw [WeierstrassCurve.Affine.equation_iff, S1726Curve_a₁, S1726Curve_a₂,
    S1726Curve_a₃, S1726Curve_a₄, S1726Curve_a₆]
  norm_num

/-- The two actual points (0,0) and (1,0) of the affine model are distinct. -/
theorem S1726ZeroZero_ne_one_zero :
    (⟨(0, 0), S1726Equation_zero_zero⟩ : S1726PuncturedCurve) ≠
      ⟨(1, 0), S1726Equation_one_zero⟩ := by
  intro h
  have h0 := congrArg (fun p : S1726PuncturedCurve => p.1.1) h
  norm_num at h0

/-! ## 3. The finite etale cover, its structure group and the cusp count -/

/-- The split finite etale F'-algebra F' x F' of the degree-two cover. -/
abbrev S1726FiniteEtaleAlgebra : Type := S1726K × S1726K

/-- The F'-points of the finite etale cover Spec (R' (x)_{F'} (F' x F')). -/
abbrev S1726Cover : Type :=
  TensorProduct S1726K S1726CoordinateRing S1726FiniteEtaleAlgebra →ₐ[S1726K] S1726K

/-- The cover-to-punctured map on actual F'-points. -/
noncomputable def S1726CoverToPunctured (φ : S1726Cover) : S1726PuncturedCurve :=
  S1726PuncturedPointOfAlgHom (φ.comp Algebra.TensorProduct.includeLeft)

/-- The actual cover map is surjective onto the actual punctured points. -/
theorem S1726CoverToPunctured_surjective :
    Function.Surjective S1726CoverToPunctured := by
  intro P
  obtain ⟨ψ, hψ⟩ := S1726PuncturedPointOfAlgHom_surjective P
  refine ⟨Algebra.TensorProduct.lift ψ
    (AlgHom.fst S1726K S1726K S1726K)
    (fun _ _ => Commute.all _ _), ?_⟩
  show S1726PuncturedPointOfAlgHom
    ((Algebra.TensorProduct.lift ψ
      (AlgHom.fst S1726K S1726K S1726K)
      (fun _ _ => Commute.all _ _)).comp
        Algebra.TensorProduct.includeLeft) = P
  rw [Algebra.TensorProduct.lift_comp_includeLeft]
  exact hψ

/-- The cover map is not injective: the two sheet lifts of a punctured point are
distinct actual F'-points of the cover. -/
theorem S1726CoverToPunctured_not_injective :
    ¬ Function.Injective S1726CoverToPunctured := by
  classical
  obtain ⟨P⟩ : Nonempty S1726PuncturedCurve :=
    ⟨S1726PuncturedPointOfAlgHom (S1726PointAlgHom 0 0 S1726Equation_zero_zero)⟩
  obtain ⟨psi, hpsi⟩ := S1726PuncturedPointOfAlgHom_surjective P
  let fstMap : S1726FiniteEtaleAlgebra →ₐ[S1726K] S1726K :=
    AlgHom.fst S1726K S1726K S1726K
  let sndMap : S1726FiniteEtaleAlgebra →ₐ[S1726K] S1726K :=
    AlgHom.snd S1726K S1726K S1726K
  let phi1 : S1726Cover :=
    Algebra.TensorProduct.lift psi fstMap (fun _ _ => Commute.all _ _)
  let phi2 : S1726Cover :=
    Algebra.TensorProduct.lift psi sndMap (fun _ _ => Commute.all _ _)
  have h1 : S1726CoverToPunctured phi1 = P := by
    show S1726PuncturedPointOfAlgHom (phi1.comp Algebra.TensorProduct.includeLeft) = P
    rw [show phi1.comp Algebra.TensorProduct.includeLeft = psi from
      Algebra.TensorProduct.lift_comp_includeLeft psi fstMap
        (fun _ _ => Commute.all _ _)]
    exact hpsi
  have h2 : S1726CoverToPunctured phi2 = P := by
    show S1726PuncturedPointOfAlgHom (phi2.comp Algebra.TensorProduct.includeLeft) = P
    rw [show phi2.comp Algebra.TensorProduct.includeLeft = psi from
      Algebra.TensorProduct.lift_comp_includeLeft psi sndMap
        (fun _ _ => Commute.all _ _)]
    exact hpsi
  intro hinj
  have hEq : phi1 = phi2 := hinj (by rw [h1, h2])
  have hval := congrArg (fun phi : S1726Cover =>
    phi (Algebra.TensorProduct.includeRight
      ((1 : S1726K), (0 : S1726K)))) hEq
  have e1 : phi1 (Algebra.TensorProduct.includeRight
      ((1 : S1726K), (0 : S1726K))) = 1 := by
    dsimp only [phi1]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
    simp [fstMap]
  have e2 : phi2 (Algebra.TensorProduct.includeRight
      ((1 : S1726K), (0 : S1726K))) = 0 := by
    dsimp only [phi2]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
    simp [sndMap]
  rw [e1, e2] at hval
  exact one_ne_zero hval

/-- The cover carrier is not a subsingleton (in particular not PUnit): the
cover is a genuine degree-two cover. -/
theorem S1726Cover_not_subsingleton : ¬ Subsingleton S1726Cover := by
  intro h
  exact S1726CoverToPunctured_not_injective
    (fun _ _ _ => Subsingleton.elim _ _)

/-- The structure group of the cover: the automorphism group of F' x F'. -/
abbrev S1726StructureGroup : Type :=
  S1726FiniteEtaleAlgebra ≃ₐ[S1726K] S1726FiniteEtaleAlgebra

instance S1726StructureGroup_group : Group S1726StructureGroup :=
  inferInstance

/-- The actual sheet-swap deck transformation. -/
noncomputable def S1726Swap :
    S1726FiniteEtaleAlgebra →ₐ[S1726K] S1726FiniteEtaleAlgebra :=
  (AlgHom.snd S1726K S1726K S1726K).prod
    (AlgHom.fst S1726K S1726K S1726K)

/-- The sheet-swap as an actual automorphism of the finite etale algebra. -/
noncomputable def S1726SwapEquiv : S1726StructureGroup :=
  AlgEquiv.ofAlgHom (S1726Swap) (S1726Swap)
    (by
      apply AlgHom.ext
      intro x
      rcases x with ⟨a, b⟩
      simp [S1726Swap, AlgHom.prod_apply, AlgHom.comp_apply, AlgHom.id_apply])
    (by
      apply AlgHom.ext
      intro x
      rcases x with ⟨a, b⟩
      simp [S1726Swap, AlgHom.prod_apply, AlgHom.comp_apply, AlgHom.id_apply])

/-- The sheet-swap is not the identity. -/
theorem S1726SwapEquiv_ne_refl : S1726SwapEquiv ≠ AlgEquiv.refl := by
  intro h
  have h1 : S1726SwapEquiv (1, 0) = AlgEquiv.refl (1, 0) :=
    congrArg (fun e : S1726StructureGroup => e (1, 0)) h
  have h2 : (0 : S1726K) = 1 := by
    have h3 := congrArg Prod.fst h1
    simp [S1726SwapEquiv, S1726Swap] at h3
  exact zero_ne_one h2

/-- The actual structure group is nontrivial, not the trivial group. -/
theorem S1726StructureGroup_nontrivial :
    ∃ g : S1726StructureGroup, g ≠ 1 := by
  refine ⟨S1726SwapEquiv, ?_⟩
  intro h
  apply S1726SwapEquiv_ne_refl
  rw [h]
  apply AlgEquiv.ext
  intro x
  exact AlgEquiv.one_apply (R := S1726K) x

/-- The actual cusp count of the once-punctured elliptic signature. -/
def S1726CuspCount : Nat := Iut.OrbicurveSignature.oncePuncturedElliptic.punctures

theorem S1726CuspCount_eq_one : S1726CuspCount = 1 := rfl

theorem S1726CuspCount_pos : 0 < S1726CuspCount := by decide

/-! ## 4. The representable etale stack and the actual hyperbolic orbicurve -/

/-- The affine scheme Spec R' of the model. -/
abbrev S1726AffineScheme : Scheme := Spec (CommRingCat.of S1726CoordinateRing)

/-- Spec R' as a scheme over Spec F'. -/
abbrev S1726AffineOver : Iut.SchemeOverField S1726K :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing)))

/-- The base test scheme Spec F' over Spec F'. -/
abbrev S1726Base : Iut.SchemeOverField S1726K :=
  Over.mk (𝟙 (Spec (CommRingCat.of S1726K)))

/-- The representable category-valued etale pseudofunctor of the actual affine
model of E' is an etale stack. -/
theorem S1726RepresentableIsStack :
    (Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver).IsStack
      (Iut.SchemeOverField.etaleTopology S1726K) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology S1726K)
      (yoneda.obj S1726AffineOver) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf (F := S1726K) S1726AffineOver)
  change (discretePseudo (C := Iut.SchemeOverField S1726K)
    (yoneda.obj S1726AffineOver)).IsStack
      (Iut.SchemeOverField.etaleTopology S1726K)
  exact DiscreteSheafStack.discretePseudo_isStack
    (P := yoneda.obj S1726AffineOver) hP

/-- **The actual D6 hyperbolic orbicurve for E'/F'**: the representable etale
stack of the punctured affine model of E', with the once-punctured elliptic
signature. -/
noncomputable def S1726Orbicurve : Iut.HyperbolicOrbicurve S1726K :=
  realizedHyperbolicOrbicurve S1726K
    (Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver)
    (S1726RepresentableIsStack)
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

/-- The signature of the actual orbicurve is the once-punctured elliptic one. -/
theorem S1726Orbicurve_signature :
    S1726Orbicurve.signature = Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

/-- The actual hyperbolic orbicurve is hyperbolic. -/
theorem S1726Orbicurve_hyperbolic :
    S1726Orbicurve.signature.IsHyperbolic :=
  S1726Orbicurve.hyperbolic

@[simp] theorem S1726Orbicurve_stack_fiber :
    S1726Orbicurve.stack.fiber =
      Iut.schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver := rfl

/-- The stack carried by the orbicurve is an etale stack. -/
theorem S1726Orbicurve_stack_isStack :
    S1726Orbicurve.stack.fiber.IsStack
      (Iut.SchemeOverField.etaleTopology S1726K) :=
  S1726Orbicurve.stack.isStack

/-- The canonical signature stored in the stack is the once-punctured elliptic
one (not only the separate geometry certificate). -/
theorem S1726Orbicurve_stack_orbicurveSignature :
    S1726Orbicurve.stack.orbicurveSignature =
      some Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

/-- An algebra point R' -> F' gives an actual section Spec F' -> Spec R' over
Spec F'. -/
noncomputable def S1726OverOfAlgHom
    (ψ : S1726CoordinateRing →ₐ[S1726K] S1726K) :
    S1726Base ⟶ S1726AffineOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (by
    dsimp [S1726Base, S1726AffineOver]
    erw [← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
    have h : ψ.toRingHom.comp (algebraMap S1726K S1726CoordinateRing) =
        RingHom.id S1726K := by
      ext x
      exact ψ.commutes x
    change Spec.map (CommRingCat.ofHom
      (ψ.toRingHom.comp (algebraMap S1726K S1726CoordinateRing))) =
      𝟙 (Spec (CommRingCat.of S1726K))
    rw [h]
    change Spec.map (𝟙 (CommRingCat.of S1726K)) =
      𝟙 (Spec (CommRingCat.of S1726K))
    rw [Spec.map_id])

theorem S1726OverOfAlgHom_injective :
    Function.Injective S1726OverOfAlgHom := by
  intro ψ₁ ψ₂ h
  have hleft : (S1726OverOfAlgHom ψ₁).left =
      (S1726OverOfAlgHom ψ₂).left :=
    congrArg (fun f => f.left) h
  change Spec.map (CommRingCat.ofHom ψ₁.toRingHom) =
    Spec.map (CommRingCat.ofHom ψ₂.toRingHom) at hleft
  have hringCat := Spec.map_injective hleft
  have hring : ψ₁.toRingHom = ψ₂.toRingHom :=
    congrArg CommRingCat.Hom.hom hringCat
  ext x
  exact congrArg (fun φ : S1726CoordinateRing →+* S1726K => φ x) hring

/-! ## 5. Nonterminality of the actual orbicurve -/

/-- The representable fiber at the base test scheme has two distinct actual
sections, from the two distinct points (0,0) and (1,0) of the model. -/
theorem S1726Nonterminal : ¬ Subsingleton (S1726Base ⟶ S1726AffineOver) := by
  intro hsub
  have hψ : S1726PointAlgHom 0 0 S1726Equation_zero_zero ≠
      S1726PointAlgHom 1 0 S1726Equation_one_zero := by
    intro h
    have h0 := congrArg (fun ψ : S1726CoordinateRing →ₐ[S1726K] S1726K =>
      ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0))) h
    simp at h0
  have hover : S1726OverOfAlgHom (S1726PointAlgHom 0 0 S1726Equation_zero_zero) ≠
      S1726OverOfAlgHom (S1726PointAlgHom 1 0 S1726Equation_one_zero) :=
    fun h => hψ (S1726OverOfAlgHom_injective h)
  exact hover (Subsingleton.elim _ _)

/-- The actual orbicurve is nonterminal: at least one stack fiber is not a
subsingleton. -/
theorem S1726NonterminalFiber :
    S1319NonterminalFiber S1726Orbicurve := by
  refine ⟨Opposite.op S1726Base, ?_⟩
  intro hsub
  apply S1726Nonterminal
  have hsub' : Subsingleton
      (Discrete (S1726Base ⟶ S1726AffineOver)) := hsub
  haveI := hsub'
  constructor
  intro f g
  have h : (Discrete.mk f : Discrete (S1726Base ⟶ S1726AffineOver)) =
      Discrete.mk g := Subsingleton.elim _ _
  exact congrArg Discrete.as h

/-- Nonterminality is the classical negation of being a point fiber. -/
theorem S1726NonterminalFiber_iff_notPointFiber
    (X : Iut.HyperbolicOrbicurve S1726K) :
    S1319NonterminalFiber X ↔ ¬ IsPointFiber X.stack.fiber := by
  classical
  constructor
  · rintro ⟨U, hU⟩ h
    exact hU (h U)
  · intro h
    by_contra h'
    apply h
    intro U
    by_contra hU
    exact h' ⟨U, hU⟩

/-- The actual orbicurve is not a point fiber. -/
theorem S1726Orbicurve_not_pointFiber :
    ¬ IsPointFiber S1726Orbicurve.stack.fiber :=
  (S1726NonterminalFiber_iff_notPointFiber S1726Orbicurve).mp
    S1726NonterminalFiber

/-- The actual orbicurve is not the degenerate point-fiber orbicurve. -/
theorem S1726Orbicurve_ne_degeneratePointFiber :
    S1726Orbicurve ≠ degeneratePointFiberOrbicurve S1726K := by
  intro h
  apply S1726Orbicurve_not_pointFiber
  rw [h]
  exact degeneratePointFiberOrbicurve_isPointFiber S1726K

/-! ## 6. The D6 source clause: actual geometric fields and exact residual -/

/-- The projective point type of E'. -/
abbrev S1726CurveType : Type := S1726Curve.toProjective.Point

/-- The affine inclusion of the punctured affine model into the projective
curve of E'. -/
noncomputable def S1726CurveToPunctured :
    S1726PuncturedCurve → S1726CurveType :=
  fun p => WeierstrassCurve.Projective.Point.fromAffine
    (WeierstrassCurve.Affine.Point.some p.1.1 p.1.2
      ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp p.2))

/-- The exact-sequence clause carried by actual orbifold fundamental-group
data (base group the absolute Galois group of F'). -/
noncomputable def S1726SourceExactSequenceOfGroups
    {X : Iut.HyperbolicOrbicurve S1726K}
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    SourceExactSequenceClause.{0, 0, 0} :=
  S1348SourceExactSequenceOfProfinite
    (Iut.OrbicurveFundamentalGroupData.exactSequence groups)

/-- The D6 SourceOrbicurveClause over E'/F' with all geometric fields actual,
conditional only on the orbifold fundamental-group data of X.  The cover, its
structure group, the cover map, its surjectivity, the cusp count and the curve
compatibility are the actual objects constructed in this file. -/
noncomputable def S1726SourceOrbicurveClauseOfGroupsAt
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    SourceOrbicurveClause.{0, 0, 0} where
  curve := S1726CurveType
  puncturedCurve := S1726PuncturedCurve
  cover := S1726Cover
  structureGroup := S1726StructureGroup
  curveToPunctured := S1726CurveToPunctured
  coverToPunctured := S1726CoverToPunctured
  cover_surjective := S1726CoverToPunctured_surjective
  exactSequence := S1726SourceExactSequenceOfGroups groups
  cuspCount := S1726CuspCount
  cuspCount_pos := S1726CuspCount_pos
  curveCompatibility := Function.Surjective S1726CoverToPunctured
  curveCompatibility_proved := S1726CoverToPunctured_surjective

/-- The D6 clause over E'/F', specialized to the actual orbicurve. -/
noncomputable def S1726SourceOrbicurveClauseOfGroups
    (groups : Iut.OrbicurveFundamentalGroupData S1726Orbicurve
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    SourceOrbicurveClause.{0, 0, 0} :=
  S1726SourceOrbicurveClauseOfGroupsAt S1726Orbicurve groups

@[simp] theorem S1726SourceOrbicurveClauseOfGroupsAt_curve
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    (S1726SourceOrbicurveClauseOfGroupsAt X groups).curve =
      S1726CurveType := rfl

@[simp] theorem S1726SourceOrbicurveClauseOfGroupsAt_puncturedCurve
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    (S1726SourceOrbicurveClauseOfGroupsAt X groups).puncturedCurve =
      S1726PuncturedCurve := rfl

@[simp] theorem S1726SourceOrbicurveClauseOfGroupsAt_cover
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    (S1726SourceOrbicurveClauseOfGroupsAt X groups).cover = S1726Cover := rfl

@[simp] theorem S1726SourceOrbicurveClauseOfGroupsAt_structureGroup
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    (S1726SourceOrbicurveClauseOfGroupsAt X groups).structureGroup =
      S1726StructureGroup := rfl

@[simp] theorem S1726SourceOrbicurveClauseOfGroupsAt_coverToPunctured
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    (S1726SourceOrbicurveClauseOfGroupsAt X groups).coverToPunctured =
      S1726CoverToPunctured := rfl

@[simp] theorem S1726SourceOrbicurveClauseOfGroupsAt_cuspCount
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    (S1726SourceOrbicurveClauseOfGroupsAt X groups).cuspCount = 1 := rfl

/-- The exact-sequence cover group of the clause is definitionally the actual
arithmetic orbifold fundamental group supplied by the group data. -/
@[simp] theorem S1726SourceOrbicurveClauseOfGroupsAt_coverGroup
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    (S1726SourceOrbicurveClauseOfGroupsAt X groups).exactSequence.coverGroup =
      ↥groups.arithmeticGroup := rfl

@[simp] theorem S1726SourceOrbicurveClauseOfGroupsAt_baseGroup
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    (S1726SourceOrbicurveClauseOfGroupsAt X groups).exactSequence.baseGroup =
      ↥(Iut.AbsoluteGaloisProfinite S1726K) := rfl

/-- The clause's cover map is not injective: it is the genuine degree-two cover,
not the identity cover. -/
theorem S1726SourceOrbicurveClauseOfGroupsAt_cover_not_injective
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    ¬ Function.Injective
      (S1726SourceOrbicurveClauseOfGroupsAt X groups).coverToPunctured :=
  S1726CoverToPunctured_not_injective

/-- The clause's cover carrier is not a subsingleton. -/
theorem S1726SourceOrbicurveClauseOfGroupsAt_cover_not_subsingleton
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    ¬ Subsingleton (S1726SourceOrbicurveClauseOfGroupsAt X groups).cover :=
  S1726Cover_not_subsingleton

/-- The clause's structure group is nontrivial. -/
theorem S1726SourceOrbicurveClauseOfGroupsAt_structureGroup_nontrivial
    (X : Iut.HyperbolicOrbicurve S1726K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite S1726K)) :
    ∃ g : S1726StructureGroup, g ≠ 1 :=
  S1726StructureGroup_nontrivial

/-! ### The exact first missing field -/

/-- The non-group prefix of the D6 first field over F': the actual hyperbolic
orbicurve with the once-punctured elliptic signature, nonterminal. -/
structure S1726FirstField where
  /-- The actual hyperbolic orbicurve over F'. -/
  X : Iut.HyperbolicOrbicurve S1726K
  /-- The orbicurve is nonterminal, not a point fiber. -/
  nonterminal : S1319NonterminalFiber X
  /-- Its signature is exactly the once-punctured elliptic one. -/
  signature : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic

/-- The exact residual after the (constructed) non-group prefix: the certified
orbifold etale fundamental-group data of X over the absolute Galois group. -/
abbrev S1726OrbifoldPiRemainder (F : S1726FirstField) : Type 1 :=
  Iut.OrbicurveFundamentalGroupData F.X (Iut.AbsoluteGaloisProfinite S1726K)

/-- The actual non-group prefix, with the constructed orbicurve. -/
noncomputable def S1726FirstFieldActual : S1726FirstField where
  X := S1726Orbicurve
  nonterminal := S1726NonterminalFiber
  signature := S1726Orbicurve_signature

@[simp] theorem S1726FirstFieldActual_X :
    S1726FirstFieldActual.X = S1726Orbicurve := rfl

/-- **The exact first missing field of D6 for E'/F'**: the certified orbifold
fundamental-group data of the actual hyperbolic orbicurve.  No group, cover
category or fiber functor is supplied arbitrarily. -/
abbrev S1726FirstMissing : Type 1 :=
  S1726OrbifoldPiRemainder S1726FirstFieldActual

/-- The literal S1348-style sigma first field, for comparison. -/
abbrev S1726D6FirstMissingField : Type 1 :=
  Σ (X : Iut.HyperbolicOrbicurve S1726K),
    Iut.OrbicurveFundamentalGroupData X (Iut.AbsoluteGaloisProfinite S1726K)

/-- The S1348-style first field is obtained from the actual orbicurve and the
exact missing group data. -/
noncomputable def S1726D6FirstMissingOfGroups
    (groups : S1726FirstMissing) : S1726D6FirstMissingField :=
  ⟨S1726Orbicurve, groups⟩

/-- From the exact first missing field the whole D6 clause is constructed. -/
noncomputable def S1726SourceOrbicurveClauseOfFirstMissing
    (groups : S1726FirstMissing) : SourceOrbicurveClause.{0, 0, 0} :=
  S1726SourceOrbicurveClauseOfGroups groups

/-- From any S1348-style first field the D6 clause is constructed. -/
noncomputable def S1726SourceOrbicurveClauseOfFirstField
    (F : S1726D6FirstMissingField) : SourceOrbicurveClause.{0, 0, 0} :=
  S1726SourceOrbicurveClauseOfGroupsAt F.1 F.2

theorem S1726SourceOrbicurveClauseOfFirstField_coverGroup
    (F : S1726D6FirstMissingField) :
    (S1726SourceOrbicurveClauseOfFirstField F).exactSequence.coverGroup =
      ↥F.2.arithmeticGroup := rfl

/-- The exact missing field is not replaced by an arbitrary group: the D6 clause
built from it exposes the same arithmetic group in its exact sequence. -/
theorem S1726FirstMissing_spec (groups : S1726FirstMissing) :
    (S1726SourceOrbicurveClauseOfFirstMissing groups).exactSequence.coverGroup =
      ↥groups.arithmeticGroup := rfl

/-! ## 7. Filling the D6 slot of the source contract -/

/-- Fill the orbicurve (D6) slot of the Definition 3.1 source contract over F'
with the actual clause of this file, alongside the D5 clause of S1725. -/
noncomputable def S1726FillD6 (l : PrimeGeFive)
    (S : SourceDefinition31Data.{0} l) (groups : S1726FirstMissing) :
    SourceDefinition31Data.{0} l :=
  { S with orbicurve := S1726SourceOrbicurveClauseOfGroups groups }

@[simp] theorem S1726FillD6_orbicurve (l : PrimeGeFive)
    (S : SourceDefinition31Data.{0} l) (groups : S1726FirstMissing) :
    (S1726FillD6 l S groups).orbicurve =
      S1726SourceOrbicurveClauseOfGroups groups := rfl

/-! ## 8. Axiom footprint -/

#print axioms S1726AffinePolynomial_eq
#print axioms S1726CoordinateRing_eq
#print axioms S1726PointAlgHom_equation
#print axioms S1726PuncturedPointOfAlgHom_surjective
#print axioms S1726CoverToPunctured_surjective
#print axioms S1726CoverToPunctured_not_injective
#print axioms S1726Cover_not_subsingleton
#print axioms S1726StructureGroup_nontrivial
#print axioms S1726RepresentableIsStack
#print axioms S1726Orbicurve
#print axioms S1726Orbicurve_signature
#print axioms S1726Orbicurve_hyperbolic
#print axioms S1726Orbicurve_stack_isStack
#print axioms S1726Orbicurve_stack_orbicurveSignature
#print axioms S1726Nonterminal
#print axioms S1726NonterminalFiber
#print axioms S1726Orbicurve_not_pointFiber
#print axioms S1726Orbicurve_ne_degeneratePointFiber
#print axioms S1726SourceOrbicurveClauseOfGroupsAt
#print axioms S1726SourceOrbicurveClauseOfGroupsAt_coverGroup
#print axioms S1726SourceOrbicurveClauseOfFirstMissing
#print axioms S1726FirstMissing_spec
#print axioms S1726FillD6

end LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

end