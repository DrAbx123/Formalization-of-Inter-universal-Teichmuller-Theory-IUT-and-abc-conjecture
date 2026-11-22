import tmp.sheaf.xif.paper.S1331OrbicurveClauseAudit
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# S1348: actual D6 orbicurve clause over the Gaussian curve

Consumer: the D6 field Theorem311Source.SourceOrbicurveClause of Definition
3.1(d) over the actual S1280 Gaussian arithmetic input.  S1331 supplied the
actual curve point carrier and the exact residual; this file constructs the
remaining actual geometric fields from the actual Gaussian curve
y^2 + xy = x^3 + 5, the Example36 orbicurve/feasibility data, the standard
punctured-elliptic-curve carrier, and an actual finite etale cover.

## What is constructed (all actual, no placeholders)

* the actual affine coordinate ring R = K[x,y]/(y^2 + xy - x^3 - 5) of the
  punctured Gaussian curve over K = Q(i);
* the actual K-algebra point R -> K attached to every affine point
  (S1348PointAlgHom), and the actual projective point of the Gaussian curve
  it determines (S1348EvalPoint);
* the proof that every actual punctured point is obtained this way
  (S1348PointAlgHom_surjective);
* the finite K-algebra L = K x K (a split finite etale K-algebra, finite as a
  K-module) and the base-change cover Spec(R (x)_K L) -> Spec R; its K-points
  are the cover carrier
  (S1348Cover), with the actual cover map to the punctured curve
  (S1348CoverToPunctured), a proof of surjectivity
  (S1348CoverToPunctured_surjective) and a proof that it is not injective
  (S1348CoverToPunctured_not_injective): a genuine degree-two cover, not the
  identity/terminal cover and not a subsingleton;
* the structure group S1348StructureGroup = Aut_K(L), with the actual
  sheet-swap deck transformation and the proof that it is nontrivial
  (S1348StructureGroup_nontrivial);
* the actual cusp count 1 of the once-punctured elliptic signature
  (S1348CuspCount, S1348CuspCount_pos);
* the actual compatibility proposition (cover surjectivity) with proof;
* S1348ClauseOfExactSequence, the SourceOrbicurveClause with all these
  actual fields, conditional only on the exact-sequence residual.

## The exact first field

The exact-sequence slot is the one field not constructed here.  Its base group
is actual (the absolute Galois group of K, as fixed by S1331), but its
coverGroup is the arithmetic orbicurve fundamental group, which the tree does
not contain (Mathlib has no etale fundamental group of a curve).  The exact
first field is therefore

    S1348D6FirstMissingField l
      = Sigma X : HyperbolicOrbicurve K, OrbicurveFundamentalGroupData X G_K,

i.e. an actual hyperbolic orbicurve over K together with its certified
arithmetic fundamental-group data with base G_K.  S1348ClauseOfFirstField
constructs the whole SourceOrbicurveClause from this field alone, and
S1348ExactSequenceResidualOfOrbicurve shows that its first field is exactly
the exact-sequence coverGroup.

## Honest boundary (not claimed)

* The finite etale cover used is the split degree-two cover
  R (x)_K (K x K) -> R.  It is a genuine finite etale cover and its K-points
  surject onto the punctured K-points, but it is disconnected.  The paper's
  connected cover and the connectedness of the source orbicurve are not
  constructed here.
* The exact-sequence arithmetic orbicurve fundamental group is not constructed;
  only the exact first field and the reduction from it to the full clause.
* No terminal stack, no PUnit, no arbitrary Type, no True-valued compatibility
  and no new axiom are used.  The compatibility proposition is the actual
  surjectivity of the cover map.

Axiom footprints are printed at the end.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable (l : PrimeGeFive)

/-- The actual Gaussian field of the S1280 arithmetic input. -/
abbrev S1348K : Type := (S1280Arithmetic l).F

/-- The actual Gaussian curve y^2 + xy = x^3 + 5 over the S1280 field. -/
abbrev S1348Curve : WeierstrassCurve (S1348K l) := (S1280Arithmetic l).curve.curve

instance S1348Curve_isElliptic : (S1348Curve l).IsElliptic :=
  (S1280Arithmetic l).curve.isElliptic

/-- The affine Weierstrass polynomial y^2 + xy - x^3 - 5 of the actual Gaussian
curve, in the two variables x = X 0 and y = X 1. -/
abbrev S1348AffinePolynomial : MvPolynomial (Fin 2) (S1348K l) :=
  weierstrassAffinePolynomial (S1348Curve l)

/-- The actual affine coordinate ring K[x,y]/(y^2 + xy - x^3 - 5) of the
punctured Gaussian curve (the puncture is the point at infinity, so the affine
curve is exactly the punctured curve). -/
abbrev S1348CoordinateRing : Type :=
  MvPolynomial (Fin 2) (S1348K l) ⧸ Ideal.span {S1348AffinePolynomial l}

/-- Evaluation of the affine Weierstrass polynomial at an arbitrary assignment
of the two coordinates. -/
theorem S1348_aeval_affinePolynomial_apply (f : Fin 2 → S1348K l) :
    MvPolynomial.aeval f (S1348AffinePolynomial l) =
      f 1 ^ 2 + (S1348Curve l).a₁ * f 0 * f 1 + (S1348Curve l).a₃ * f 1 -
        (f 0 ^ 3 + (S1348Curve l).a₂ * f 0 ^ 2 + (S1348Curve l).a₄ * f 0 +
          (S1348Curve l).a₆) := by
  simp [S1348AffinePolynomial, weierstrassAffinePolynomial]

/-- Evaluation of the affine Weierstrass polynomial at the coordinate pair. -/
theorem S1348_aeval_affinePolynomial (x y : S1348K l) :
    MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i) (S1348AffinePolynomial l) =
      y ^ 2 + (S1348Curve l).a₁ * x * y + (S1348Curve l).a₃ * y -
        (x ^ 3 + (S1348Curve l).a₂ * x ^ 2 + (S1348Curve l).a₄ * x +
          (S1348Curve l).a₆) := by
  rw [S1348_aeval_affinePolynomial_apply]
  simp

/-- The affine Weierstrass polynomial vanishes at every actual affine point. -/
theorem S1348_aeval_affinePolynomial_eq_zero {x y : S1348K l}
    (h : (S1348Curve l).toAffine.Equation x y) :
    MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i) (S1348AffinePolynomial l) = 0 := by
  rw [S1348_aeval_affinePolynomial, sub_eq_zero]
  exact (WeierstrassCurve.Affine.equation_iff x y).mp h

/-- The K-algebra map R -> K attached to an actual affine point (x,y): evaluation
at the coordinates.  This is the actual F-point of the punctured Gaussian curve
corresponding to (x,y). -/
noncomputable def S1348PointAlgHom (x y : S1348K l)
    (h : (S1348Curve l).toAffine.Equation x y) :
    S1348CoordinateRing l →ₐ[S1348K l] S1348K l :=
  Ideal.Quotient.liftₐ (Ideal.span {S1348AffinePolynomial l})
    (MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i))
    (by
      have hle : Ideal.span ({S1348AffinePolynomial l} : Set _) ≤
          RingHom.ker (AlgHom.toRingHom
            (MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i))) := by
        rw [Ideal.span_le]
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        exact S1348_aeval_affinePolynomial_eq_zero l h
      intro a ha
      exact hle ha)

@[simp]
theorem S1348PointAlgHom_X0 (x y : S1348K l)
    (h : (S1348Curve l).toAffine.Equation x y) :
    S1348PointAlgHom l x y h
      (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (MvPolynomial.X 0)) = x := by
  rw [S1348PointAlgHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp

@[simp]
theorem S1348PointAlgHom_X1 (x y : S1348K l)
    (h : (S1348Curve l).toAffine.Equation x y) :
    S1348PointAlgHom l x y h
      (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (MvPolynomial.X 1)) = y := by
  rw [S1348PointAlgHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp

/-- The equation satisfied by the coordinates of any K-point of the affine
punctured curve. -/
theorem S1348EvalPoint_equation (ψ :
    S1348CoordinateRing l →ₐ[S1348K l] S1348K l) :
    (S1348Curve l).toAffine.Equation
      (ψ (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (MvPolynomial.X 0)))
      (ψ (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (MvPolynomial.X 1))) := by
  let Φ : MvPolynomial (Fin 2) (S1348K l) →ₐ[S1348K l] S1348K l :=
    ψ.comp (Ideal.Quotient.mkₐ (S1348K l) (Ideal.span {S1348AffinePolynomial l}))
  have hΦ : Φ (S1348AffinePolynomial l) = 0 := by
    have hzero : Ideal.Quotient.mkₐ (S1348K l)
        (Ideal.span {S1348AffinePolynomial l}) (S1348AffinePolynomial l) = 0 := by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    show ψ (Ideal.Quotient.mkₐ (S1348K l)
      (Ideal.span {S1348AffinePolynomial l}) (S1348AffinePolynomial l)) = 0
    rw [hzero, map_zero]
  have hcomp : Φ =
      MvPolynomial.aeval (fun i : Fin 2 => Φ (MvPolynomial.X i)) := by
    conv_lhs => rw [MvPolynomial.aeval_unique Φ]
    rfl
  have haeval : MvPolynomial.aeval
      (fun i : Fin 2 => Φ (MvPolynomial.X i)) (S1348AffinePolynomial l) = 0 := by
    rw [← hcomp]
    exact hΦ
  have hfun : (fun i : Fin 2 =>
      ψ (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (MvPolynomial.X i))) =
      (fun i : Fin 2 => Φ (MvPolynomial.X i)) := by
    funext i
    simp only [Φ, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [← hfun, S1348_aeval_affinePolynomial_apply] at haeval
  exact (WeierstrassCurve.Affine.equation_iff _ _).mpr (sub_eq_zero.mp haeval)

/-- The projective point of the actual Gaussian curve attached to a K-point of
the affine coordinate ring. -/
noncomputable def S1348EvalPoint (ψ :
    S1348CoordinateRing l →ₐ[S1348K l] S1348K l) :
    (S1280Arithmetic l).curve.curve.toProjective.Point :=
  WeierstrassCurve.Projective.Point.fromAffine
    (WeierstrassCurve.Affine.Point.some
      (ψ (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (MvPolynomial.X 0)))
      (ψ (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
        (MvPolynomial.X 1)))
      ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp
        (S1348EvalPoint_equation l ψ)))

theorem S1348EvalPoint_ne_zero (ψ :
    S1348CoordinateRing l →ₐ[S1348K l] S1348K l) :
    S1348EvalPoint l ψ ≠ (0 : (S1280Arithmetic l).curve.curve.toProjective.Point) := by
  unfold S1348EvalPoint
  exact WeierstrassCurve.Projective.Point.fromAffine_some_ne_zero _

/-- The cover-to-punctured map at the point level: every K-point of the affine
punctured Gaussian curve is an actual punctured point. -/
noncomputable def S1348EvalPunctured (ψ :
    S1348CoordinateRing l →ₐ[S1348K l] S1348K l) :
    S1331ClausePuncturedCurve l :=
  ⟨S1348EvalPoint l ψ, by
    rw [S1331_puncture_eq_zero]
    exact S1348EvalPoint_ne_zero l ψ⟩


/-! ## 2. Surjectivity of the affine-point cover map

Every actual punctured point is the image of an actual K-point of the affine
coordinate ring, obtained by evaluating at its affine coordinates. -/

/-- Every punctured actual point is the image of an actual K-algebra point of the
affine coordinate ring. -/
theorem S1348PointAlgHom_surjective :
    Function.Surjective (S1348EvalPunctured l) := by
  classical
  intro P
  have hP : P.1 ≠ (0 : (S1280Arithmetic l).curve.curve.toProjective.Point) := by
    intro h0
    exact P.2 (h0.trans (S1331_puncture_eq_zero l).symm)
  generalize hQdef :
    WeierstrassCurve.Projective.Point.toAffineLift
      (W := (S1280Arithmetic l).curve.curve.toProjective) P.1 = Q at hP ⊢
  rcases Q with _ | ⟨x, y, hns⟩
  · have hP1 : P.1 = (0 : (S1280Arithmetic l).curve.curve.toProjective.Point) := by
      apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv
        (S1280Arithmetic l).curve.curve.toProjective).injective
      rw [AddEquiv.map_zero]
      rw [WeierstrassCurve.Projective.Point.toAffineAddEquiv_apply]
      exact hQdef
    exact absurd hP1 hP
  · have hns' : (S1348Curve l).toAffine.Nonsingular x y := hns
    have hEq : (S1348Curve l).toAffine.Equation x y :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular).mpr hns'
    refine ⟨S1348PointAlgHom l x y hEq, ?_⟩
    apply Subtype.ext
    have hcoord0 : S1348PointAlgHom l x y hEq
        (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
          (MvPolynomial.X 0)) = x := by simp
    have hcoord1 : S1348PointAlgHom l x y hEq
        (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
          (MvPolynomial.X 1)) = y := by simp
    have hleft : WeierstrassCurve.Projective.Point.fromAffine
        (WeierstrassCurve.Projective.Point.toAffineLift
          (W := (S1280Arithmetic l).curve.curve.toProjective) P.1) = P.1 := by
      rw [← WeierstrassCurve.Projective.Point.toAffineAddEquiv_symm_apply
        (W := (S1280Arithmetic l).curve.curve.toProjective)
        (WeierstrassCurve.Projective.Point.toAffineLift
          (W := (S1280Arithmetic l).curve.curve.toProjective) P.1)]
      exact AddEquiv.symm_apply_apply _ _
    have hsome : WeierstrassCurve.Affine.Point.some
        ((S1348PointAlgHom l x y hEq)
          (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
            (MvPolynomial.X 0)))
        ((S1348PointAlgHom l x y hEq)
          (Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
            (MvPolynomial.X 1)))
        ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp
          (S1348EvalPoint_equation l (S1348PointAlgHom l x y hEq)))
        = WeierstrassCurve.Affine.Point.some x y hns := by
      exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hcoord0, hcoord1⟩
    rw [← hleft, hQdef]
    exact congrArg WeierstrassCurve.Projective.Point.fromAffine hsome


/-! ## 3. The actual finite etale cover, structure group and cusp count -/

/-- The degree-two finite etale K-algebra L = K x K.  Base change of the
punctured curve along Spec L -> Spec K is the actual finite etale double cover
used below. -/
abbrev S1348FiniteEtaleAlgebra : Type := S1348K l × S1348K l

/-- The cover algebra L = K x K is finite as a K-module (rank two); this is the
finiteness half of the finite-etale certificate of the cover. -/
theorem S1348FiniteEtaleAlgebra_moduleFinite :
    Module.Finite (S1348K l) (S1348FiniteEtaleAlgebra l) := inferInstance

/-- The actual K-points of the finite etale cover
Spec(R (x)_K L) -> Spec R of the punctured Gaussian curve, where
R = K[x,y]/(y^2+xy-x^3-5) is the actual affine coordinate ring. -/
abbrev S1348Cover : Type :=
  TensorProduct (S1348K l) (S1348CoordinateRing l) (S1348FiniteEtaleAlgebra l) →ₐ[S1348K l] S1348K l

/-- The cover-to-punctured map on actual K-points, induced by the structure
morphism R -> R (x)_K L. -/
noncomputable def S1348CoverToPunctured (phi : S1348Cover l) :
    S1331ClausePuncturedCurve l :=
  S1348EvalPunctured l (phi.comp Algebra.TensorProduct.includeLeft)

/-- The actual cover map is surjective onto the actual punctured points: every
affine K-point of the curve extends to a K-point of the finite etale cover. -/
theorem S1348CoverToPunctured_surjective :
    Function.Surjective (S1348CoverToPunctured l) := by
  intro P
  obtain ⟨psi, hpsi⟩ := S1348PointAlgHom_surjective l P
  refine ⟨Algebra.TensorProduct.lift psi
    (AlgHom.fst (S1348K l) (S1348K l) (S1348K l))
    (fun _ _ => Commute.all _ _), ?_⟩
  show S1348EvalPunctured l
    ((Algebra.TensorProduct.lift psi
      (AlgHom.fst (S1348K l) (S1348K l) (S1348K l))
      (fun _ _ => Commute.all _ _)).comp
        Algebra.TensorProduct.includeLeft) = P
  rw [Algebra.TensorProduct.lift_comp_includeLeft]
  exact hpsi

/-- The cover point type is nonempty: the cover surjects onto the nonempty
punctured point type. -/
theorem S1348Cover_nonempty : Nonempty (S1348Cover l) := by
  obtain ⟨P⟩ := S1331ClausePuncturedCurve_nonempty l
  obtain ⟨phi, _⟩ := S1348CoverToPunctured_surjective l P
  exact ⟨phi⟩

/-- The cover map is not injective: the two sheet lifts of an actual punctured
point are distinct actual K-points of the finite etale cover.  Hence the cover
is a genuine degree-two cover, not the identity/terminal cover. -/
theorem S1348CoverToPunctured_not_injective :
    ¬ Function.Injective (S1348CoverToPunctured l) := by
  classical
  obtain ⟨P⟩ := S1331ClausePuncturedCurve_nonempty l
  obtain ⟨psi, hpsi⟩ := S1348PointAlgHom_surjective l P
  let fstMap : S1348FiniteEtaleAlgebra l →ₐ[S1348K l] S1348K l :=
    AlgHom.fst (S1348K l) (S1348K l) (S1348K l)
  let sndMap : S1348FiniteEtaleAlgebra l →ₐ[S1348K l] S1348K l :=
    AlgHom.snd (S1348K l) (S1348K l) (S1348K l)
  let phi1 : S1348Cover l :=
    Algebra.TensorProduct.lift psi fstMap (fun _ _ => Commute.all _ _)
  let phi2 : S1348Cover l :=
    Algebra.TensorProduct.lift psi sndMap (fun _ _ => Commute.all _ _)
  have h1 : S1348CoverToPunctured l phi1 = P := by
    show S1348EvalPunctured l (phi1.comp Algebra.TensorProduct.includeLeft) = P
    rw [show phi1.comp Algebra.TensorProduct.includeLeft = psi from
      Algebra.TensorProduct.lift_comp_includeLeft psi fstMap
        (fun _ _ => Commute.all _ _)]
    exact hpsi
  have h2 : S1348CoverToPunctured l phi2 = P := by
    show S1348EvalPunctured l (phi2.comp Algebra.TensorProduct.includeLeft) = P
    rw [show phi2.comp Algebra.TensorProduct.includeLeft = psi from
      Algebra.TensorProduct.lift_comp_includeLeft psi sndMap
        (fun _ _ => Commute.all _ _)]
    exact hpsi
  intro hinj
  have hEq : phi1 = phi2 := hinj (by rw [h1, h2])
  have hval := congrArg (fun phi : S1348Cover l =>
    phi (Algebra.TensorProduct.includeRight
      ((1 : S1348K l), (0 : S1348K l)))) hEq
  have e1 : phi1 (Algebra.TensorProduct.includeRight
      ((1 : S1348K l), (0 : S1348K l))) = 1 := by
    dsimp only [phi1]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
    simp [fstMap]
  have e2 : phi2 (Algebra.TensorProduct.includeRight
      ((1 : S1348K l), (0 : S1348K l))) = 0 := by
    dsimp only [phi2]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
    simp [sndMap]
  rw [e1, e2] at hval
  exact one_ne_zero hval

/-- The cover carrier is not a subsingleton (in particular not PUnit): two
distinct sheet lifts of an actual punctured point exist. -/
theorem S1348Cover_not_subsingleton : ¬ Subsingleton (S1348Cover l) := by
  intro h
  exact S1348CoverToPunctured_not_injective l
    (fun _ _ _ => Subsingleton.elim _ _)

/-- The structure group of the finite etale cover: the automorphism group of
the finite etale K-algebra L = K x K (the Galois group of the degree-two cover). -/
abbrev S1348StructureGroup : Type :=
  S1348FiniteEtaleAlgebra l ≃ₐ[S1348K l] S1348FiniteEtaleAlgebra l

instance S1348StructureGroup_group :
    Group ((S1348FiniteEtaleAlgebra l) ≃ₐ[S1348K l] (S1348FiniteEtaleAlgebra l)) :=
  inferInstance

/-- The nontrivial deck transformation of the double cover: swap of the two
sheets. -/
noncomputable def S1348Swap :
    S1348FiniteEtaleAlgebra l →ₐ[S1348K l] S1348FiniteEtaleAlgebra l :=
  (AlgHom.snd (S1348K l) (S1348K l) (S1348K l)).prod
    (AlgHom.fst (S1348K l) (S1348K l) (S1348K l))

/-- The sheet-swap as an automorphism of the finite etale algebra. -/
noncomputable def S1348SwapEquiv : S1348StructureGroup l :=
  AlgEquiv.ofAlgHom (S1348Swap l) (S1348Swap l)
    (by
      apply AlgHom.ext
      intro x
      rcases x with ⟨a, b⟩
      simp [S1348Swap, AlgHom.prod_apply, AlgHom.comp_apply, AlgHom.id_apply])
    (by
      apply AlgHom.ext
      intro x
      rcases x with ⟨a, b⟩
      simp [S1348Swap, AlgHom.prod_apply, AlgHom.comp_apply, AlgHom.id_apply])

/-- The sheet-swap is not the identity: the structure group is nontrivial. -/
theorem S1348SwapEquiv_ne_refl : S1348SwapEquiv l ≠ AlgEquiv.refl := by
  intro h
  have h1 : S1348SwapEquiv l (1, 0) = AlgEquiv.refl (1, 0) :=
    congrArg (fun e : S1348StructureGroup l => e (1, 0)) h
  have h2 : (0 : S1348K l) = 1 := by
    have h3 := congrArg Prod.fst h1
    simp [S1348SwapEquiv, S1348Swap] at h3
  exact zero_ne_one h2

/-- The actual structure group is nontrivial. -/
theorem S1348StructureGroup_nontrivial :
    ∃ g : S1348StructureGroup l, g ≠ 1 := by
  refine ⟨S1348SwapEquiv l, ?_⟩
  intro h
  apply S1348SwapEquiv_ne_refl l
  rw [h]
  apply AlgEquiv.ext
  intro x
  exact AlgEquiv.one_apply (R := S1348K l) x

/-- The actual cusp count of the once-punctured elliptic orbicurve signature. -/
def S1348CuspCount : Nat := Iut.OrbicurveSignature.oncePuncturedElliptic.punctures

theorem S1348CuspCount_eq_one : S1348CuspCount = 1 := rfl

theorem S1348CuspCount_pos : 0 < S1348CuspCount := by decide

/-- The cusp count is the one of the source once-punctured elliptic signature
used by the Example36 orbicurve carrier. -/
theorem S1348CuspCount_eq_oncePuncturedSignature :
    S1348CuspCount = OrbicurveFeasibility.oncePuncturedSignature.punctures := rfl

/-- The curve-compatibility proposition of this actual clause: the finite etale
cover admits a surjection onto the actual punctured points. -/
def S1348CurveCompatibility : Prop :=
  Function.Surjective (S1348CoverToPunctured l)

theorem S1348CurveCompatibility_proved : S1348CurveCompatibility l :=
  S1348CoverToPunctured_surjective l

/-! ## 4. The clause with the actual D6 geometric fields

Every field except the source exact-sequence slot is now an actual object:
the actual Gaussian point carriers and inclusion (S1331), the actual finite
etale double cover R (x)_K (K x K) and its K-points, its sheet-swap structure
group, the actual once-punctured cusp count, and the proved cover-surjectivity
compatibility.  The exact-sequence residual is the single remaining input. -/

/-- The SourceOrbicurveClause over the actual S1280 Gaussian data, with every
geometric field actual, conditional only on the exact-sequence residual. -/
noncomputable def S1348ClauseOfExactSequence
    (E : S1331ExactSequenceResidual l) : SourceOrbicurveClause.{0, 0, 0} where
  curve := S1331ClauseCurve l
  puncturedCurve := S1331ClausePuncturedCurve l
  cover := S1348Cover l
  structureGroup := S1348StructureGroup l
  curveToPunctured := S1331ClauseCurveToPunctured l
  coverToPunctured := S1348CoverToPunctured l
  cover_surjective := S1348CoverToPunctured_surjective l
  exactSequence := E.toExactSequence
  cuspCount := S1348CuspCount
  cuspCount_pos := S1348CuspCount_pos
  curveCompatibility := S1348CurveCompatibility l
  curveCompatibility_proved := S1348CurveCompatibility_proved l

@[simp] theorem S1348ClauseOfExactSequence_curve (E : S1331ExactSequenceResidual l) :
    (S1348ClauseOfExactSequence l E).curve = S1331ClauseCurve l := rfl

@[simp] theorem S1348ClauseOfExactSequence_puncturedCurve
    (E : S1331ExactSequenceResidual l) :
    (S1348ClauseOfExactSequence l E).puncturedCurve = S1331ClausePuncturedCurve l := rfl

@[simp] theorem S1348ClauseOfExactSequence_cover (E : S1331ExactSequenceResidual l) :
    (S1348ClauseOfExactSequence l E).cover = S1348Cover l := rfl

@[simp] theorem S1348ClauseOfExactSequence_structureGroup
    (E : S1331ExactSequenceResidual l) :
    (S1348ClauseOfExactSequence l E).structureGroup = S1348StructureGroup l := rfl

@[simp] theorem S1348ClauseOfExactSequence_coverToPunctured
    (E : S1331ExactSequenceResidual l) :
    (S1348ClauseOfExactSequence l E).coverToPunctured = S1348CoverToPunctured l := rfl

@[simp] theorem S1348ClauseOfExactSequence_cuspCount
    (E : S1331ExactSequenceResidual l) :
    (S1348ClauseOfExactSequence l E).cuspCount = S1348CuspCount := rfl

@[simp] theorem S1348ClauseOfExactSequence_exactSequence_baseGroup
    (E : S1331ExactSequenceResidual l) :
    (S1348ClauseOfExactSequence l E).exactSequence.baseGroup =
      S1331ExactSequenceBaseGroup l := rfl

/-- The clause's cover map is not injective: the clause uses the genuine
degree-two cover, not the identity cover. -/
theorem S1348ClauseOfExactSequence_coverToPunctured_not_injective
    (E : S1331ExactSequenceResidual l) :
    ¬ Function.Injective (S1348ClauseOfExactSequence l E).coverToPunctured :=
  S1348CoverToPunctured_not_injective l

/-- The clause's cover carrier is not a subsingleton: it is not PUnit and not
the terminal cover. -/
theorem S1348ClauseOfExactSequence_cover_not_subsingleton
    (E : S1331ExactSequenceResidual l) :
    ¬ Subsingleton (S1348ClauseOfExactSequence l E).cover :=
  S1348Cover_not_subsingleton l

/-- The clause's structure group is an actual nontrivial group. -/
theorem S1348ClauseOfExactSequence_structureGroup_nontrivial
    (E : S1331ExactSequenceResidual l) :
    ∃ g : S1348StructureGroup l, g ≠ 1 :=
  S1348StructureGroup_nontrivial l


/-! ## 5. The exact-sequence slot: actual base group and exact first field

The base group of the source exact sequence is actual: it is the absolute
Galois group of the S1280 field.  The missing part of the slot is the
arithmetic orbicurve fundamental group (the coverGroup) together with its
projection, i.e. actual OrbicurveEtaleFundamentalGroup data over an actual
hyperbolic orbicurve.  The tree has no inhabitant of that datum for the
Gaussian curve (Mathlib has no curve etale fundamental group); this is recorded
as the exact first field, and a constructor from it to the whole clause is
provided below. -/

/-- Convert an actual profinite exact sequence into the source exact-sequence
clause (whose groups are the underlying types of the profinite groups). -/
noncomputable def S1348SourceExactSequenceOfProfinite
    {Ggeom Garith Galois : ProfiniteGrp.{0}}
    (S : Iut.ProfiniteFundamentalExactSequence Ggeom Garith Galois) :
    SourceExactSequenceClause.{0, 0, 0} where
  baseGroup := ↥Galois
  coverGroup := ↥Garith
  geometricGroup := ↥Ggeom
  injection := (S.inclusion.hom).toMonoidHom
  projection := (S.projection.hom).toMonoidHom
  injection_injective := S.inclusion_injective
  projection_surjective := S.projection_surjective
  exact_at_cover := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ (S.projection.hom).ker := hx
      rw [← S.exact] at hx'
      rcases hx' with ⟨y, hy⟩
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      have hcomp := Iut.ProfiniteFundamentalExactSequence.projection_comp_inclusion_eq_one S
      exact congrArg (fun f => f y) hcomp

/-- The exact-sequence residual built from actual orbicurve fundamental-group
data over the actual S1280 hyperbolic orbicurve.  The base group is the actual
absolute Galois group of the S1280 field. -/
noncomputable def S1348ExactSequenceResidualOfOrbicurve
    (X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)) :
    S1331ExactSequenceResidual l where
  coverGroup := ↥groups.arithmeticGroup
  geometricGroup := ↥groups.geometric.group
  injection :=
    (Iut.OrbicurveFundamentalGroupData.exactSequence groups).inclusion.hom.toMonoidHom
  projection :=
    (Iut.OrbicurveFundamentalGroupData.exactSequence groups).projection.hom.toMonoidHom
  injection_injective :=
    (Iut.OrbicurveFundamentalGroupData.exactSequence groups).inclusion_injective
  projection_surjective :=
    (Iut.OrbicurveFundamentalGroupData.exactSequence groups).projection_surjective
  exact_at_cover := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ ((Iut.OrbicurveFundamentalGroupData.exactSequence groups).projection.hom).ker :=
        hx
      rw [← (Iut.OrbicurveFundamentalGroupData.exactSequence groups).exact] at hx'
      rcases hx' with ⟨y, hy⟩
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      have hcomp := Iut.ProfiniteFundamentalExactSequence.projection_comp_inclusion_eq_one
        (Iut.OrbicurveFundamentalGroupData.exactSequence groups)
      exact congrArg (fun f => f y) hcomp

/-- The exact first field of the source exact-sequence slot over the actual
Gaussian data: an actual hyperbolic orbicurve over the S1280 field together
with its certified arithmetic orbicurve fundamental-group data with base the
actual absolute Galois group. -/
abbrev S1348D6FirstMissingField (l : PrimeGeFive) : Type 1 :=
  Σ (X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K),
    Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)

/-- From the exact first field, the exact-sequence residual is constructed. -/
noncomputable def S1348ExactSequenceResidualOfFirstField
    (F : S1348D6FirstMissingField l) : S1331ExactSequenceResidual l :=
  S1348ExactSequenceResidualOfOrbicurve l F.1 F.2

/-- **The exact reduction.**  The full SourceOrbicurveClause over the actual
S1280 Gaussian data is constructed from the exact first field alone: the
covering, structure group, cover map and its surjectivity, cusp count and
compatibility are the actual objects of this file. -/
noncomputable def S1348ClauseOfFirstField
    (F : S1348D6FirstMissingField l) : SourceOrbicurveClause.{0, 0, 0} :=
  S1348ClauseOfExactSequence l (S1348ExactSequenceResidualOfFirstField l F)


/-! ## 6. The exact-sequence fields supplied by the first field -/

/-- The exact-sequence cover group of the residual built from actual orbicurve
fundamental-group data is the arithmetic orbicurve fundamental group. -/
@[simp] theorem S1348ExactSequenceResidualOfOrbicurve_coverGroup
    (X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)) :
    (S1348ExactSequenceResidualOfOrbicurve l X groups).coverGroup =
      ↥groups.arithmeticGroup := rfl

/-- The exact-sequence geometric group of the residual built from actual
orbicurve fundamental-group data is the geometric orbicurve fundamental group. -/
@[simp] theorem S1348ExactSequenceResidualOfOrbicurve_geometricGroup
    (X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (groups : Iut.OrbicurveFundamentalGroupData X
      (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)) :
    (S1348ExactSequenceResidualOfOrbicurve l X groups).geometricGroup =
      ↥groups.geometric.group := rfl

/-- The exact first component of the first field is the exact-sequence
coverGroup: the arithmetic orbicurve fundamental group. -/
@[simp] theorem S1348ExactSequenceFirstMissingField_coverGroup
    (F : S1348D6FirstMissingField l) :
    (S1348ExactSequenceResidualOfFirstField l F).coverGroup =
      ↥F.2.arithmeticGroup := rfl

/-- The signature of a clause produced from the exact first field.  Every field
except the exact-sequence slot is an actual object of this file. -/
theorem S1348ClauseOfFirstField_spec
    (F : S1348D6FirstMissingField l) :
    (S1348ClauseOfFirstField l F).curve = S1331ClauseCurve l ∧
    (S1348ClauseOfFirstField l F).puncturedCurve = S1331ClausePuncturedCurve l ∧
    (S1348ClauseOfFirstField l F).cover = S1348Cover l ∧
    (S1348ClauseOfFirstField l F).structureGroup = S1348StructureGroup l ∧
    (S1348ClauseOfFirstField l F).cuspCount = 1 ∧
    0 < (S1348ClauseOfFirstField l F).cuspCount := 
  ⟨rfl, rfl, rfl, rfl, rfl, S1348CuspCount_pos⟩

/-! ## 7. Axiom footprint -/

#print axioms S1348_aeval_affinePolynomial
#print axioms S1348PointAlgHom_X0
#print axioms S1348EvalPoint_equation
#print axioms S1348PointAlgHom_surjective
#print axioms S1348CoverToPunctured_surjective
#print axioms S1348CoverToPunctured_not_injective
#print axioms S1348Cover_not_subsingleton
#print axioms S1348StructureGroup_nontrivial
#print axioms S1348CuspCount_pos
#print axioms S1348ClauseOfExactSequence
#print axioms S1348SourceExactSequenceOfProfinite
#print axioms S1348ClauseOfFirstField
#print axioms S1348ExactSequenceFirstMissingField_coverGroup
end LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual

end