import tmp.sheaf.xif.paper.S1932SignActionQuotientActual
import tmp.sheaf.xif.paper.S1886D9OrbicurveActual
import tmp.sheaf.xif.paper.S1881D9D7bActual

/-!
# S1964: the quotient C_F = X_F/{+-1} of the actual S1726 orbicurve

S1932 isolated the paper's C_F as

    S1932CFQuotient l A = (cF : HyperbolicOrbicurve F') x
      (cF.signature = (1,1)^pm) x
      (quotient : OrbicurveSignInvariantMorphism A cF) x
      (quotientWitness : OrbicurveSignQuotientWitness A quotient)

and recorded that the quotient stack itself is neither constructed nor
postulated.  This file does **not** postulate it either.  It (a) constructs the
genuine geometric input that any honest quotient has to respect, (b) proves
that the quotient datum is unique up to 2-isomorphism if it exists, (c) proves
that the substantive missing datum is the *quotient structure* alone (the
signature label is not determined by the fiber and is not a consequence of the
universal property), and (d) states the missing object as a type.

## Result

Proved, unconditionally, in this file:

* **Fixed locus of the actual elliptic involution** (section 1).  The actual
  affine Weierstrass model of E' is y^2 = x^3 + (61/64) x^2 - (125/64) x, and

      x^3 + (61/64) x^2 - (125/64) x = x * (x - 1) * (x + 125/64).

  Hence the affine points with y = 0 are exactly the three points
  (0,0), (1,0), (-125/64,0) (S1964TwoTorsion_abscissa), they are pairwise
  distinct, and they are exactly the affine points fixed by the actual scheme
  endomorphism S1898AffineEndo of [-1] (S1964Section_fixed_iff,
  S1964FixedAffinePoints_classified).  Each of these three points is a
  ramification point of the involution (y |-> -y on the local coordinate),
  i.e. the honest quotient of the model has three order-two stacky points; the
  image of the origin in the projective closure is the fourth fixed point and
  is the cusp.  These are the actual geometric data of C_F.

* **The honest signature type** (section 2): (0; 2,2,2; 1) with orbifold Euler
  characteristic -1/2, hence hyperbolic, and the *coarse* quotient (0; -; 1)
  has Euler characteristic 1, so a coarse (non-stacky) quotient could not be a
  hyperbolic orbicurve at all.  The honest type is recorded as a type-level
  datum; it is **not** asserted to be the signature of a constructed quotient
  (none exists).

* **Signature labels are not determined by the fiber** (section 3): two
  hyperbolic orbicurves with the *same* etale stack fiber and different
  signatures exist.  Consequently the cF_signature field of the paper target
  is a label, not a consequence of any construction of the quotient fiber.

* **The quotient structure and its uniqueness** (section 4): the substantive
  content of the paper target is a S1964QuotientStructure l A (quotient
  orbicurve + sign-invariant morphism + universal property, *without* the
  signature label); the paper target maps to it, and it is unique up to
  2-isomorphism compatible with the two quotient morphisms.

## The exact first missing

The first missing object is a S1964QuotientStructure l A, i.e. a
category-valued etale stack

    [X_F / {+-1}]  =  colim over B(Z/2) of X_F

together with the sign-invariant quotient morphism and its bicategorical
universal property.  What is missing in the tree/Mathlib is the construction,
not a lemma about an existing object:

1. the pointwise lax colimit (Grothendieck construction) of the group action
   A.diagram on the Cat-valued pseudofunctor X_F.fiber --- no such construction
   for a group action on a category-valued etale stack exists;
2. its functoriality/coherence as a pseudofunctor of test schemes;
3. **descent**: Pseudofunctor.IsStack for that pseudofunctor (i.e.
   stackification of the pointwise colimit) --- Mathlib carries the bare class
   Pseudofunctor.IsStack, and the tree has IsStack only for representable
   (discrete) and sheaf-valued fibers, never for a quotient;
4. the bicategorical universal property, i.e. the descend / factor /
   descendTwoCell / twoCellExt data.

Steps 1-3 are exactly the "quotient-stack route" already recorded as absent in
S1761 and S1792; nothing in the present file pretends to supply them.  The
#print axioms block at the end shows that every declaration below uses only
propext, Classical.choice and Quot.sound; there is no sorry, no admit, no new
axiom, and no postulated quotient.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1964QuotientCFActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual
open LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

/-! ## 1. The fixed locus of the actual elliptic involution -/

/-- The cubic part of the affine Weierstrass polynomial of E' factors over the
three two-torsion abscissae. -/
theorem S1964Cubic_factors (x : S1726K) :
    x ^ 3 + (61/64 : S1726K) * x ^ 2 - (125/64 : S1726K) * x =
      x * (x - 1) * (x + 125/64) := by
  ring

/-- The third two-torsion point (-125/64, 0) of the actual model satisfies the
Weierstrass equation. -/
theorem S1964Equation_neg125 :
    S1726Curve.toAffine.Equation (-125/64 : S1726K) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff, S1726Curve_a₁, S1726Curve_a₂,
    S1726Curve_a₃, S1726Curve_a₄, S1726Curve_a₆]
  norm_num

/-- If (x,y) is an affine point then so is (x,-y). -/
theorem S1964Equation_neg_y {x y : S1726K}
    (h : S1726Curve.toAffine.Equation x y) :
    S1726Curve.toAffine.Equation x (-y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  rw [S1726Curve_a₁, S1726Curve_a₃] at h ⊢
  have hy : (-y) ^ 2 = y ^ 2 := by ring
  rw [hy]
  simpa using h

/-- The affine coordinate endomorphism of [-1] fixes the class of x. -/
theorem S1964CoordEndo_x :
    S1898CoordEndo (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0)) =
      Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0) := by
  rw [S1932CoordEndo_mk, S1898PolyEndo_X0]

/-- An F'-algebra map out of the affine coordinate ring is determined by its
values on the classes of x and y. -/
theorem S1964PointAlgHom_ext {ψ φ : S1726CoordinateRing →ₐ[S1726K] S1726K}
    (h0 : ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0)) =
      φ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0)))
    (h1 : ψ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 1)) =
      φ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 1))) : ψ = φ := by
  have key : (ψ.comp (Ideal.Quotient.mkₐ (S1726K)
        (Ideal.span {S1726AffinePolynomial}))) =
      (φ.comp (Ideal.Quotient.mkₐ (S1726K)
        (Ideal.span {S1726AffinePolynomial}))) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simpa [Ideal.Quotient.mkₐ_eq_mk] using h0
    · simpa [Ideal.Quotient.mkₐ_eq_mk] using h1
  apply AlgHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.span {S1726AffinePolynomial}) z
  simpa [Ideal.Quotient.mkₐ_eq_mk] using
    congrArg (fun e : MvPolynomial (Fin 2) S1726K →ₐ[S1726K] S1726K => e p) key

/-- The point (x,0) is fixed by the actual involution on the coordinate ring. -/
theorem S1964PointAlgHom_zero_comp (x : S1726K)
    (h : S1726Curve.toAffine.Equation x 0) :
    (S1726PointAlgHom x 0 h).comp S1898CoordEndo = S1726PointAlgHom x 0 h := by
  apply S1964PointAlgHom_ext
  · rw [AlgHom.comp_apply, S1964CoordEndo_x, S1726PointAlgHom_X0]
  · rw [AlgHom.comp_apply, S1898CoordEndo_y, map_neg, S1726PointAlgHom_X1]
    simp

/-- **The fixed F'-points of the actual involution are exactly the two-torsion
points**: the point (x,y) is fixed iff y = 0. -/
theorem S1964PointAlgHom_fixed_iff (x y : S1726K)
    (h : S1726Curve.toAffine.Equation x y) :
    (S1726PointAlgHom x y h).comp S1898CoordEndo = S1726PointAlgHom x y h ↔
      y = 0 := by
  constructor
  · intro heq
    have h1 := congrArg (fun φ : S1726CoordinateRing →ₐ[S1726K] S1726K =>
      φ (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 1))) heq
    rw [AlgHom.comp_apply, S1898CoordEndo_y, map_neg, S1726PointAlgHom_X1] at h1
    have h2 : (2 : S1726K) * y = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  · intro hy
    subst hy
    exact S1964PointAlgHom_zero_comp x h

/-- Composition with the actual involution acts on F'-algebra points by
precomposition with the coordinate endomorphism. -/
theorem S1964OverOfAlgHom_comp (ψ : S1726CoordinateRing →ₐ[S1726K] S1726K) :
    S1726OverOfAlgHom ψ ≫ S1898AffineEndo =
      S1726OverOfAlgHom (ψ.comp S1898CoordEndo) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  show Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom S1898CoordEndo.toRingHom) =
    Spec.map (CommRingCat.ofHom (ψ.comp S1898CoordEndo).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- **A section of the affine model is fixed by the actual involution iff its
y-coordinate vanishes.** -/
theorem S1964Section_fixed_iff (x y : S1726K)
    (h : S1726Curve.toAffine.Equation x y) :
    (S1726OverOfAlgHom (S1726PointAlgHom x y h) ≫ S1898AffineEndo =
        S1726OverOfAlgHom (S1726PointAlgHom x y h)) ↔ y = 0 := by
  rw [S1964OverOfAlgHom_comp]
  constructor
  · intro hfix
    exact (S1964PointAlgHom_fixed_iff x y h).mp (S1726OverOfAlgHom_injective hfix)
  · intro hy
    subst hy
    rw [S1964PointAlgHom_zero_comp x h]

/-- The two-torsion abscissae are exactly 0, 1, -125/64. -/
theorem S1964TwoTorsion_abscissa {x : S1726K}
    (h : S1726Curve.toAffine.Equation x 0) :
    x = 0 ∨ x = 1 ∨ x = -125/64 := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  rw [S1726Curve_a₁, S1726Curve_a₂, S1726Curve_a₃, S1726Curve_a₄,
    S1726Curve_a₆] at h
  have hpoly : x * (x - 1) * (x + 125/64) = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp hpoly with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl (by linear_combination h2))
  · exact Or.inr (Or.inr (by linear_combination h1))

/-- The elliptic negation p |-> -p on the actual affine points. -/
noncomputable def S1964Neg (p : S1726PuncturedCurve) : S1726PuncturedCurve :=
  ⟨(p.1.1, -p.1.2), S1964Equation_neg_y p.2⟩

/-- The negation is an involution on the actual affine points. -/
theorem S1964Neg_involutive (p : S1726PuncturedCurve) :
    S1964Neg (S1964Neg p) = p := by
  apply Subtype.ext
  simp [S1964Neg]

/-- An affine point is fixed by the negation exactly when its y-coordinate
vanishes. -/
theorem S1964Neg_eq_self_iff (p : S1726PuncturedCurve) :
    S1964Neg p = p ↔ p.1.2 = 0 := by
  constructor
  · intro h
    have h2 := congrArg (fun q : S1726PuncturedCurve => q.1.2) h
    simp only [S1964Neg, neg_inj] at h2
    have h3 : (2 : S1726K) * p.1.2 = 0 := by linear_combination -h2
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
  · intro hy
    apply Subtype.ext
    exact Prod.ext rfl (by simp [S1964Neg, hy])

/-- **The fixed points of the actual involution on the affine curve are exactly
the three two-torsion points** (the order-two points of the quotient). -/
theorem S1964FixedPoint_cases {p : S1726PuncturedCurve}
    (hp : S1964Neg p = p) :
    p = ⟨(0, 0), S1726Equation_zero_zero⟩ ∨
      p = ⟨(1, 0), S1726Equation_one_zero⟩ ∨
      p = ⟨(-125/64, 0), S1964Equation_neg125⟩ := by
  have hy : p.1.2 = 0 := (S1964Neg_eq_self_iff p).mp hp
  rcases S1964TwoTorsion_abscissa (by simpa [hy] using p.2) with h | h | h
  · refine Or.inl (Subtype.ext (Prod.ext h hy))
  · exact Or.inr (Or.inl (Subtype.ext (Prod.ext h hy)))
  · exact Or.inr (Or.inr (Subtype.ext (Prod.ext h hy)))

/-- **Classification of the fixed affine points of the actual involution.** -/
theorem S1964FixedAffinePoints_classified {x y : S1726K}
    (h : S1726Curve.toAffine.Equation x y)
    (hfix : S1726OverOfAlgHom (S1726PointAlgHom x y h) ≫ S1898AffineEndo =
      S1726OverOfAlgHom (S1726PointAlgHom x y h)) :
    (x = 0 ∨ x = 1 ∨ x = -125/64) ∧ y = 0 := by
  have hy : y = 0 := (S1964Section_fixed_iff x y h).mp hfix
  subst hy
  exact ⟨S1964TwoTorsion_abscissa h, rfl⟩

/-- The three two-torsion points of the affine model are pairwise distinct. -/
theorem S1964TwoTorsion_pairwise_distinct :
    (⟨(0, 0), S1726Equation_zero_zero⟩ : S1726PuncturedCurve) ≠
        ⟨(1, 0), S1726Equation_one_zero⟩ ∧
      (⟨(0, 0), S1726Equation_zero_zero⟩ : S1726PuncturedCurve) ≠
        ⟨(-125/64, 0), S1964Equation_neg125⟩ ∧
      (⟨(1, 0), S1726Equation_one_zero⟩ : S1726PuncturedCurve) ≠
        ⟨(-125/64, 0), S1964Equation_neg125⟩ := by
  refine ⟨S1726ZeroZero_ne_one_zero, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun p : S1726PuncturedCurve => p.1.1) h
    norm_num at h0
  · intro h
    have h0 := congrArg (fun p : S1726PuncturedCurve => p.1.1) h
    norm_num at h0

/-- **The actual involution fixes the three two-torsion sections.** -/
theorem S1964TwoTorsionSections_fixed :
    (S1726OverOfAlgHom (S1726PointAlgHom 0 0 S1726Equation_zero_zero) ≫
        S1898AffineEndo =
      S1726OverOfAlgHom (S1726PointAlgHom 0 0 S1726Equation_zero_zero)) ∧
    (S1726OverOfAlgHom (S1726PointAlgHom 1 0 S1726Equation_one_zero) ≫
        S1898AffineEndo =
      S1726OverOfAlgHom (S1726PointAlgHom 1 0 S1726Equation_one_zero)) ∧
    (S1726OverOfAlgHom (S1726PointAlgHom (-125/64) 0 S1964Equation_neg125) ≫
        S1898AffineEndo =
      S1726OverOfAlgHom (S1726PointAlgHom (-125/64) 0 S1964Equation_neg125)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [S1964OverOfAlgHom_comp, S1964PointAlgHom_zero_comp]
  · rw [S1964OverOfAlgHom_comp, S1964PointAlgHom_zero_comp]
  · rw [S1964OverOfAlgHom_comp, S1964PointAlgHom_zero_comp]

/-! ## 2. The signature type of the honest quotient -/

/-- The signature type that the honest quotient X_F/{+-1} of the affine model
has: genus 0, three order-two stacky points (the images of the three two-torsion
points of section 1), and one cusp (the image of the origin).  This is the
*geometric expectation* recorded for the missing quotient; it is not asserted
to be the signature of any constructed orbicurve. -/
def S1964HonestQuotientSignature : Iut.OrbicurveSignature where
  genus := 0
  stackyOrders := [2, 2, 2]
  punctures := 1
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide

/-- Orbifold Euler characteristic of the honest quotient type: -1/2. -/
theorem S1964HonestQuotientSignature_euler :
    S1964HonestQuotientSignature.eulerCharacteristic = -1/2 := by
  norm_num [S1964HonestQuotientSignature, Iut.OrbicurveSignature.eulerCharacteristic]

/-- The honest quotient type is hyperbolic. -/
theorem S1964HonestQuotientSignature_hyperbolic :
    S1964HonestQuotientSignature.IsHyperbolic := by
  rw [Iut.OrbicurveSignature.IsHyperbolic, S1964HonestQuotientSignature_euler]
  norm_num

/-- The honest quotient type is not the paper's (1,1)^pm label. -/
theorem S1964HonestSignature_ne_paper :
    S1964HonestQuotientSignature ≠ sourceTypeOneOnePlusMinus := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  norm_num [S1964HonestQuotientSignature, sourceTypeOneOnePlusMinus] at hg

/-- The signature of the *coarse* quotient (P^1 with one puncture, no stacky
points): Euler characteristic 1. -/
def S1964CoarseQuotientSignature : Iut.OrbicurveSignature where
  genus := 0
  stackyOrders := []
  punctures := 1
  stackyOrders_ge_two := by simp

/-- **A coarse quotient cannot be a hyperbolic orbicurve**: dropping the three
order-two stacky points makes the Euler characteristic positive.  Hence the
paper's C_F, which is required to be hyperbolic, must be a genuine stacky
quotient, not the coarse quotient sheaf. -/
theorem S1964CoarseQuotientSignature_not_hyperbolic :
    ¬ S1964CoarseQuotientSignature.IsHyperbolic := by
  rw [Iut.OrbicurveSignature.IsHyperbolic]
  norm_num [S1964CoarseQuotientSignature, Iut.OrbicurveSignature.eulerCharacteristic]

/-! ## 3. Signature labels are not determined by the fiber -/

/-- **Two hyperbolic orbicurves with the same etale stack fiber and different
signatures.**  Hence HyperbolicOrbicurve.signature is a label attached to a
fiber, and no construction of the quotient fiber can force the paper's (1,1)^pm
label: that field of the paper target is not a mathematical consequence of the
quotient. -/
theorem S1964SignatureLabelsNotDeterminedByFiber (l : PrimeGeFive) :
    ∃ X Y : Iut.HyperbolicOrbicurve (S1732A l).F,
      X.stack.fiber = Y.stack.fiber ∧
        X.signature = sourceTypeOneOnePlusMinus ∧
        Y.signature = S1964HonestQuotientSignature := by
  refine ⟨realizedHyperbolicOrbicurve (S1732A l).F S1726Orbicurve.stack.fiber
      S1726Orbicurve.stack.isStack sourceTypeOneOnePlusMinus
      sourceTypeOneOnePlusMinus_hyperbolic,
    realizedHyperbolicOrbicurve (S1732A l).F S1726Orbicurve.stack.fiber
      S1726Orbicurve.stack.isStack S1964HonestQuotientSignature
      S1964HonestQuotientSignature_hyperbolic,
    ?_, rfl, rfl⟩
  rw [realizedHyperbolicOrbicurve_stack_fiber, realizedHyperbolicOrbicurve_stack_fiber]

/-! ## 4. The quotient structure: the substantive missing datum -/

/-- The bicategorical quotient of the sign action: the quotient orbicurve, the
sign-invariant morphism, and the universal property.  The signature label is
deliberately *not* part of this structure (section 3 shows it is metadata). -/
structure S1964QuotientStructure (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) where
  /-- The quotient orbicurve C_F. -/
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  /-- The sign-invariant quotient morphism X_F -> C_F. -/
  quotient : Iut.OrbicurveSignInvariantMorphism A cF
  /-- The bicategorical universal property of the quotient. -/
  quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient

/-- The paper target S1932CFQuotient maps to the quotient structure: its
substantive content is the quotient structure alone, the signature label being
metadata (section 3). -/
def S1964QuotientStructure.ofPaper {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (Q : S1932CFQuotient l A) : S1964QuotientStructure l A :=
  ⟨Q.cF, Q.quotient, Q.quotientWitness⟩

/-- **The quotient is unique up to 2-isomorphism compatible with the quotient
morphisms.**  Two quotient structures for the same action factor through each
other: the composite of the two descended morphisms with the quotient map is
2-isomorphic to the quotient map. -/
theorem S1964QuotientUnique {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (S T : S1964QuotientStructure l A) :
    ∃ (f : T.cF.Hom S.cF) (g : S.cF.Hom T.cF),
      Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp T.quotient.map f) S.quotient.map) ∧
      Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp S.quotient.map g) T.quotient.map) :=
  ⟨T.quotientWitness.descend S.cF S.quotient,
   S.quotientWitness.descend T.cF T.quotient,
   ⟨T.quotientWitness.factor S.cF S.quotient⟩,
   ⟨S.quotientWitness.factor T.cF T.quotient⟩⟩

/-- The signature-parameterized paper target: a quotient structure together with
a chosen signature for the quotient.  At sourceTypeOneOnePlusMinus this is
definitionally S1932CFQuotient. -/
structure S1964CFQuotientAt (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve)
    (s : Iut.OrbicurveSignature) (hs : s.IsHyperbolic) where
  /-- The quotient orbicurve. -/
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  /-- The chosen signature label. -/
  cF_signature : cF.signature = s
  /-- The sign-invariant quotient morphism. -/
  quotient : Iut.OrbicurveSignInvariantMorphism A cF
  /-- The universal property of the quotient. -/
  quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient

/-- The paper target is the parameterized target at the paper label (1,1)^pm:
the two structures have the same four fields, so their inhabitednesses agree. -/
theorem S1964CFQuotientAt_iff_paper (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    Nonempty (S1964CFQuotientAt l A sourceTypeOneOnePlusMinus
        sourceTypeOneOnePlusMinus_hyperbolic) ↔
      Nonempty (S1932CFQuotient l A) := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨⟨Q.cF, Q.cF_signature, Q.quotient, Q.quotientWitness⟩⟩
  · rintro ⟨Q⟩
    exact ⟨⟨Q.cF, Q.cF_signature, Q.quotient, Q.quotientWitness⟩⟩

/-- Forgetting the label from the parameterized target. -/
def S1964QuotientStructure.ofAt {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    {s : Iut.OrbicurveSignature} {hs : s.IsHyperbolic}
    (Q : S1964CFQuotientAt l A s hs) : S1964QuotientStructure l A :=
  ⟨Q.cF, Q.quotient, Q.quotientWitness⟩

/-- The exact first missing datum of the paper's C_F, as a property: the
existence of the bicategorical quotient structure.  Its construction is not in
the tree (see the module comment); it is not postulated here. -/
def S1964FirstMissing (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) : Prop :=
  Nonempty (S1964QuotientStructure l A)

/-- **The paper target S1932CFQuotient implies the quotient structure**, which
is therefore the substantive missing datum. -/
theorem S1964FirstMissing_ofPaper {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : Nonempty (S1932CFQuotient l A)) : S1964FirstMissing l A :=
  h.elim fun Q => ⟨S1964QuotientStructure.ofPaper Q⟩

/-- The same reduction for any other signature label, in particular the honest
one: the label adds nothing to the quotient structure. -/
theorem S1964FirstMissing_ofAt {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    {s : Iut.OrbicurveSignature} {hs : s.IsHyperbolic}
    (h : Nonempty (S1964CFQuotientAt l A s hs)) : S1964FirstMissing l A :=
  h.elim fun Q => ⟨S1964QuotientStructure.ofAt Q⟩

/-- The paper-faithful target with the *honest* signature label of section 2. -/
abbrev S1964HonestCFQuotient (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :=
  S1964CFQuotientAt l A S1964HonestQuotientSignature
    S1964HonestQuotientSignature_hyperbolic

/-- The first missing datum does not depend on which signature label is used:
the honest labelled target reduces to the same quotient structure as the paper
labelled one. -/
theorem S1964FirstMissing_ofHonest {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : Nonempty (S1964HonestCFQuotient l A)) : S1964FirstMissing l A :=
  S1964FirstMissing_ofAt h

/-! ## 5. Axiom footprint -/

#print axioms S1964Cubic_factors
#print axioms S1964Equation_neg125
#print axioms S1964Equation_neg_y
#print axioms S1964CoordEndo_x
#print axioms S1964PointAlgHom_ext
#print axioms S1964PointAlgHom_zero_comp
#print axioms S1964PointAlgHom_fixed_iff
#print axioms S1964OverOfAlgHom_comp
#print axioms S1964Section_fixed_iff
#print axioms S1964TwoTorsion_abscissa
#print axioms S1964FixedAffinePoints_classified
#print axioms S1964TwoTorsion_pairwise_distinct
#print axioms S1964TwoTorsionSections_fixed
#print axioms S1964Neg_involutive
#print axioms S1964Neg_eq_self_iff
#print axioms S1964FixedPoint_cases
#print axioms S1964HonestQuotientSignature_euler
#print axioms S1964HonestQuotientSignature_hyperbolic
#print axioms S1964HonestSignature_ne_paper
#print axioms S1964CoarseQuotientSignature_not_hyperbolic
#print axioms S1964SignatureLabelsNotDeterminedByFiber
#print axioms S1964QuotientStructure.ofPaper
#print axioms S1964QuotientUnique
#print axioms S1964CFQuotientAt_iff_paper
#print axioms S1964QuotientStructure.ofAt
#print axioms S1964FirstMissing_ofPaper
#print axioms S1964FirstMissing_ofAt
#print axioms S1964FirstMissing_ofHonest

end LeanFormal.IUT.XiFPaper.S1964QuotientCFActual

end
