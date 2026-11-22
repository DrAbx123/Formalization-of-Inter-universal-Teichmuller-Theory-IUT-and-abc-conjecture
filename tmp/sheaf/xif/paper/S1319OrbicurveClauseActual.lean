import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
# S1319: the actual D6 boundary clause from the concrete Gaussian curve

S1280 constructs the actual D3/D4 prefix of Definition 3.1 over the concrete
Gaussian arithmetic input.  S1298 isolates the D5 torsion basis.  This file
constructs the actual point-level boundary clause for D6 (Definition 3.1(d),
the hyperbolic orbicurve C_K = X_K/(+-1)) and freezes the remaining stack and
fundamental-group gap.

## What is constructed here (actual, not terminal)

The concrete curve is the base change to Q(i) of

  E : y^2 + xy = x^3 + 5.

The file constructs, from actual data only:

* the actual projective point set of E over Q(i);
* the actual punctured point set (projective points different from the
  recorded origin/puncture);
* an explicit nonzero point (1,2), proved nonsingular and different from
  the puncture, hence the punctured point set is nonempty;
* the actual sign involution P |-> -P and the setoid of its orbits;
* the actual coarse quotient curve X_K/(+-1), its punctured quotient, and
  the quotient map from the punctured curve to its quotient;
* the actual quotient map is surjective, and it is nondegenerate: the
  distinct points (1,2) and -(1,2) have the same image, so the cover is
  not the identity/terminal cover;
* the actual sign invariance of the quotient map (the curve compatibility);
* the actual structure group SignGroup = +-1;
* the actual once-punctured cusp count 1;
* the actual profinite exact sequence attached to the l-torsion Galois
  representation of the concrete curve:
    1 -> ker(rho_l) -> G_{Q(i)} -> rho_l(G_{Q(i)}) -> 1.

These fields are assembled into a genuine SourceOrbicurveClause.

## Exact boundary

This is not the terminal constant stack of
SourceDefinition31OrbicurveInstance, and not the identity cover.  The
cover map constructed here has a genuinely nontrivial fibre.  However, the
clause is the boundary clause record, not the full D6 stack object: it
does not encode the coherent sign action, the stack quotient, or certified
etale fundamental groups.  The cover map is the coarse quotient map of the
sign action, not a scheme-level finite-etale morphism; the finite-etale and
stack refinements are part of the exact gap.  In particular the exactSequence slot is the
actual l-torsion representation sequence; it is a real exact sequence of
the actual curve, but it is not claimed to be the orbifold fundamental-group
sequence 1 -> Delta_C -> Pi_C -> G_K -> 1.  That sequence, together with the
nonterminal stack orbicurve and its certified fundamental groups, is the
exact remaining D6 gap, frozen below as S1319OrbifoldPiGap.

No PUnit, True, arbitrary cover, terminal stack, identity cover, axiom or
sorry is used.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

local instance s1319GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1319FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The actual curve and its points -/

abbrev S1319CurveWeierstrass (l : PrimeGeFive) :
    WeierstrassCurve (S1280Arithmetic l).F :=
  (S1280Arithmetic l).curve.curve

abbrev S1319CurvePoints (l : PrimeGeFive) : Type :=
  (S1319CurveWeierstrass l).toProjective.Point

abbrev S1319PuncturedPoints (l : PrimeGeFive) : Type :=
  {P : S1319CurvePoints l // P ≠ (S1280Arithmetic l).curve.puncture}

def S1319CurveToPunctured (l : PrimeGeFive) :
    S1319PuncturedPoints l → S1319CurvePoints l :=
  Subtype.val

theorem S1319CurveToPunctured_injective (l : PrimeGeFive) :
    Function.Injective (S1319CurveToPunctured l) :=
  Subtype.coe_injective

def S1319QAffinePoint : concreteSplitCurve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 1 2 (by
    rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]
    constructor
    · norm_num [concreteSplitCurve]
    · left
      norm_num [concreteSplitCurve])

def S1319QProjectivePoint : concreteSplitCurve.toProjective.Point :=
  WeierstrassCurve.Projective.Point.fromAffine S1319QAffinePoint

theorem S1319QProjectivePoint_point :
    S1319QProjectivePoint.point = ⟦![1, 2, 1]⟧ := by
  simp [S1319QProjectivePoint, S1319QAffinePoint,
    WeierstrassCurve.Projective.Point.fromAffine_some,
    WeierstrassCurve.Projective.Point.mk_point]

def S1319GaussianPoint (l : PrimeGeFive) : S1319CurvePoints l :=
  PuncturedEllipticCurve.projectivePointMap (algebraMap ℚ (S1280Arithmetic l).F)
    concreteSplitCurve S1319QProjectivePoint

theorem S1319GaussianPoint_point (l : PrimeGeFive) :
    (S1319GaussianPoint l).point = ⟦![1, 2, 1]⟧ := by
  rw [S1319GaussianPoint, PuncturedEllipticCurve.projectivePointMap_point,
    S1319QProjectivePoint_point,
    PuncturedEllipticCurve.projectivePointClassMap_mk]
  congr 1
  funext i
  fin_cases i <;>
    simp only [Function.comp_apply, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    rfl

theorem S1319CurveWeierstrass_a1 (l : PrimeGeFive) :
    (S1319CurveWeierstrass l).a₁ = (1 : (S1280Arithmetic l).F) := by
  rw [S1319CurveWeierstrass, concreteGaussianInitialThetaArithmeticData_curve,
    PuncturedEllipticCurve.baseChange_curve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_a₁]
  exact map_one _

theorem S1319CurveWeierstrass_a3 (l : PrimeGeFive) :
    (S1319CurveWeierstrass l).a₃ = (0 : (S1280Arithmetic l).F) := by
  rw [S1319CurveWeierstrass, concreteGaussianInitialThetaArithmeticData_curve,
    PuncturedEllipticCurve.baseChange_curve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_a₃]
  exact map_zero _

theorem S1319GaussianPoint_neg_vector (l : PrimeGeFive) :
    (S1319CurveWeierstrass l).toProjective.neg ![1, 2, 1] = ![1, -3, 1] := by
  ext i
  fin_cases i <;>
    simp [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY,
      S1319CurveWeierstrass_a1, S1319CurveWeierstrass_a3] <;>
    norm_num

theorem S1319_puncture_point (l : PrimeGeFive) :
    ((S1280Arithmetic l).curve.puncture).point = (⟦![0, 1, 0]⟧ :
      WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) := by
  rw [concreteGaussianInitialThetaArithmeticData_curve]
  simp only [PuncturedEllipticCurve.baseChange, PuncturedEllipticCurve.map,
    concreteSplitPuncturedCurve]
  rw [PuncturedEllipticCurve.projectivePointMap_point,
    PuncturedEllipticCurve.projectivePointClassMap_mk]
  change Quotient.mk _ (fun i : Fin 3 =>
    (algebraMap ℚ (S1280Arithmetic l).F) (![0, 1, 0] i)) =
      Quotient.mk _ ![0, 1, 0]
  congr 1
  funext i
  fin_cases i <;> simp

theorem S1319_puncture_eq_zero (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.puncture = 0 := by
  apply WeierstrassCurve.Projective.Point.ext
  rw [S1319_puncture_point, WeierstrassCurve.Projective.Point.zero_point]

theorem S1319GaussianPoint_ne_puncture (l : PrimeGeFive) :
    S1319GaussianPoint l ≠ (S1280Arithmetic l).curve.puncture := by
  intro h
  have hp := congrArg (fun P => P.point) h
  rw [S1319GaussianPoint_point, S1319_puncture_point] at hp
  have hne : (⟦![1, 2, 1]⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F)
      ≠ ⟦![0, 1, 0]⟧ := by
    intro heq
    exact WeierstrassCurve.Projective.not_equiv_of_Y_ne
      (P := ![1, 2, 1]) (Q := ![0, 1, 0]) (by simp) (Quotient.exact heq)
  exact hne hp

theorem S1319GaussianPoint_ne_neg (l : PrimeGeFive) :
    S1319GaussianPoint l ≠ -S1319GaussianPoint l := by
  intro h
  have hp := congrArg (fun P => P.point) h
  have hneg : (-S1319GaussianPoint l).point = (⟦![1, -3, 1]⟧ :
      WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) := by
    rw [WeierstrassCurve.Projective.Point.neg_point, S1319GaussianPoint_point,
      WeierstrassCurve.Projective.negMap_eq, S1319GaussianPoint_neg_vector]
  rw [S1319GaussianPoint_point, hneg] at hp
  have hne : (⟦![1, 2, 1]⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F)
      ≠ ⟦![1, -3, 1]⟧ := by
    intro heq
    refine WeierstrassCurve.Projective.not_equiv_of_Y_ne
      (P := ![1, 2, 1]) (Q := ![1, -3, 1]) ?_ (Quotient.exact heq)
    simp only [Matrix.cons_val_two]
    norm_num
  exact hne hp

theorem S1319_puncture_nonempty (l : PrimeGeFive) :
    Nonempty (S1319PuncturedPoints l) :=
  ⟨⟨S1319GaussianPoint l, S1319GaussianPoint_ne_puncture l⟩⟩

/-! ## 2. The sign quotient C_K = X_K/(+-1) -/

def S1319SignSetoid (l : PrimeGeFive) : Setoid (S1319CurvePoints l) where
  r P Q := Q = P ∨ Q = -P
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro P
      exact Or.inl rfl
    · rintro P Q (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    · rintro P Q R (h | h) (h' | h')
      · exact Or.inl (h'.trans h)
      · exact Or.inr (by rw [h', h])
      · exact Or.inr (by rw [h', h])
      · exact Or.inl (by rw [h', h, neg_neg])

abbrev S1319Curve (l : PrimeGeFive) : Type :=
  Quotient (S1319SignSetoid l)

def S1319PunctureClass (l : PrimeGeFive) : S1319Curve l :=
  Quotient.mk (S1319SignSetoid l) (S1280Arithmetic l).curve.puncture

abbrev S1319PuncturedCurve (l : PrimeGeFive) : Type :=
  {x : S1319Curve l // x ≠ S1319PunctureClass l}

def S1319CurveQuotientToPunctured (l : PrimeGeFive) :
    S1319PuncturedCurve l → S1319Curve l :=
  Subtype.val

theorem S1319CurveQuotientToPunctured_injective (l : PrimeGeFive) :
    Function.Injective (S1319CurveQuotientToPunctured l) :=
  Subtype.coe_injective

theorem S1319_neg_puncture_eq (l : PrimeGeFive) :
    -(S1280Arithmetic l).curve.puncture = (S1280Arithmetic l).curve.puncture := by
  rw [S1319_puncture_eq_zero, neg_zero]

theorem S1319_neg_ne_puncture (l : PrimeGeFive) {P : S1319CurvePoints l}
    (hP : P ≠ (S1280Arithmetic l).curve.puncture) :
    -P ≠ (S1280Arithmetic l).curve.puncture := by
  intro h
  apply hP
  have h1 : -(-P) = -(S1280Arithmetic l).curve.puncture := congrArg Neg.neg h
  have h2 : -(-P) = P := neg_neg P
  have h' : P = -(S1280Arithmetic l).curve.puncture := h2.symm.trans h1
  rw [S1319_neg_puncture_eq] at h'
  exact h'

def S1319CoverToPunctured (l : PrimeGeFive) :
    S1319PuncturedPoints l → S1319PuncturedCurve l :=
  fun P => ⟨Quotient.mk (S1319SignSetoid l) P.1, by
    intro h
    have hrel := Quotient.exact h
    have hP : P.1 = (S1280Arithmetic l).curve.puncture := by
      rcases hrel with h' | h'
      · exact h'.symm
      · have h2 : -((S1280Arithmetic l).curve.puncture) = P.1 :=
          (congrArg Neg.neg h').trans (neg_neg P.1)
        rw [S1319_neg_puncture_eq] at h2
        exact h2.symm
    exact P.2 hP⟩

theorem S1319CoverToPunctured_surjective (l : PrimeGeFive) :
    Function.Surjective (S1319CoverToPunctured l) := by
  rintro ⟨x, hx⟩
  obtain ⟨P, rfl⟩ := Quot.exists_rep x
  have hP : P ≠ (S1280Arithmetic l).curve.puncture := by
    intro h
    apply hx
    rw [h]
    rfl
  refine ⟨⟨P, hP⟩, ?_⟩
  apply Subtype.ext
  rfl

def S1319SignInvariant (l : PrimeGeFive) : Prop :=
  ∀ P : S1319PuncturedPoints l,
    S1319CoverToPunctured l ⟨-P.1, S1319_neg_ne_puncture l P.2⟩ =
      S1319CoverToPunctured l P

theorem S1319SignInvariant_proved (l : PrimeGeFive) :
    S1319SignInvariant l := by
  intro P
  apply Subtype.ext
  apply Quotient.sound
  exact Or.inr (neg_neg P.1).symm

theorem S1319CoverToPunctured_nondegenerate (l : PrimeGeFive) :
    ∃ x y : S1319PuncturedPoints l, x ≠ y ∧
      S1319CoverToPunctured l x = S1319CoverToPunctured l y := by
  refine ⟨⟨S1319GaussianPoint l, S1319GaussianPoint_ne_puncture l⟩,
    ⟨-S1319GaussianPoint l,
      S1319_neg_ne_puncture l (S1319GaussianPoint_ne_puncture l)⟩, ?_, ?_⟩
  · intro h
    exact S1319GaussianPoint_ne_neg l (congrArg Subtype.val h)
  · apply Subtype.ext
    apply Quotient.sound
    exact Or.inr rfl

theorem S1319CoverToPunctured_not_injective (l : PrimeGeFive) :
    ¬ Function.Injective (S1319CoverToPunctured l) := by
  intro hinj
  obtain ⟨x, y, hxy, hEq⟩ := S1319CoverToPunctured_nondegenerate l
  exact hxy (hinj hEq)

/-! ## 3. The actual l-torsion exact sequence -/

def S1319LTorsionRepresentation (l : PrimeGeFive) :
    SourceAbsoluteGalois (S1280Arithmetic l) →*
      LinearMap.GeneralLinearGroup (ZMod l.value)
        ((S1280Arithmetic l).curve.LTorsion l) :=
  (S1280Arithmetic l).curve.galoisActionOnLTorsionGeneralLinearRepresentation l

noncomputable def S1319LTorsionExactSequence (l : PrimeGeFive) :
    SourceExactSequenceClause.{0, 0, 0} where
  baseGroup := (S1319LTorsionRepresentation l).range
  coverGroup := SourceAbsoluteGalois (S1280Arithmetic l)
  geometricGroup := (S1319LTorsionRepresentation l).ker
  baseGroupLaw := inferInstance
  coverGroupLaw := inferInstance
  geometricGroupLaw := inferInstance
  injection := (S1319LTorsionRepresentation l).ker.subtype
  projection := (S1319LTorsionRepresentation l).rangeRestrict
  injection_injective := Subtype.coe_injective
  projection_surjective := (S1319LTorsionRepresentation l).rangeRestrict_surjective
  exact_at_cover := by
    intro x
    constructor
    · intro hx
      have hx' : S1319LTorsionRepresentation l x = 1 := by
        have h := congrArg Subtype.val hx
        simpa only [MonoidHom.coe_rangeRestrict, OneMemClass.coe_one] using h
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      rw [MonoidHom.coe_rangeRestrict]
      exact y.property

/-! ## 4. The actual D6 boundary clause -/

def S1319CuspCount : Nat :=
  Iut.OrbicurveSignature.oncePuncturedElliptic.punctures

theorem S1319CuspCount_eq_oncePuncturedSignature :
    S1319CuspCount = Iut.OrbicurveSignature.oncePuncturedElliptic.punctures := rfl

theorem S1319CuspCount_eq_one : S1319CuspCount = 1 := rfl

theorem S1319CuspCount_pos : 0 < S1319CuspCount := by
  decide

noncomputable def S1319SourceOrbicurveClauseOfExactSequence (l : PrimeGeFive)
    (E : SourceExactSequenceClause.{0, 0, 0}) :
    SourceOrbicurveClause.{0, 0, 0} where
  curve := S1319Curve l
  puncturedCurve := S1319PuncturedCurve l
  cover := S1319PuncturedPoints l
  structureGroup := Iut.SignGroup
  structureGroupLaw := inferInstance
  curveToPunctured := S1319CurveQuotientToPunctured l
  coverToPunctured := S1319CoverToPunctured l
  cover_surjective := S1319CoverToPunctured_surjective l
  exactSequence := E
  cuspCount := S1319CuspCount
  cuspCount_pos := S1319CuspCount_pos
  curveCompatibility := S1319SignInvariant l
  curveCompatibility_proved := S1319SignInvariant_proved l

/-- The actual D6 boundary clause, instantiating the exact-sequence slot with
the actual l-torsion representation sequence. -/
noncomputable def S1319SourceOrbicurveClause (l : PrimeGeFive) :
    SourceOrbicurveClause.{0, 0, 0} :=
  S1319SourceOrbicurveClauseOfExactSequence l (S1319LTorsionExactSequence l)

@[simp] theorem S1319SourceOrbicurveClauseOfExactSequence_exactSequence
    (l : PrimeGeFive) (E : SourceExactSequenceClause.{0, 0, 0}) :
    (S1319SourceOrbicurveClauseOfExactSequence l E).exactSequence = E := rfl

@[simp] theorem S1319SourceOrbicurveClause_curve (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).curve = S1319Curve l := rfl

@[simp] theorem S1319SourceOrbicurveClause_puncturedCurve (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).puncturedCurve = S1319PuncturedCurve l := rfl

@[simp] theorem S1319SourceOrbicurveClause_cover (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).cover = S1319PuncturedPoints l := rfl

@[simp] theorem S1319SourceOrbicurveClause_structureGroup (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).structureGroup = Iut.SignGroup := rfl

@[simp] theorem S1319SourceOrbicurveClause_curveToPunctured (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).curveToPunctured =
      S1319CurveQuotientToPunctured l := rfl

@[simp] theorem S1319SourceOrbicurveClause_coverToPunctured (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).coverToPunctured =
      S1319CoverToPunctured l := rfl

@[simp] theorem S1319SourceOrbicurveClause_cover_surjective (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).cover_surjective =
      S1319CoverToPunctured_surjective l := rfl

@[simp] theorem S1319SourceOrbicurveClause_exactSequence (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).exactSequence =
      S1319LTorsionExactSequence l := rfl

@[simp] theorem S1319SourceOrbicurveClause_cuspCount (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).cuspCount = S1319CuspCount := rfl

@[simp] theorem S1319SourceOrbicurveClause_curveCompatibility (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).curveCompatibility =
      S1319SignInvariant l := rfl

theorem S1319SourceOrbicurveClause_cover_nondegenerate (l : PrimeGeFive) :
    ∃ x y : (S1319SourceOrbicurveClause l).cover, x ≠ y ∧
      (S1319SourceOrbicurveClause l).coverToPunctured x =
        (S1319SourceOrbicurveClause l).coverToPunctured y :=
  S1319CoverToPunctured_nondegenerate l

theorem S1319SourceOrbicurveClause_cover_not_injective (l : PrimeGeFive) :
    ¬ Function.Injective (S1319SourceOrbicurveClause l).coverToPunctured :=
  S1319CoverToPunctured_not_injective l

/-- Consumer-facing summary of the actual clause: every carrier is the
actual Gaussian-curve/sign-quotient carrier, the cusp count is one, the
exact-sequence slot is the actual l-torsion sequence, and the cover has a
genuine two-point fibre. -/
theorem S1319SourceOrbicurveClause_actual_summary (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).curve = S1319Curve l ∧
    (S1319SourceOrbicurveClause l).puncturedCurve = S1319PuncturedCurve l ∧
    (S1319SourceOrbicurveClause l).cover = S1319PuncturedPoints l ∧
    (S1319SourceOrbicurveClause l).structureGroup = Iut.SignGroup ∧
    (S1319SourceOrbicurveClause l).cuspCount = 1 ∧
    (S1319SourceOrbicurveClause l).exactSequence =
      S1319LTorsionExactSequence l ∧
    (∃ x y : (S1319SourceOrbicurveClause l).cover, x ≠ y ∧
      (S1319SourceOrbicurveClause l).coverToPunctured x =
        (S1319SourceOrbicurveClause l).coverToPunctured y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    S1319SourceOrbicurveClause_cover_nondegenerate l⟩

theorem S1319SourceOrbicurveClause_structureGroup_is_signGroup (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).structureGroup = Iut.SignGroup :=
  rfl

theorem S1319SourceOrbicurveClause_fibre_two (l : PrimeGeFive) :
    S1319CoverToPunctured l
        ⟨S1319GaussianPoint l, S1319GaussianPoint_ne_puncture l⟩ =
      S1319CoverToPunctured l
        ⟨-S1319GaussianPoint l,
          S1319_neg_ne_puncture l (S1319GaussianPoint_ne_puncture l)⟩ := by
  apply Subtype.ext
  apply Quotient.sound
  exact Or.inr rfl

/-! ### Negative controls: the curve is nonterminal and the identity cover
is not accepted as the source cover -/

/-- The quotient curve is nonterminal: the point (1,2) and the puncture are
distinct quotient points. -/
theorem S1319Curve_nontrivial (l : PrimeGeFive) :
    ∃ x y : S1319Curve l, x ≠ y := by
  refine ⟨Quotient.mk (S1319SignSetoid l) (S1319GaussianPoint l),
    S1319PunctureClass l, ?_⟩
  intro h
  have hrel := Quotient.exact h
  rcases hrel with hrel | hrel
  · exact S1319GaussianPoint_ne_puncture l hrel.symm
  · have h' : -((S1280Arithmetic l).curve.puncture) = S1319GaussianPoint l :=
      (congrArg Neg.neg hrel).trans (neg_neg (S1319GaussianPoint l))
    rw [S1319_neg_puncture_eq] at h'
    exact S1319GaussianPoint_ne_puncture l h'.symm

/-- The punctured cover has at least two distinct points, so it is not a
one-point/terminal carrier. -/
theorem S1319PuncturedPoints_nontrivial (l : PrimeGeFive) :
    ∃ x y : S1319PuncturedPoints l, x ≠ y := by
  refine ⟨⟨S1319GaussianPoint l, S1319GaussianPoint_ne_puncture l⟩,
    ⟨-S1319GaussianPoint l,
      S1319_neg_ne_puncture l (S1319GaussianPoint_ne_puncture l)⟩, ?_⟩
  intro h
  exact S1319GaussianPoint_ne_neg l (congrArg Subtype.val h)

/-- The identity cover on the punctured point set: this is the degenerate
cover that the source D6 construction is not allowed to use. -/
def S1319IdentityCoverToPunctured (l : PrimeGeFive) :
    S1319PuncturedPoints l → S1319PuncturedPoints l :=
  id

/-- The identity cover has no nontrivial fibre, so it fails the
nondegeneracy condition satisfied by the actual quotient cover. -/
theorem S1319IdentityCover_not_nondegenerate (l : PrimeGeFive) :
    ¬ ∃ x y : S1319PuncturedPoints l, x ≠ y ∧
      S1319IdentityCoverToPunctured l x = S1319IdentityCoverToPunctured l y := by
  rintro ⟨x, y, hxy, hEq⟩
  exact hxy hEq

/-! ## 5. Exact D6 boundary: the orbifold fundamental-group sequence -/

/-- A hyperbolic orbicurve is nonterminal when at least one of its stack
fibres is not a subsingleton category.  This is the formal condition that
excludes the terminal/one-point constant stack from the D6 source object. -/
def S1319NonterminalFiber {F : Type} [Field F]
    (X : Iut.HyperbolicOrbicurve F) : Prop :=
  ∃ U : (Iut.SchemeOverField F)ᵒᵖ,
    ¬ Subsingleton (X.stack.fiber.obj (LocallyDiscrete.mk U))

structure S1319OrbifoldPiData (l : PrimeGeFive) where
  X : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K
  nonterminal : S1319NonterminalFiber X
  signature : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic
  groups : Iut.OrbicurveFundamentalGroupData X
    (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K)

def S1319OrbifoldPiGap (l : PrimeGeFive) : Prop :=
  Nonempty (S1319OrbifoldPiData l)

theorem S1319_exactSequence_is_lTorsion (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).exactSequence =
      S1319LTorsionExactSequence l :=
  rfl

def S1319OrbifoldExactSequenceGap (l : PrimeGeFive) : Prop :=
  S1319OrbifoldPiGap l

/-! ## 6. Axiom footprint -/

#print axioms S1319GaussianPoint_ne_puncture
#print axioms S1319GaussianPoint_ne_neg
#print axioms S1319CoverToPunctured_surjective
#print axioms S1319SignInvariant_proved
#print axioms S1319CoverToPunctured_nondegenerate
#print axioms S1319LTorsionExactSequence
#print axioms S1319SourceOrbicurveClause
#print axioms S1319SourceOrbicurveClause_cover_nondegenerate
#print axioms S1319SourceOrbicurveClause_cover_not_injective
#print axioms S1319Curve_nontrivial
#print axioms S1319PuncturedPoints_nontrivial
#print axioms S1319IdentityCover_not_nondegenerate
#print axioms S1319SourceOrbicurveClause_actual_summary
#print axioms S1319NonterminalFiber

end LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual

end
