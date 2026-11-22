import tmp.sheaf.xif.paper.S1719D5AllActual
import tmp.sheaf.xif.paper.S1711RationalSplitAtFiveBridge
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# S1720: actual arithmetic data for the S1667 curve containing sqrt(-1)

S1687 works over the splitting field S1687Field = SplittingField S1687H of the
even sextic S1687H.  That field has a quadratic subfield Q(sqrt(-3))
(the Weil-pairing determinant field of the S1667 curve), but it does not
contain i.  The paper's arithmetic input, however, requires a number field F
with a square root of -1.

This file constructs the actual field

  F' = SplittingField (S1687H * (X^2 + 1)),

proves that it is a number field, finite and Galois over Q, and that it
contains a square root of -1 (an actual root of X^2+1 in F', not a
postulated one).  It then forms the actual punctured curve

  E' = S1667Punctured.baseChange F',

constructs actual finite places of F' above the rational places 5 and 7 by
comap_surjective, and proves split multiplicative reduction of E' at both
places by the reduction base-change theorem.

## What is actual and what is the exact remaining input

Actual, with complete proofs:

* NumberField, FiniteDimensional Q F', IsGalois Q F';
* HasSqrtNegOne F' from a root of X^2+1 in F';
* the curve E' = S1667Punctured.baseChange F';
* S1720PlaceAboveFive and S1720PlaceAboveSeven, with their contractions;
* HasSplitMultiplicativeReductionAt at both places.

The two source inputs which are *not* faked are recorded as explicit
propositions:

* S1720Torsion23Missing: the literal paper condition (b)
  Torsion23Rational E'.

  S1708 proves Torsion23Rational (S1667Punctured.baseChange S1687Field).
  The missing step is the general algebraic-extension base-change lemma
  S1720Torsion23BaseChangeMissing, which would transport it from
  S1687Field to F'.  Its statement is recorded exactly below; it is not
  replaced by an axiom or by True.

* S1720DegreePrimeToL l: Nat.Coprime (Module.finrank Q F') l.value.

  This is the degreePrimeToL field of ThetaFieldTower.  For l = 5
  (the D5 case handled by S1717/S1719) it is exactly the statement that
  5 does not divide [F' : Q].  It is left as an explicit missing
  statement; no numerical degree or coprimality is assumed.

Conditional on S1720DegreePrimeToL l, the actual InitialThetaArithmeticData l
with Fmod = Q, F = F', K = F' is assembled below.  K = F is allowed
by the source shape and is also used by the checked concrete Gaussian example
in ConcreteArithmeticExample.lean.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual

/-! ## 1. The defining polynomial and the field -/

/-- The polynomial X^2 + 1. -/
def S1720SqrtPolynomial : ℚ[X] := X ^ 2 + 1

/-- The defining polynomial of F': the product of the S1687 sextic with X^2+1. -/
def S1720H : ℚ[X] := S1687H * S1720SqrtPolynomial

/-- The actual field F' = SplittingField (S1687H * (X^2+1)). -/
abbrev S1720Field : Type := Polynomial.SplittingField S1720H

local instance S1720FieldDecEq : DecidableEq S1720Field := Classical.decEq _

instance S1720NumberField : NumberField S1720Field where
  to_charZero := inferInstance
  to_finiteDimensional := by
    letI : IsSplittingField ℚ S1720Field S1720H :=
      Polynomial.IsSplittingField.splittingField S1720H
    exact Polynomial.IsSplittingField.finiteDimensional S1720Field S1720H

instance S1720FiniteDimensional : FiniteDimensional ℚ S1720Field :=
  inferInstance

/-- F' is finite over Q. -/
theorem S1720_finiteDimensional : FiniteDimensional ℚ S1720Field :=
  inferInstance

/-- The normal instance from the splitting-field property. -/
instance S1720Normal : Normal ℚ S1720Field :=
  Polynomial.SplittingField.instNormal (F := ℚ) S1720H

/-- F' is Galois over Q: it is a splitting field in characteristic zero. -/
instance S1720IsGalois : IsGalois ℚ S1720Field :=
  isGalois_iff.mpr ⟨inferInstance, S1720Normal⟩

theorem S1720_isGalois : IsGalois ℚ S1720Field := inferInstance

/-! ## 2. The polynomial X^2+1 splits in F' and has a root -/

theorem S1720H_splits : (S1720H.map (algebraMap ℚ S1720Field)).Splits :=
  Polynomial.SplittingField.splits S1720H

/-- X^2+1 splits in F' because it divides the defining polynomial. -/
theorem S1720SqrtPolynomial_splits :
    (S1720SqrtPolynomial.map (algebraMap ℚ S1720Field)).Splits := by
  have hf : ((S1687H * S1720SqrtPolynomial).map (algebraMap ℚ S1720Field)).Splits := by
    simpa [S1720H] using S1720H_splits
  rw [Polynomial.map_mul] at hf
  rw [Polynomial.splits_mul'] at hf
  exact hf.2.resolve_right (by
    intro h
    exact S1687H_map_ne_zero (by simpa using h))

theorem S1720SqrtPolynomial_degree :
    S1720SqrtPolynomial.degree = (2 : WithBot ℕ) := by
  unfold S1720SqrtPolynomial
  compute_degree!


/-- The map of X^2+1 to F' is nonzero. -/
theorem S1720SqrtPolynomial_map_ne_zero :
    S1720SqrtPolynomial.map (algebraMap ℚ S1720Field) ≠ 0 := by
  rw [Polynomial.map_ne_zero_iff (algebraMap ℚ S1720Field).injective]
  intro h
  have hdeg := S1720SqrtPolynomial_degree
  rw [h] at hdeg
  simp at hdeg

/-- The S1687 sextic splits in F'. -/
theorem S1687H_splits_in_F' : (S1687H.map (algebraMap ℚ S1720Field)).Splits := by
  have hf : ((S1687H * S1720SqrtPolynomial).map (algebraMap ℚ S1720Field)).Splits := by
    simpa [S1720H] using S1720H_splits
  rw [Polynomial.map_mul] at hf
  rw [Polynomial.splits_mul'] at hf
  exact hf.1.resolve_right S1720SqrtPolynomial_map_ne_zero

/-- The canonical Q-algebra map S1687Field -> F' obtained from the splitting
field property of S1687H. -/
noncomputable def S1720Lift : S1687Field →ₐ[ℚ] S1720Field :=
  Polynomial.SplittingField.lift (f := S1687H) (L := S1720Field) S1687H_splits_in_F'


/-- The actual square root of -1 in F', obtained from a root of X^2+1
in the splitting field. -/
theorem S1720HasSqrtNegOne : HasSqrtNegOne S1720Field := by
  have hdeg : (S1720SqrtPolynomial.map (algebraMap ℚ S1720Field)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap ℚ S1720Field).injective,
      S1720SqrtPolynomial_degree]
    norm_num
  let r : S1720Field :=
    Polynomial.rootOfSplits S1720SqrtPolynomial_splits hdeg
  have hr : Polynomial.eval r
      (S1720SqrtPolynomial.map (algebraMap ℚ S1720Field)) = 0 :=
    Polynomial.eval_rootOfSplits S1720SqrtPolynomial_splits hdeg
  have hr' : Polynomial.aeval r S1720SqrtPolynomial = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using hr
  refine ⟨r, ?_⟩
  have h : r ^ 2 + 1 = 0 := by
    simpa [S1720SqrtPolynomial] using hr'
  rw [pow_two] at h
  linear_combination h

theorem S1720_hasSqrtNegOne : HasSqrtNegOne S1720Field :=
  S1720HasSqrtNegOne

/-! ## 3. The curve E' = S1667Punctured.baseChange F' -/

/-- The base-changed S1667 punctured curve over F'. -/
abbrev S1720Curve : PuncturedEllipticCurve S1720Field :=
  S1667Punctured.baseChange S1720Field

/-- The underlying curve is the base change of the S1667 curve. -/
@[simp] theorem S1720Curve_curve :
    S1720Curve.curve = S1667Curve.baseChange S1720Field := rfl

/-! ## 4. Actual places above 5 and 7 -/

/-- An actual finite place of F' above the rational place 5, obtained from
comap_surjective. -/
noncomputable def S1720PlaceAboveFive : NumberField.FinitePlace S1720Field :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1720Field) concreteFivePlace)

/-- The place above 5 contracts to the rational place 5. -/
theorem S1720PlaceAboveFive_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S1720PlaceAboveFive = concreteFivePlace :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1720Field) concreteFivePlace)

/-- An actual finite place of F' above the rational place 7, obtained from
comap_surjective. -/
noncomputable def S1720PlaceAboveSeven : NumberField.FinitePlace S1720Field :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1720Field) concreteSevenPlace)

/-- The place above 7 contracts to the rational place 7. -/
theorem S1720PlaceAboveSeven_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S1720PlaceAboveSeven =
      concreteSevenPlace :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := S1720Field) concreteSevenPlace)

/-! ## 5. Split multiplicative reduction at the two actual places -/

/-- E' has split multiplicative reduction at the actual place above 5. -/
theorem S1720SplitAtFive :
    S1720Curve.HasSplitMultiplicativeReductionAt S1720PlaceAboveFive := by
  apply PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
  rw [S1720PlaceAboveFive_comap]
  exact S1711RationalSplitAtFive

/-- E' has split multiplicative reduction at the actual place above 7. -/
theorem S1720SplitAtSeven :
    S1720Curve.HasSplitMultiplicativeReductionAt S1720PlaceAboveSeven := by
  apply PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
  rw [S1720PlaceAboveSeven_comap]
  exact S1717_splitMultiplicativeReductionAtSeven

/-! ## 6. The exact remaining torsion input -/

/-- The literal paper condition (b) over the actual field F'.  This is the
exact torsion input still missing: S1708 gives it over S1687Field, and the
only gap is the general algebraic-extension base-change lemma stated next. -/
def S1720Torsion23Missing : Prop :=
  PuncturedEllipticCurve.Torsion23Rational S1720Curve

/-- The exact general base-change step that is missing for the torsion input.
It is the statement that Torsion23Rational passes to any algebraic field
extension.  No instance of this proposition is assumed; it is only recorded. -/
def S1720Torsion23BaseChangeMissing : Prop :=
  ∀ {k K : Type} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : PuncturedEllipticCurve k),
    PuncturedEllipticCurve.Torsion23Rational X →
    PuncturedEllipticCurve.Torsion23Rational (X.baseChange K)

/-- Torsion23Rational only depends on the underlying curve, not on the
puncture or the ellipticity proof. -/
theorem Torsion23Rational_congr_curve {F : Type} [Field F]
    {X Y : PuncturedEllipticCurve F} (h : X.curve = Y.curve) :
    PuncturedEllipticCurve.Torsion23Rational X ↔
      PuncturedEllipticCurve.Torsion23Rational Y := by
  cases X with
  | mk curve isElliptic puncture =>
  cases Y with
  | mk curve' isElliptic' puncture' =>
  simp only at h
  subst h
  rfl

/-- The iterated base change and the direct base change have the same
underlying curve. -/
theorem S1720IteratedCurve_eq
    [Algebra S1687Field S1720Field] [IsScalarTower ℚ S1687Field S1720Field] :
    ((S1667Punctured.baseChange S1687Field).baseChange S1720Field).curve =
      S1720Curve.curve := by
  simp only [PuncturedEllipticCurve.baseChange_curve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_map]
  congr 1
  ext x
  exact (IsScalarTower.algebraMap_apply ℚ S1687Field S1720Field x).symm

/-- If the general base-change step is supplied, then S1708 gives the exact
paper torsion condition for the direct base-changed curve over F'.  The
canonical algebra structure S1687Field -> F' is built locally from the
splitting-field lift; only the general base-change lemma is missing. -/
theorem S1720Torsion23Missing_of_baseChange
    (h : S1720Torsion23BaseChangeMissing) : S1720Torsion23Missing := by
  letI : Algebra S1687Field S1720Field := S1720Lift.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ S1687Field S1720Field :=
    IsScalarTower.of_algebraMap_eq fun x => (S1720Lift.commutes x).symm
  haveI : Algebra.IsAlgebraic S1687Field S1720Field := by
    haveI : Algebra.IsIntegral S1687Field S1720Field := by
      refine ⟨fun x => ?_⟩
      exact IsIntegral.tower_top (A := S1687Field) (IsIntegral.of_finite ℚ x)
    infer_instance
  exact (Torsion23Rational_congr_curve S1720IteratedCurve_eq).mp
    (h (S1667Punctured.baseChange S1687Field)
      LeanFormal.IUT.XiFPaper.S1708NinePointInjectionActual.S1708Torsion23Rational)

/-- The exact paper condition (b) is literally Torsion23Rational E'. -/
theorem S1720PaperConditionB_eq :
    S1667PaperConditionB S1720Field S1720Curve = S1720Torsion23Missing := rfl

/-! ## 7. The exact remaining degree input -/

/-- The degreePrimeToL field of ThetaFieldTower, recorded exactly for F'. -/
def S1720DegreePrimeToL (l : PrimeGeFive) : Prop :=
  Nat.Coprime (Module.finrank ℚ S1720Field) l.value

/-- The tower Q -> F' -> F'.  The square-root condition is the actual
S1720HasSqrtNegOne; degreePrimeToL is the exact missing statement. -/
theorem S1720ThetaFieldTower (l : PrimeGeFive)
    (hdeg : S1720DegreePrimeToL l) :
    ThetaFieldTower l ℚ S1720Field S1720Field where
  sqrtNegOne := S1720HasSqrtNegOne
  degreePrimeToL := hdeg

/-! ## 8. Conditional assembly of the actual arithmetic data -/

/-- The actual InitialThetaArithmeticData l with Fmod = Q, F = F',
K = F', conditional only on the explicit coprimality statement.
There is no faked field, square root, or curve: every field of the structure
is the actual object constructed above. -/
noncomputable def S1720InitialThetaArithmeticData (l : PrimeGeFive)
    (hdeg : S1720DegreePrimeToL l) : InitialThetaArithmeticData l where
  Fmod := ℚ
  F := S1720Field
  K := S1720Field
  tower := S1720ThetaFieldTower l hdeg
  curve := S1720Curve

/-- The assembled data has the actual field F'. -/
@[simp] theorem S1720InitialThetaArithmeticData_F (l : PrimeGeFive)
    (hdeg : S1720DegreePrimeToL l) :
    (S1720InitialThetaArithmeticData l hdeg).F = S1720Field := rfl

/-- The assembled data has the actual base-changed curve. -/
@[simp] theorem S1720InitialThetaArithmeticData_curve (l : PrimeGeFive)
    (hdeg : S1720DegreePrimeToL l) :
    (S1720InitialThetaArithmeticData l hdeg).curve = S1720Curve := rfl

/-- The assembled data satisfies the square-root condition actually. -/
theorem S1720InitialThetaArithmeticData_sqrtNegOne (l : PrimeGeFive)
    (hdeg : S1720DegreePrimeToL l) :
    HasSqrtNegOne (S1720InitialThetaArithmeticData l hdeg).F :=
  (S1720InitialThetaArithmeticData l hdeg).tower.sqrtNegOne

/-! ## 9. The exact missing package, and the conditional paper data -/

/-- The exact two source inputs which are still missing for this curve: the
torsion condition and the coprimality of the field degree with l. -/
structure S1720ExactMissing (l : PrimeGeFive) where
  torsion23 : S1720Torsion23Missing
  degreePrimeToL : S1720DegreePrimeToL l

/-- The conditional paper arithmetic data together with the exact missing
torsion statement: the data itself is actual, and the torsion condition is a
separate source hypothesis, not a field of InitialThetaArithmeticData. -/
structure S1720PaperArithmeticData (l : PrimeGeFive) where
  degreePrimeToL : S1720DegreePrimeToL l
  torsion23 : S1720Torsion23Missing

/-- The actual InitialThetaArithmeticData carried by the paper data. -/
noncomputable def S1720PaperArithmeticData.toInitialTheta
    {l : PrimeGeFive} (P : S1720PaperArithmeticData l) :
    InitialThetaArithmeticData l :=
  S1720InitialThetaArithmeticData l P.degreePrimeToL

@[simp] theorem S1720PaperArithmeticData.toInitialTheta_F
    {l : PrimeGeFive} (P : S1720PaperArithmeticData l) :
    P.toInitialTheta.F = S1720Field := rfl

@[simp] theorem S1720PaperArithmeticData.toInitialTheta_curve
    {l : PrimeGeFive} (P : S1720PaperArithmeticData l) :
    P.toInitialTheta.curve = S1720Curve := rfl

/-- From the exact missing package build the paper arithmetic data.  The
square root, field, curve and places are all actual; only the two explicit
missing statements are supplied as hypotheses. -/
theorem S1720PaperArithmeticData_of_missing (l : PrimeGeFive)
    (M : S1720ExactMissing l) : S1720PaperArithmeticData l where
  degreePrimeToL := M.degreePrimeToL
  torsion23 := M.torsion23

/-- The paper data exposes the exact torsion condition. -/
theorem S1720PaperArithmeticData_missing (l : PrimeGeFive)
    (P : S1720PaperArithmeticData l) : S1720Torsion23Missing :=
  P.torsion23

/-! ## 10. Axiom footprint -/

#print axioms S1720HasSqrtNegOne
#print axioms S1720SqrtPolynomial_splits
#print axioms S1720PlaceAboveFive_comap
#print axioms S1720PlaceAboveSeven_comap
#print axioms S1720SplitAtFive
#print axioms S1720SplitAtSeven
#print axioms S1720ThetaFieldTower
#print axioms S1720InitialThetaArithmeticData_sqrtNegOne
#print axioms S1720Torsion23Missing_of_baseChange
#print axioms S1720PaperArithmeticData_of_missing

end LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
end