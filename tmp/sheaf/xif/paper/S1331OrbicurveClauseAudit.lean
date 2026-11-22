/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

/-!
# S1331: independent audit of `SourceOrbicurveClause` (D6)

This file is an independent audit of the D6 clause type
`Theorem311Source.SourceOrbicurveClause`, over the actual S1280 Gaussian
arithmetic input.  It does not import, and does not depend on, any file of the
S1319 line; the statements below are derived only from the frozen production
definitions and the actual S1280 data.

## Field inventory (the 13 fields of `SourceOrbicurveClause`)

```
 1  curve                : Type u      -- points of the curve
 2  puncturedCurve       : Type v      -- points of the punctured curve
 3  cover                : Type w      -- the covering
 4  structureGroup       : Type u      -- the structure group
 5  [structureGroupLaw]  : Group structureGroup
 6  curveToPunctured      : puncturedCurve -> curve
 7  coverToPunctured      : cover -> puncturedCurve
 8  cover_surjective      : Surjective coverToPunctured
 9  exactSequence         : SourceExactSequenceClause
10  cuspCount             : Nat
11  cuspCount_pos         : 0 < cuspCount
12  curveCompatibility    : Prop
13  curveCompatibility_proved
```

## Audit result

* **Actually constructible from the S1280 data: fields 1, 2, 6.**  The actual
  S1280 curve is the base change of the concrete split multiplicative curve
  `y^2 + xy = x^3 + 5` over `Q(i)`, punctured at the origin.  Fields 1 and 2
  are the carrier of its projective points and the complement of the actual
  puncture; field 6 is the inclusion.  The file constructs these three values,
  proves that the first two are nonempty and *not* subsingletons (each has at
  least two actual points), and proves that the inclusion is injective with
  range exactly the complement of the puncture.  So the exact first field is
  `S1331ClauseCurve l = (S1280Arithmetic l).curve.curve.toProjective.Point`,
  not `PUnit`, not a point, and not a fresh choice.

  *Reading of the first field.*  `SourceOrbicurveClause` declares
  `curve : Type u` without linking it to the arithmetic input (the clause type
  has no parameter depending on `A`).  Read literally the field is an
  arbitrary type.  The audit fixes the point-carrier reading, the only value
  that carries the actual curve's points and supports the
  `puncturedCurve`/`curveToPunctured` reading of fields 2 and 6.  The literal
  alternative `PuncturedEllipticCurve F` is also an element of `Type`, but it
  does not support the punctured-complement reading; the ambiguity is recorded
  here rather than hidden.

* **The first field of the exact-sequence slot is also actual**: the base group
  of the source exact sequence is the absolute Galois group of the actual field
  `K` (`SourceOrbicurveGroupData X (Iut.AbsoluteGaloisProfinite A.K)` in the
  constructor layer).  Its carrier and group structure are constructed here;
  the other nine field slots of `SourceExactSequenceClause` (the cover and
  geometric groups with their group structures, the two maps, injectivity,
  surjectivity, and exactness) are not determined.

* **Not constructible from the S1280 data: fields 3, 4, 5, 7, 8, 9, 10, 11,
  12, 13.**  No compiled donor supplies the nondegenerate cover, the structure
  group, the geometric/cover fundamental groups, a cusp count, or the
  compatibility proposition.  The residual obligation is packaged below as
  `S1331ResidualFields l` — exactly the clause fields left after the actual
  first three are fixed; `S1331ResidualFields.toClause` is the corresponding
  clause constructor.

* **No fake terminal.**  With the actual first field fixed, a point (terminal)
  substitution is impossible: the actual curve carrier is not a subsingleton,
  and a surjection from a subsingleton cover onto the actual punctured carrier
  would force the punctured carrier to be a subsingleton, which it is not.  At
  the stack level the existing production theorem
  `no_missingD6Realization_with_terminalConstantFiber` excludes the terminal
  constant fiber from every `MissingD6GeometricRealization`.
  Consequently a clause with the actual first field cannot be a point
  substitution at the curve or cover fields, and this file does not manufacture
  any inhabitant of `SourceOrbicurveClause`.

* **Why an inhabitant must not be manufactured.**  `D6OrbicurveConstruction l`
  is, at the actual arithmetic input, *exactly* the nonemptiness of the clause
  type: `D6OrbicurveConstruction l <-> Nonempty SourceOrbicurveClause` (both
  directions are proved below).  A degenerate clause would therefore close the
  D6 gate for every `l` with no source content.  The file records this
  equivalence and provides no such clause.

Everything here is stated over the concrete S1280 input; nothing is claimed
about an arbitrary `InitialThetaArithmeticData`.  There is no `sorry`, no new
axiom, no `PUnit`/terminal substitution as source data.  Axiom footprints are
printed at the end.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceDefinition31Root
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

local instance s1331GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The actual D6 curve and the exact first field -/

/-- The actual curve of the S1280 arithmetic input: the base change of the
concrete split multiplicative curve `y^2 + xy = x^3 + 5` to `Q(i)`, punctured
at the origin.  This is the first field of the exact missing D6 object
`MissingD6GeometricRealization`. -/
abbrev S1331ActualCurve (l : PrimeGeFive) :
    PuncturedEllipticCurve (S1280Arithmetic l).F :=
  (S1280Arithmetic l).curve

/-- The first field of the exact missing D6 object is literally the S1280
curve: no new choice is made. -/
@[simp] theorem S1331D6FirstField_eq (l : PrimeGeFive) :
    S1331ActualCurve l = (S1280Arithmetic l).curve := rfl

/-- The exact first field of `SourceOrbicurveClause`: the carrier of the
projective points of the actual curve.  It is a value of the field type
`Type`, determined by the actual S1280 curve.  This is the point-carrier
reading of the unlabelled `curve : Type u` field; the module header records
that the production clause type does not by itself force this reading. -/
abbrev S1331ClauseCurve (l : PrimeGeFive) : Type :=
  (S1280Arithmetic l).curve.curve.toProjective.Point

/-- The exact first field, by definition. -/
@[simp] theorem S1331ClauseCurve_eq (l : PrimeGeFive) :
    S1331ClauseCurve l =
      (S1280Arithmetic l).curve.curve.toProjective.Point := rfl

/-- The actual puncture is a point of the exact first field: the field is
inhabited by actual data. -/
theorem S1331ClauseCurve_nonempty (l : PrimeGeFive) :
    Nonempty (S1331ClauseCurve l) :=
  ⟨(S1280Arithmetic l).curve.puncture⟩

/-! ### 1.1 The actual affine point `(1,2)` and its negative `(1,-3)`

The split curve is `y^2 + xy = x^3 + 5`; `(1,2)` and `(1,-3)` are two
distinct actual points, and neither is the origin.  They witness that neither
the curve carrier nor the punctured carrier is a subsingleton. -/

theorem S1331_coeffA1 (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.curve.a₁ = (1 : (S1280Arithmetic l).F) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1280Arithmetic l).F)).a₁ = 1
  rw [WeierstrassCurve.map_a₁, concreteSplitCurve]
  norm_num

theorem S1331_coeffA2 (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.curve.a₂ = (0 : (S1280Arithmetic l).F) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1280Arithmetic l).F)).a₂ = 0
  rw [WeierstrassCurve.map_a₂, concreteSplitCurve]
  norm_num

theorem S1331_coeffA3 (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.curve.a₃ = (0 : (S1280Arithmetic l).F) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1280Arithmetic l).F)).a₃ = 0
  rw [WeierstrassCurve.map_a₃, concreteSplitCurve]
  norm_num

theorem S1331_coeffA4 (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.curve.a₄ = (0 : (S1280Arithmetic l).F) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1280Arithmetic l).F)).a₄ = 0
  rw [WeierstrassCurve.map_a₄, concreteSplitCurve]
  norm_num

theorem S1331_coeffA6 (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.curve.a₆ = (5 : (S1280Arithmetic l).F) := by
  change (concreteSplitCurve.map (algebraMap ℚ (S1280Arithmetic l).F)).a₆ = 5
  rw [WeierstrassCurve.map_a₆, concreteSplitCurve]
  norm_num

theorem S1331_nonsingular_one_two (l : PrimeGeFive) :
    ((S1280Arithmetic l).curve.curve.toAffine).Nonsingular 1 2 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
    S1331_coeffA1 l, S1331_coeffA2 l, S1331_coeffA3 l, S1331_coeffA4 l,
    S1331_coeffA6 l]
  norm_num

theorem S1331_nonsingular_one_neg_three (l : PrimeGeFive) :
    ((S1280Arithmetic l).curve.curve.toAffine).Nonsingular 1 (-3) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff,
    S1331_coeffA1 l, S1331_coeffA2 l, S1331_coeffA3 l, S1331_coeffA4 l,
    S1331_coeffA6 l]
  norm_num

/-- The actual point `(1,2)` of the S1280 curve. -/
noncomputable def S1331Point (l : PrimeGeFive) : S1331ClauseCurve l :=
  WeierstrassCurve.Projective.Point.fromAffine
    (WeierstrassCurve.Affine.Point.some 1 2 (S1331_nonsingular_one_two l))

/-- The actual point `(1,-3)`, the negative of `(1,2)`. -/
noncomputable def S1331PointNeg (l : PrimeGeFive) : S1331ClauseCurve l :=
  WeierstrassCurve.Projective.Point.fromAffine
    (WeierstrassCurve.Affine.Point.some 1 (-3) (S1331_nonsingular_one_neg_three l))

theorem S1331Point_point (l : PrimeGeFive) :
    (S1331Point l).point =
      (⟦![1, 2, 1]⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) := by
  rw [S1331Point, WeierstrassCurve.Projective.Point.fromAffine_some,
    WeierstrassCurve.Projective.Point.mk_point]

theorem S1331PointNeg_point (l : PrimeGeFive) :
    (S1331PointNeg l).point =
      (⟦![1, -3, 1]⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) := by
  rw [S1331PointNeg, WeierstrassCurve.Projective.Point.fromAffine_some,
    WeierstrassCurve.Projective.Point.mk_point]

/-- The actual puncture is the origin of the projective point carrier. -/
theorem S1331_puncture_point (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.puncture.point =
      (⟦![0, 1, 0]⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) := by
  change (PuncturedEllipticCurve.projectivePointClassMap
      (algebraMap ℚ (S1280Arithmetic l).F)
      (⟦![0, 1, 0]⟧ : WeierstrassCurve.Projective.PointClass ℚ)) = ⟦![0, 1, 0]⟧
  rw [PuncturedEllipticCurve.projectivePointClassMap_mk]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The actual puncture is the zero of the projective point group. -/
theorem S1331_puncture_eq_zero (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.puncture = (0 : S1331ClauseCurve l) := by
  apply WeierstrassCurve.Projective.Point.ext
  rw [S1331_puncture_point l, WeierstrassCurve.Projective.Point.zero_point]

theorem S1331Point_ne_zero (l : PrimeGeFive) :
    S1331Point l ≠ (0 : S1331ClauseCurve l) :=
  WeierstrassCurve.Projective.Point.fromAffine_some_ne_zero
    (S1331_nonsingular_one_two l)

theorem S1331PointNeg_ne_zero (l : PrimeGeFive) :
    S1331PointNeg l ≠ (0 : S1331ClauseCurve l) :=
  WeierstrassCurve.Projective.Point.fromAffine_some_ne_zero
    (S1331_nonsingular_one_neg_three l)

theorem S1331Point_ne_puncture (l : PrimeGeFive) :
    S1331Point l ≠ (S1280Arithmetic l).curve.puncture := by
  rw [S1331_puncture_eq_zero l]
  exact S1331Point_ne_zero l

theorem S1331PointNeg_ne_puncture (l : PrimeGeFive) :
    S1331PointNeg l ≠ (S1280Arithmetic l).curve.puncture := by
  rw [S1331_puncture_eq_zero l]
  exact S1331PointNeg_ne_zero l

/-- The two actual points have distinct projective classes. -/
theorem S1331Point_ne_S1331PointNeg (l : PrimeGeFive) :
    S1331Point l ≠ S1331PointNeg l := by
  intro h
  have hp : (S1331Point l).point = (S1331PointNeg l).point := by rw [h]
  rw [S1331Point_point l, S1331PointNeg_point l] at hp
  refine WeierstrassCurve.Projective.not_equiv_of_Y_ne
    (P := ![1, 2, 1]) (Q := ![1, -3, 1]) ?_ (Quotient.exact hp)
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- **The exact first field is not a point.**  The actual curve carrier has at
least two distinct actual points, so no terminal/point substitution can be the
exact first field. -/
theorem S1331ClauseCurve_not_subsingleton (l : PrimeGeFive) :
    ¬ Subsingleton (S1331ClauseCurve l) := by
  intro h
  have hpq : S1331Point l = (S1280Arithmetic l).curve.puncture :=
    Subsingleton.elim _ _
  exact S1331Point_ne_puncture l hpq

/-- The exact first field is not `PUnit`. -/
theorem S1331ClauseCurve_ne_punit (l : PrimeGeFive) :
    S1331ClauseCurve l ≠ PUnit := by
  intro h
  exact S1331ClauseCurve_not_subsingleton l
    (h ▸ (inferInstance : Subsingleton PUnit))

/-! ## 2. The exact second and third fields -/

/-- The exact second field of `SourceOrbicurveClause`: the actual punctured
projective points, i.e. the actual curve carrier with the actual puncture
removed. -/
abbrev S1331ClausePuncturedCurve (l : PrimeGeFive) : Type :=
  {P : S1331ClauseCurve l // P ≠ (S1280Arithmetic l).curve.puncture}

@[simp] theorem S1331ClausePuncturedCurve_eq (l : PrimeGeFive) :
    S1331ClausePuncturedCurve l =
      {P : S1331ClauseCurve l // P ≠ (S1280Arithmetic l).curve.puncture} := rfl

/-- The exact third field of `SourceOrbicurveClause`: the inclusion of the
punctured points into the curve. -/
def S1331ClauseCurveToPunctured (l : PrimeGeFive) :
    S1331ClausePuncturedCurve l → S1331ClauseCurve l :=
  fun P => P.1

@[simp] theorem S1331ClauseCurveToPunctured_apply (l : PrimeGeFive)
    (P : S1331ClausePuncturedCurve l) :
    S1331ClauseCurveToPunctured l P = P.1 := rfl

/-- The actual point `(1,2)` is a point of the exact second field. -/
theorem S1331ClausePuncturedCurve_nonempty (l : PrimeGeFive) :
    Nonempty (S1331ClausePuncturedCurve l) :=
  ⟨⟨S1331Point l, S1331Point_ne_puncture l⟩⟩

/-- The exact second field is not a point either: `(1,2)` and `(1,-3)` are
two distinct punctured points. -/
theorem S1331ClausePuncturedCurve_not_subsingleton (l : PrimeGeFive) :
    ¬ Subsingleton (S1331ClausePuncturedCurve l) := by
  intro h
  have hpq : (⟨S1331Point l, S1331Point_ne_puncture l⟩ : S1331ClausePuncturedCurve l) =
      ⟨S1331PointNeg l, S1331PointNeg_ne_puncture l⟩ :=
    Subsingleton.elim _ _
  exact S1331Point_ne_S1331PointNeg l (congrArg Subtype.val hpq)

/-- The exact third field is an injection. -/
theorem S1331ClauseCurveToPunctured_injective (l : PrimeGeFive) :
    Function.Injective (S1331ClauseCurveToPunctured l) :=
  fun _ _ h => Subtype.ext h

/-- The range of the exact third field is exactly the complement of the actual
puncture: no point of the curve is missing or added. -/
theorem S1331ClauseCurveToPunctured_range (l : PrimeGeFive) :
    Set.range (S1331ClauseCurveToPunctured l) =
      {P : S1331ClauseCurve l | P ≠ (S1280Arithmetic l).curve.puncture} := by
  ext P
  constructor
  · rintro ⟨Q, rfl⟩
    exact Q.2
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩

/-! ## 3. The first field of the exact-sequence slot

The base group of the source exact sequence is the absolute Galois group of the
actual field `K`: the constructor layer builds every source exact sequence as
`SourceOrbicurveGroupData X (Iut.AbsoluteGaloisProfinite A.K)`, whose
`groups.exactSequence` has base group `G_K`.  So the first field of
`SourceExactSequenceClause.baseGroup` (and its group structure) is actual;
the other nine field slots are the residual D6 data. -/

/-- The actual base group of the exact-sequence field: the absolute Galois
group of the actual field `K`, as an actual type with its group structure. -/
abbrev S1331ExactSequenceBaseGroup (l : PrimeGeFive) : Type :=
  (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K : Type)

/-- The group structure of the actual base group. -/
noncomputable instance S1331ExactSequenceBaseGroupGroup (l : PrimeGeFive) :
    Group (S1331ExactSequenceBaseGroup l) :=
  inferInstanceAs (Group (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K))

theorem S1331ExactSequenceBaseGroup_nonempty (l : PrimeGeFive) :
    Nonempty (S1331ExactSequenceBaseGroup l) :=
  ⟨1⟩

/-- The residual of the exact-sequence slot once its first field is the actual
base group `G_K`: the cover and geometric groups and the exact sequence
between them.  This is `SourceExactSequenceClause` with its actual first field
fixed. -/
structure S1331ExactSequenceResidual (l : PrimeGeFive) where
  coverGroup : Type
  [coverGroupLaw : Group coverGroup]
  geometricGroup : Type
  [geometricGroupLaw : Group geometricGroup]
  injection : geometricGroup →* coverGroup
  projection : coverGroup →* S1331ExactSequenceBaseGroup l
  injection_injective : Function.Injective injection
  projection_surjective : Function.Surjective projection
  exact_at_cover : ∀ x : coverGroup,
    projection x = 1 ↔ ∃ y : geometricGroup, injection y = x

attribute [instance] S1331ExactSequenceResidual.coverGroupLaw
  S1331ExactSequenceResidual.geometricGroupLaw

namespace S1331ExactSequenceResidual

variable {l : PrimeGeFive} (E : S1331ExactSequenceResidual l)

/-- The exact-sequence clause with the actual base group. -/
def toExactSequence : SourceExactSequenceClause.{0, 0, 0} where
  baseGroup := S1331ExactSequenceBaseGroup l
  coverGroup := E.coverGroup
  geometricGroup := E.geometricGroup
  injection := E.injection
  projection := E.projection
  injection_injective := E.injection_injective
  projection_surjective := E.projection_surjective
  exact_at_cover := E.exact_at_cover

@[simp] theorem toExactSequence_baseGroup :
    E.toExactSequence.baseGroup = S1331ExactSequenceBaseGroup l := rfl

@[simp] theorem toExactSequence_coverGroup :
    E.toExactSequence.coverGroup = E.coverGroup := rfl

@[simp] theorem toExactSequence_geometricGroup :
    E.toExactSequence.geometricGroup = E.geometricGroup := rfl

@[simp] theorem toExactSequence_injection :
    E.toExactSequence.injection = E.injection := rfl

@[simp] theorem toExactSequence_projection :
    E.toExactSequence.projection = E.projection := rfl

end S1331ExactSequenceResidual

/-! ## 4. The residual clause fields and the clause with the actual first field

`S1331ResidualFields l` is exactly the part of `SourceOrbicurveClause` left
after fixing the actual first three fields and the actual exact-sequence base
group.  Its `toClause` constructor is the only way the clause is produced in
this file: the first three fields are actual values, never fresh choices. -/

/-- The residual fields of `SourceOrbicurveClause` over the actual S1280 data:
the cover, the structure group, the cover map and its surjectivity, the exact
sequence, the cusp count with its positivity, and the opaque compatibility
proposition together with its proof.  None of these is determined by the S1280
data. -/
structure S1331ResidualFields (l : PrimeGeFive) where
  cover : Type
  structureGroup : Type
  [structureGroupLaw : Group structureGroup]
  coverToPunctured : cover → S1331ClausePuncturedCurve l
  cover_surjective : Function.Surjective coverToPunctured
  exactSequence : S1331ExactSequenceResidual l
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount
  curveCompatibility : Prop
  curveCompatibility_proved : curveCompatibility

attribute [instance] S1331ResidualFields.structureGroupLaw

namespace S1331ResidualFields

variable {l : PrimeGeFive} (R : S1331ResidualFields l)

/-- The clause with the exact actual first three fields and the residual data.
This is the only clause constructor in the file; it requires the residual
fields as explicit data. -/
def toClause : SourceOrbicurveClause.{0, 0, 0} where
  curve := S1331ClauseCurve l
  puncturedCurve := S1331ClausePuncturedCurve l
  cover := R.cover
  structureGroup := R.structureGroup
  curveToPunctured := S1331ClauseCurveToPunctured l
  coverToPunctured := R.coverToPunctured
  cover_surjective := R.cover_surjective
  exactSequence := R.exactSequence.toExactSequence
  cuspCount := R.cuspCount
  cuspCount_pos := R.cuspCount_pos
  curveCompatibility := R.curveCompatibility
  curveCompatibility_proved := R.curveCompatibility_proved

@[simp] theorem toClause_curve :
    (R.toClause).curve = S1331ClauseCurve l := rfl

@[simp] theorem toClause_puncturedCurve :
    (R.toClause).puncturedCurve = S1331ClausePuncturedCurve l := rfl

@[simp] theorem toClause_curveToPunctured :
    (R.toClause).curveToPunctured = S1331ClauseCurveToPunctured l := rfl

@[simp] theorem toClause_cover :
    (R.toClause).cover = R.cover := rfl

@[simp] theorem toClause_structureGroup :
    (R.toClause).structureGroup = R.structureGroup := rfl

@[simp] theorem toClause_coverToPunctured :
    (R.toClause).coverToPunctured = R.coverToPunctured := rfl

@[simp] theorem toClause_exactSequence :
    (R.toClause).exactSequence = R.exactSequence.toExactSequence := rfl

/-- The exact-sequence slot of any clause produced here has the actual base
group `G_K`: the first field of the exact-sequence field is actual. -/
@[simp] theorem toClause_exactSequence_baseGroup :
    (R.toClause).exactSequence.baseGroup = S1331ExactSequenceBaseGroup l := rfl

@[simp] theorem toClause_cuspCount :
    (R.toClause).cuspCount = R.cuspCount := rfl

@[simp] theorem toClause_curveCompatibility :
    (R.toClause).curveCompatibility = R.curveCompatibility := rfl

/-- The three actual fields of the clause are exactly the values constructed
above. -/
theorem toClause_actual_first_fields :
    (R.toClause).curve = S1331ClauseCurve l ∧
      (R.toClause).puncturedCurve = S1331ClausePuncturedCurve l ∧
      (R.toClause).curveToPunctured = S1331ClauseCurveToPunctured l :=
  ⟨rfl, rfl, rfl⟩

/-- The exact first field of any clause produced here is not a point. -/
theorem toClause_curve_not_subsingleton :
    ¬ Subsingleton (R.toClause).curve := by
  rw [toClause_curve]
  exact S1331ClauseCurve_not_subsingleton l

/-- **No point cover.**  With the actual punctured carrier, the cover cannot be
a subsingleton: surjectivity onto a carrier with two distinct actual points is
impossible from a point.  This is the clause-level form of the "no fake
terminal" constraint. -/
theorem toClause_cover_not_subsingleton :
    ¬ Subsingleton (R.toClause).cover := by
  rw [toClause_cover]
  intro h
  have hsub : Subsingleton (S1331ClausePuncturedCurve l) :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := R.cover_surjective a
      obtain ⟨y, rfl⟩ := R.cover_surjective b
      rw [Subsingleton.elim x y]⟩
  exact S1331ClausePuncturedCurve_not_subsingleton l hsub

/-- The clause's cover map is a surjection onto the actual punctured carrier. -/
theorem toClause_cover_surjective :
    Function.Surjective (R.toClause).coverToPunctured :=
  R.cover_surjective

/-- The clause's cusp count is positive, as required. -/
theorem toClause_cuspCount_pos : 0 < (R.toClause).cuspCount :=
  R.cuspCount_pos

end S1331ResidualFields

/-! ## 5. The D6 gate is exactly clause nonemptiness

The clause type has no parameter depending on the arithmetic input.  Hence any
inhabitant of it closes `D6OrbicurveConstruction` at every prime, and the gate
at the actual S1280 input is exactly the nonemptiness of the clause type.  That
is precisely why a degenerate inhabitant must not be manufactured; this file
provides none. -/

/-- Any inhabitant of the clause type closes the D6 gate at every prime `l`. -/
theorem S1331D6Gate_of_nonempty_clause
    (h : Nonempty SourceOrbicurveClause.{0, 0, 0}) (l : PrimeGeFive) :
    D6OrbicurveConstruction.{0, 0, 0} l :=
  fun _ => h

/-- Conversely, the D6 gate at the actual S1280 arithmetic input yields an
inhabitant of the clause type at that input. -/
theorem S1331NonemptyClause_of_D6Gate (l : PrimeGeFive)
    (h : D6OrbicurveConstruction.{0, 0, 0} l) :
    Nonempty SourceOrbicurveClause.{0, 0, 0} :=
  h (S1280Arithmetic l)

/-- The D6 gate at the actual input is exactly the nonemptiness of the clause
type: it carries no further arithmetic content. -/
theorem S1331D6Gate_iff_nonempty_clause (l : PrimeGeFive) :
    D6OrbicurveConstruction.{0, 0, 0} l ↔ Nonempty SourceOrbicurveClause.{0, 0, 0} :=
  ⟨S1331NonemptyClause_of_D6Gate l, fun h => S1331D6Gate_of_nonempty_clause h l⟩

/-! ## 6. The stack-level terminal exclusion -/

/-- No D6 geometric realization uses the terminal constant fiber: its
`nondegenerate` field refutes the point fiber.  This is the production
"no fake terminal" theorem at the actual S1280 field. -/
theorem S1331NoTerminalFiber (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1280Arithmetic l).F) :
    D.fiber ≠
      InitialThetaSource.Definition31OrbicurveInstance.terminalConstantFiber
        (S1280Arithmetic l).F :=
  no_missingD6Realization_with_terminalConstantFiber
    (F := (S1280Arithmetic l).F) D

/-- The exact D6 object over the actual field: the nondegenerate etale-stack
geometric realization whose first field is the actual curve.  No inhabitant is
constructed in this file. -/
abbrev S1331D6Requirement (l : PrimeGeFive) : Type 1 :=
  MissingD6GeometricRealization (S1280Arithmetic l).F

/-- The first field of the D6 requirement is the curve whose point carrier is
the clause's exact first field.  The requirement type itself does not force its
first field to be the actual curve (an inhabitant carries an arbitrary
`PuncturedEllipticCurve F`); the exact binding is supplied by
`S1331ActualCurve` and `S1331ClauseCurve`, not by the requirement type. -/
theorem S1331D6Requirement_curve_carrier (l : PrimeGeFive) :
    S1331ClauseCurve l = (S1331ActualCurve l).curve.toProjective.Point := rfl

/-! ## 7. Axiom footprint -/

#print axioms S1331ClauseCurve_nonempty
#print axioms S1331ClauseCurve_not_subsingleton
#print axioms S1331ClauseCurve_ne_punit
#print axioms S1331ClausePuncturedCurve_not_subsingleton
#print axioms S1331ClauseCurveToPunctured_injective
#print axioms S1331ClauseCurveToPunctured_range
#print axioms S1331ExactSequenceBaseGroupGroup
#print axioms S1331ExactSequenceResidual.toExactSequence
#print axioms S1331ResidualFields.toClause_cover_not_subsingleton
#print axioms S1331D6Gate_iff_nonempty_clause
#print axioms S1331NoTerminalFiber

end LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit

end
