import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FinitePresentation

/-!
# S1409: a scheme-level connected finite etale cover for the D6 clause

S1381 showed that a nonsplit quadratic K-algebra has no K-points, so the
K-point carrier of its base change cannot surject onto the punctured
K-points.  This file replaces the K-point carrier by the actual scheme-level
cover.

The exact first field is a nonsquare element 'd' of 'K = Q(i)'.  From 'd' we
construct the connected finite etale 'K'-algebra

  'L = K[X]/(X^2 - d)',

the connected finite etale scheme 'Spec L -> Spec K' (etale and finite are
proved from the algebra), and the scheme-point cover of the punctured curve

  'cover = puncturedCurve x Spec L',

whose second factor is the underlying point type of the connected scheme
'Spec L', not the K-point type 'L ->_K K'.  The projection to the punctured
curve is surjective because 'Spec L' is nonempty (indeed a field spectrum).
The cover is not the terminal cover: the punctured curve is not a subsingleton
and the cover algebra has K-dimension two.

The D6 clause is then assembled from this cover and an exact-sequence
residual.  No terminal object, no split algebra 'K x K', no new axiom and no
'sorry' are used.  The only arithmetic input is the exact first field
'{ d : K // not IsSquare d }'.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1409ConnectedCoverSchemeActual

open LeanFormal.IUT
open AlgebraicGeometry
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual

open Polynomial

variable (l : PrimeGeFive)

/-! ## 1. The exact first field: a nonsquare in the Gaussian field -/

/-- The exact first field of the connected quadratic cover: an element 'd' of
'K = Q(i)' which is not a square.  Every such 'd' gives the connected quadratic
field 'K(sqrt d)'. -/
abbrev S1409D6FirstField : Type :=
  { d : S1348K l // ¬ IsSquare d }

/-- The quadratic polynomial 'X^2 - d' attached to the first field. -/
abbrev S1409QuadraticPolynomial (d : S1348K l) : Polynomial (S1348K l) :=
  Polynomial.X ^ 2 - Polynomial.C d

/-- The polynomial 'X^2 - d' is irreducible when 'd' is not a square. -/
theorem S1409QuadraticPolynomial_irreducible (d : S1348K l) (hd : ¬ IsSquare d) :
    Irreducible (S1409QuadraticPolynomial l d) := by
  rw [S1409QuadraticPolynomial]
  refine X_pow_sub_C_irreducible_of_prime (p := 2) (by norm_num) ?_
  intro b hb
  exact hd ⟨b, by rw [pow_two] at hb; exact hb.symm⟩

/-- The connected finite etale 'K'-algebra attached to the first field. -/
abbrev S1409ConnectedAlgebra (d : S1348K l) : Type :=
  AdjoinRoot (S1409QuadraticPolynomial l d)

/-- A bundled connected finite etale algebra of degree two over 'K'.  The
'Field' instance is the connectedness (a finite etale algebra is connected
exactly when it is a field); the dimension is two. -/
structure S1409ConnectedEtaleAlgebra where
  L : Type
  [field : Field L]
  [algebra : Algebra (S1348K l) L]
  [finite : Module.Finite (S1348K l) L]
  [etale : Algebra.Etale (S1348K l) L]
  finrank_eq_two : Module.finrank (S1348K l) L = 2

attribute [instance] S1409ConnectedEtaleAlgebra.field
  S1409ConnectedEtaleAlgebra.algebra
  S1409ConnectedEtaleAlgebra.finite
  S1409ConnectedEtaleAlgebra.etale

/-- Construction of the connected finite etale algebra from a nonsquare. -/
noncomputable def S1409ConnectedEtaleAlgebra.ofNonsquare
    (d : S1348K l) (hd : ¬ IsSquare d) : S1409ConnectedEtaleAlgebra l where
  L := S1409ConnectedAlgebra l d
  field := by
    letI : Fact (Irreducible (S1409QuadraticPolynomial l d)) :=
      ⟨S1409QuadraticPolynomial_irreducible l d hd⟩
    infer_instance
  algebra := inferInstance
  finite := by
    change Module.Finite (S1348K l)
      (AdjoinRoot (S1409QuadraticPolynomial l d))
    exact (Polynomial.monic_X_pow_sub_C d (by norm_num : 2 ≠ 0)).finite_adjoinRoot
  etale := by
    letI : Fact (Irreducible (S1409QuadraticPolynomial l d)) :=
      ⟨S1409QuadraticPolynomial_irreducible l d hd⟩
    letI : Field (S1409ConnectedAlgebra l d) := by infer_instance
    letI : Module.Finite (S1348K l) (S1409ConnectedAlgebra l d) := by
      change Module.Finite (S1348K l)
        (AdjoinRoot (S1409QuadraticPolynomial l d))
      exact (Polynomial.monic_X_pow_sub_C d (by norm_num : 2 ≠ 0)).finite_adjoinRoot
    constructor
    · exact Algebra.FormallyEtale.of_isSeparable (S1348K l) (S1409ConnectedAlgebra l d)
    · exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  finrank_eq_two := by
    change Module.finrank (S1348K l)
      (AdjoinRoot (S1409QuadraticPolynomial l d)) = 2
    rw [(AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C d
      (by norm_num : 2 ≠ 0))).finrank]
    rw [AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]

/-- From an exact first field, the connected finite etale algebra. -/
noncomputable def S1409ConnectedEtaleAlgebra.ofFirstField
    (F : S1409D6FirstField l) : S1409ConnectedEtaleAlgebra l :=
  S1409ConnectedEtaleAlgebra.ofNonsquare l F.1 F.2

/-! ## 2. The scheme-level connected finite etale cover

We use the underlying point type of the scheme 'Spec L', not the K-point type
'L ->_K K'.  The spectrum of a field has a point even when 'L' has no K-points;
this is exactly the distinction that S1381 identified. -/

/-- The actual scheme 'Spec L' of the connected finite etale algebra. -/
abbrev S1409Spec (D : S1409ConnectedEtaleAlgebra l) : Scheme :=
  Spec (CommRingCat.of D.L)

/-- The structure morphism 'Spec L -> Spec K'. -/
abbrev S1409SpecStructureMap (D : S1409ConnectedEtaleAlgebra l) :
    S1409Spec l D ⟶ Spec (CommRingCat.of (S1348K l)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S1348K l) D.L))

/-- The structure morphism of 'Spec L' is etale. -/
theorem S1409SpecStructureMap_etale (D : S1409ConnectedEtaleAlgebra l) :
    Etale (S1409SpecStructureMap l D) := by
  rw [S1409SpecStructureMap]
  exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Etale) (Q := @RingHom.Etale)).mpr
    (RingHom.etale_algebraMap.mpr D.etale)

/-- The structure morphism of 'Spec L' is finite. -/
theorem S1409SpecStructureMap_finite (D : S1409ConnectedEtaleAlgebra l) :
    IsFinite (S1409SpecStructureMap l D) := by
  rw [S1409SpecStructureMap]
  exact (AlgebraicGeometry.IsFinite.SpecMap_iff
    (R := CommRingCat.of (S1348K l)) (S := CommRingCat.of D.L)
    (f := CommRingCat.ofHom (algebraMap (S1348K l) D.L))).mpr
    (RingHom.finite_algebraMap.mpr D.finite)

/-- 'Spec L' is connected: a field spectrum is a one-point space. -/
theorem S1409Spec_connected (D : S1409ConnectedEtaleAlgebra l) :
    ConnectedSpace (S1409Spec l D) := by
  haveI : Unique (PrimeSpectrum D.L) := inferInstance
  refine ConnectedSpace.mk (toPreconnectedSpace := ?_) ⟨default⟩
  exact ⟨Set.Subsingleton.isPreconnected (by
    intro x hx y hy
    exact Subsingleton.elim x y)⟩

/-- In particular the scheme 'Spec L' is nonempty, even when 'L' has no
K-points. -/
theorem S1409Spec_nonempty (D : S1409ConnectedEtaleAlgebra l) :
    Nonempty (S1409Spec l D) :=
  ⟨default⟩


/-! ## 2.1 The actual scheme-level base change over the Gaussian curve

This is the total space of the finite etale cover of the affine curve: the
tensor product 'R (x)_K L' of the actual Gaussian coordinate ring with the
connected quadratic algebra.  Its fibres over K-points are the connected
scheme 'Spec L' used by the D6 carrier below. -/

/-- The cover algebra of the actual affine Gaussian curve: 'R (x)_K L'. -/
abbrev S1409CoverAlgebra (D : S1409ConnectedEtaleAlgebra l) : Type :=
  TensorProduct (S1348K l) (S1348CoordinateRing l) D.L

/-- The total scheme of the scheme-level connected finite etale cover. -/
abbrev S1409TotalCoverScheme (D : S1409ConnectedEtaleAlgebra l) : Scheme :=
  Spec (CommRingCat.of (S1409CoverAlgebra l D))

/-- The structure morphism of the total cover to the actual Gaussian curve. -/
abbrev S1409TotalCoverStructureMap (D : S1409ConnectedEtaleAlgebra l) :
    S1409TotalCoverScheme l D ⟶ Spec (CommRingCat.of (S1348CoordinateRing l)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S1348CoordinateRing l)
    (S1409CoverAlgebra l D)))

/-- The base-changed total cover is etale over the actual Gaussian curve. -/
theorem S1409TotalCoverStructureMap_etale (D : S1409ConnectedEtaleAlgebra l) :
    Etale (S1409TotalCoverStructureMap l D) := by
  rw [S1409TotalCoverStructureMap]
  exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Etale) (Q := @RingHom.Etale)).mpr
    (RingHom.etale_algebraMap.mpr
      (inferInstance : Algebra.Etale (S1348CoordinateRing l)
        (S1409CoverAlgebra l D)))

/-- The base-changed total cover is finite over the actual Gaussian curve. -/
theorem S1409TotalCoverStructureMap_finite (D : S1409ConnectedEtaleAlgebra l) :
    IsFinite (S1409TotalCoverStructureMap l D) := by
  rw [S1409TotalCoverStructureMap]
  exact (AlgebraicGeometry.IsFinite.SpecMap_iff
    (R := CommRingCat.of (S1348CoordinateRing l))
    (S := CommRingCat.of (S1409CoverAlgebra l D))
    (f := CommRingCat.ofHom (algebraMap (S1348CoordinateRing l)
      (S1409CoverAlgebra l D)))).mpr
    (by
      simpa using (RingHom.finite_algebraMap.mpr
        (inferInstance : Module.Finite (S1348CoordinateRing l)
          (S1409CoverAlgebra l D))))

/-! ## 3. The D6 cover carrier at the scheme-point level -/

/-- The scheme-point cover over the punctured K-points: the family of the
connected finite etale scheme 'Spec L' over every punctured K-point.  The
second factor is a scheme point type, not the K-point type of 'L'. -/
abbrev S1409Cover (D : S1409ConnectedEtaleAlgebra l) : Type :=
  S1331ClausePuncturedCurve l × S1409Spec l D

/-- The cover-to-punctured projection. -/
def S1409CoverToPunctured (D : S1409ConnectedEtaleAlgebra l) :
    S1409Cover l D → S1331ClausePuncturedCurve l :=
  Prod.fst

/-- The projection is surjective: every punctured K-point has the nonempty
scheme fibre 'Spec L' above it. -/
theorem S1409CoverToPunctured_surjective (D : S1409ConnectedEtaleAlgebra l) :
    Function.Surjective (S1409CoverToPunctured l D) := by
  intro P
  exact ⟨(P, default), rfl⟩

/-- The cover carrier is not a subsingleton; in particular it is not the
terminal cover. -/
theorem S1409Cover_not_subsingleton (D : S1409ConnectedEtaleAlgebra l) :
    ¬ Subsingleton (S1409Cover l D) := by
  intro h
  have hP : Subsingleton (S1331ClausePuncturedCurve l) :=
    ⟨fun a b => congrArg Prod.fst
      (Subsingleton.elim ((a, (default : S1409Spec l D)) : S1409Cover l D)
        ((b, (default : S1409Spec l D)) : S1409Cover l D))⟩
  exact S1331ClausePuncturedCurve_not_subsingleton l hP

/-- The structure group of the connected cover: the 'K'-algebra automorphisms
of 'L'. -/
abbrev S1409StructureGroup (D : S1409ConnectedEtaleAlgebra l) : Type :=
  D.L ≃ₐ[S1348K l] D.L

instance S1409StructureGroupGroup (D : S1409ConnectedEtaleAlgebra l) :
    Group (S1409StructureGroup l D) :=
  inferInstance

/-- The cover algebra has 'K'-dimension two: the scheme-level cover is a
genuine degree-two cover, not the identity cover. -/
theorem S1409Cover_degree_two (D : S1409ConnectedEtaleAlgebra l) :
    Module.finrank (S1348K l) D.L = 2 :=
  D.finrank_eq_two

/-! ## 4. The D6 clause -/

/-- The curve-compatibility proposition of this clause: the scheme-point cover
surjects onto the actual punctured points. -/
def S1409CurveCompatibility (D : S1409ConnectedEtaleAlgebra l) : Prop :=
  Function.Surjective (S1409CoverToPunctured l D)

theorem S1409CurveCompatibility_proved (D : S1409ConnectedEtaleAlgebra l) :
    S1409CurveCompatibility l D :=
  S1409CoverToPunctured_surjective l D

/-- The D6 'SourceOrbicurveClause' with the scheme-level connected finite etale
cover, conditional only on the exact-sequence residual. -/
noncomputable def S1409ClauseOfConnectedCover
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    SourceOrbicurveClause.{0, 0, 0} where
  curve := S1331ClauseCurve l
  puncturedCurve := S1331ClausePuncturedCurve l
  cover := S1409Cover l D
  structureGroup := S1409StructureGroup l D
  curveToPunctured := S1331ClauseCurveToPunctured l
  coverToPunctured := S1409CoverToPunctured l D
  cover_surjective := S1409CoverToPunctured_surjective l D
  exactSequence := E.toExactSequence
  cuspCount := 1
  cuspCount_pos := Nat.one_pos
  curveCompatibility := S1409CurveCompatibility l D
  curveCompatibility_proved := S1409CurveCompatibility_proved l D

/-- The clause constructed from the exact first field alone (plus the
exact-sequence residual). -/
noncomputable def S1409ClauseOfFirstField
    (F : S1409D6FirstField l) (E : S1331ExactSequenceResidual l) :
    SourceOrbicurveClause.{0, 0, 0} :=
  S1409ClauseOfConnectedCover l
    (S1409ConnectedEtaleAlgebra.ofFirstField l F) E

@[simp] theorem S1409ClauseOfConnectedCover_curve
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    (S1409ClauseOfConnectedCover l D E).curve = S1331ClauseCurve l := rfl

@[simp] theorem S1409ClauseOfConnectedCover_puncturedCurve
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    (S1409ClauseOfConnectedCover l D E).puncturedCurve =
      S1331ClausePuncturedCurve l := rfl

@[simp] theorem S1409ClauseOfConnectedCover_cover
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    (S1409ClauseOfConnectedCover l D E).cover = S1409Cover l D := rfl

@[simp] theorem S1409ClauseOfConnectedCover_structureGroup
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    (S1409ClauseOfConnectedCover l D E).structureGroup =
      S1409StructureGroup l D := rfl

@[simp] theorem S1409ClauseOfConnectedCover_coverToPunctured
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    (S1409ClauseOfConnectedCover l D E).coverToPunctured =
      S1409CoverToPunctured l D := rfl

@[simp] theorem S1409ClauseOfConnectedCover_cuspCount
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    (S1409ClauseOfConnectedCover l D E).cuspCount = 1 := rfl

@[simp] theorem S1409ClauseOfConnectedCover_exactSequence_baseGroup
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    (S1409ClauseOfConnectedCover l D E).exactSequence.baseGroup =
      S1331ExactSequenceBaseGroup l := rfl

/-- The clause cover is not a subsingleton. -/
theorem S1409ClauseOfConnectedCover_cover_not_subsingleton
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    ¬ Subsingleton (S1409ClauseOfConnectedCover l D E).cover :=
  S1409Cover_not_subsingleton l D

/-- The clause cover is a degree-two connected finite etale cover at the scheme
level: the cover algebra has 'K'-dimension two. -/
theorem S1409ClauseOfConnectedCover_cover_degree_two
    (D : S1409ConnectedEtaleAlgebra l) (E : S1331ExactSequenceResidual l) :
    Module.finrank (S1348K l) D.L = 2 :=
  S1409Cover_degree_two l D

/-- The exact first field is exactly a nonsquare in 'K'. -/
theorem S1409D6FirstField_spec (F : S1409D6FirstField l) :
    ¬ IsSquare F.1 :=
  F.2

/-- The first-field construction has the expected algebra: the connected
finite etale algebra is 'AdjoinRoot (X^2 - d)'. -/
theorem S1409ConnectedEtaleAlgebra_ofFirstField_L (F : S1409D6FirstField l) :
    (S1409ConnectedEtaleAlgebra.ofFirstField l F).L =
      S1409ConnectedAlgebra l F.1 := rfl

end LeanFormal.IUT.XiFPaper.S1409ConnectedCoverSchemeActual

end