/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import tmp.sheaf.xif.paper.S1493KSideTateTransportActual

/-!
# S2682: splitting the curve-indexed Tate uniformization contract

`CurveIndexedTateUniformization` (TateUniformizationContract.lean:88-127) bundles
exactly five fields:

* `canonicalIsElliptic`, `coordinateChange`, `realizesCurve` -- the
  coordinate/algebraic half: the canonical q-series is elliptic, an admissible
  Weierstrass variable change exists, and it realizes the selected
  base-changed curve;
* `pointUniformization`, `pointUniformization_galoisEquivariant` -- the
  point/analytic half: a Galois-equivariant group isomorphism from the
  q^Z-quotient of local units to the algebraic-closure points of the local
  curve.

This file records the split of that contract into the two corresponding
structures with *the same parameters*,

* `CurveIndexedTateUniformizationCoordinate` (three coordinate fields),
* `CurveIndexedTateUniformizationAnalytic` (two point fields, copied verbatim
  from the full contract), and the explicit gap proposition

* `CurveIndexedTateUniformizationAnalyticGap` :=
  `Nonempty (CurveIndexedTateUniformizationAnalytic ...)`.

The coordinate half at the source-designated section K-place is *constructed*
from the actual S1493 curve transport (which itself comes from the F-side
clause-(b) comparison transported along the actual completion map):

  `coordinateOfS1493 : CurveIndexedTateUniformizationCoordinate (kSideCurve T)
     (sectionKPlace T b) (sectionQ T b)`.

The analytic half is not constructed in this file.  The assembly theorem
`assemble` is purely structural, and the conditional theorems consume an
explicit analytic witness / gap hypothesis; no inhabitant of the analytic gap
is fabricated.  `split_iff` proves the equivalence

  `Nonempty (CurveIndexedTateUniformization X place parameter) ↔
     Nonempty (CurveIndexedTateUniformizationCoordinate X place parameter) ∧
     Nonempty (CurveIndexedTateUniformizationAnalytic X place parameter)`

in both directions, so the split is exact: the full contract has a point iff
both halves do, and neither direction manufactures analytic data from the
coordinate half.
-/

noncomputable section

namespace LeanFormal.IUT

universe u

/-- The coordinate/algebraic half of `CurveIndexedTateUniformization`: the
canonical q-series ellipticity, the admissible variable change over the
completion, and the curve realization.  The field types are copied verbatim
from the full contract. -/
structure CurveIndexedTateUniformizationCoordinate
    {F : Type u} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) where
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion place) parameter.q).IsElliptic
  coordinateChange :
    WeierstrassCurve.VariableChange
      (NumberFieldFinitePlace.Completion place)
  realizesCurve :
    coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q =
      (X.baseChange (NumberFieldFinitePlace.Completion place)).curve

/-- The point/analytic half of `CurveIndexedTateUniformization`: the
Galois-equivariant uniformization of the algebraic-closure points by the
q^Z-quotient of local units.  The two field types are copied verbatim from the
full contract (including the local `let`/`letI` binders). -/
structure CurveIndexedTateUniformizationAnalytic
    {F : Type u} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) where
  pointUniformization :
    let localCurve := X.baseChange (NumberFieldFinitePlace.Completion place)
    letI : localCurve.curve.IsElliptic := localCurve.isElliptic
    ((AlgebraicClosure (NumberFieldFinitePlace.Completion place))ˣ ⧸
      Subgroup.zpowers
        (NumberFieldFinitePlace.tateParameterUnit
          place parameter.q parameter.q_ne_zero)) ≃*
      Multiplicative localCurve.AlgebraicClosurePoint
  pointUniformization_galoisEquivariant :
    let localCurve := X.baseChange (NumberFieldFinitePlace.Completion place)
    letI : localCurve.curve.IsElliptic := localCurve.isElliptic
    ∀ (sigma :
        AlgebraicClosure (NumberFieldFinitePlace.Completion place) ≃ₐ[
          NumberFieldFinitePlace.Completion place]
        AlgebraicClosure (NumberFieldFinitePlace.Completion place))
      (x : (AlgebraicClosure
        (NumberFieldFinitePlace.Completion place))ˣ),
      pointUniformization
          (QuotientGroup.mk
            (Units.map sigma.toRingEquiv.toMonoidHom x)) =
        Multiplicative.ofAdd
          (localCurve.galoisActionOnPoint sigma
            (pointUniformization (QuotientGroup.mk x)).toAdd)

/-- The external analytic gap, as an explicit proposition: the point
uniformization half is inhabited.  This is the exact hypothesis under which the
full curve-indexed Tate uniformization is assembled from the actual coordinate
half; it is not itself inhabited in this file. -/
def CurveIndexedTateUniformizationAnalyticGap
    {F : Type u} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) : Prop :=
  Nonempty (CurveIndexedTateUniformizationAnalytic X place parameter)

end LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S2682CurveIndexedTateSplitActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual
open WeierstrassCurve

universe u

variable {l : PrimeGeFive}

/-! ## Projections of the full contract onto the two halves -/

/-- The coordinate half of an actual curve-indexed Tate uniformization. -/
noncomputable def coordinateOfUniformization
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (uniformization : CurveIndexedTateUniformization X place parameter) :
    CurveIndexedTateUniformizationCoordinate X place parameter where
  canonicalIsElliptic := uniformization.canonicalIsElliptic
  coordinateChange := uniformization.coordinateChange
  realizesCurve := uniformization.realizesCurve

/-- The analytic half of an actual curve-indexed Tate uniformization. -/
noncomputable def analyticOfUniformization
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (uniformization : CurveIndexedTateUniformization X place parameter) :
    CurveIndexedTateUniformizationAnalytic X place parameter where
  pointUniformization := uniformization.pointUniformization
  pointUniformization_galoisEquivariant :=
    uniformization.pointUniformization_galoisEquivariant

/-! ## The actual coordinate half at the source-designated section K-place -/

/-- The actual coordinate half at the section K-place, built from the S1493
curve transport: the canonical K-side Tate curve is elliptic, the F-side
coordinate change base changes to a K-side coordinate change, and it realizes
the base-changed K-side curve.  All three fields are the fields of
`s1493CurveTransport T b`; nothing is postulated. -/
noncomputable def coordinateOfS1493
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    CurveIndexedTateUniformizationCoordinate (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b) where
  canonicalIsElliptic := (s1493CurveTransport T b).canonicalIsElliptic
  coordinateChange := (s1493CurveTransport T b).coordinateChange
  realizesCurve := (s1493CurveTransport T b).realizesCurve

/-- The coordinate half at the section K-place is inhabited. -/
theorem nonempty_coordinate_atSection
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    Nonempty (CurveIndexedTateUniformizationCoordinate (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b)) :=
  ⟨coordinateOfS1493 T b⟩

/-! ## Assembly and the exact split -/

/-- Assemble the full curve-indexed Tate uniformization contract from its two
halves.  This is purely structural: no field is created. -/
noncomputable def assemble
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (coordinate : CurveIndexedTateUniformizationCoordinate X place parameter)
    (analytic : CurveIndexedTateUniformizationAnalytic X place parameter) :
    CurveIndexedTateUniformization X place parameter where
  canonicalIsElliptic := coordinate.canonicalIsElliptic
  coordinateChange := coordinate.coordinateChange
  realizesCurve := coordinate.realizesCurve
  pointUniformization := analytic.pointUniformization
  pointUniformization_galoisEquivariant :=
    analytic.pointUniformization_galoisEquivariant

/-- Forward direction of the split: a full contract yields both halves. -/
theorem coordinate_nonempty_of_nonempty
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (h : Nonempty (CurveIndexedTateUniformization X place parameter)) :
    Nonempty (CurveIndexedTateUniformizationCoordinate X place parameter) :=
  h.elim fun uniformization => ⟨coordinateOfUniformization uniformization⟩

/-- Forward direction of the split: a full contract yields the analytic half. -/
theorem analytic_nonempty_of_nonempty
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (h : Nonempty (CurveIndexedTateUniformization X place parameter)) :
    Nonempty (CurveIndexedTateUniformizationAnalytic X place parameter) :=
  h.elim fun uniformization => ⟨analyticOfUniformization uniformization⟩

/-- Backward direction of the split: the two halves assemble into the full
contract. -/
theorem nonempty_of_coordinate_nonempty_and_analytic_nonempty
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (coordinate : Nonempty (CurveIndexedTateUniformizationCoordinate X place parameter))
    (analytic : Nonempty (CurveIndexedTateUniformizationAnalytic X place parameter)) :
    Nonempty (CurveIndexedTateUniformization X place parameter) :=
  ⟨assemble coordinate.some analytic.some⟩

/-- The exact split: the full contract is inhabited iff both halves are. -/
theorem split_iff
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place} :
    Nonempty (CurveIndexedTateUniformization X place parameter) ↔
      Nonempty (CurveIndexedTateUniformizationCoordinate X place parameter) ∧
        Nonempty (CurveIndexedTateUniformizationAnalytic X place parameter) := by
  constructor
  · intro h
    exact ⟨coordinate_nonempty_of_nonempty h, analytic_nonempty_of_nonempty h⟩
  · rintro ⟨coordinate, analytic⟩
    exact nonempty_of_coordinate_nonempty_and_analytic_nonempty coordinate analytic

/-! ## Conditional construction from the actual coordinate half and the gap -/

/-- Conditional construction of the full contract from the actual coordinate
half and the explicit analytic gap.  The analytic witness is the hypothesis;
it is not constructed or postulated here. -/
noncomputable def full_of_coordinate_of_gap
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (coordinate : CurveIndexedTateUniformizationCoordinate X place parameter)
    (gap : CurveIndexedTateUniformizationAnalyticGap X place parameter) :
    CurveIndexedTateUniformization X place parameter :=
  assemble coordinate gap.some

/-- The same conditional construction at the source-designated section
K-place: the actual S1493 coordinate half plus the analytic gap yields the full
curve-indexed Tate uniformization. -/
noncomputable def fullAtSection_of_gap
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (gap : CurveIndexedTateUniformizationAnalyticGap (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b)) :
    CurveIndexedTateUniformization (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b) :=
  full_of_coordinate_of_gap (coordinateOfS1493 T b) gap

#print axioms coordinateOfS1493
#print axioms assemble
#print axioms split_iff
#print axioms full_of_coordinate_of_gap
#print axioms fullAtSection_of_gap

end LeanFormal.IUT.XiFPaper.S2682CurveIndexedTateSplitActual

end
