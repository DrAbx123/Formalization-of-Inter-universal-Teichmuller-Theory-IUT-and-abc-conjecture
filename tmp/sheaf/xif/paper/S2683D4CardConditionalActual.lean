/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tmp.sheaf.xif.paper.SourceQvCandidateActual
import tmp.sheaf.xif.paper.S2682CurveIndexedTateSplitActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization

/-!
# S2683: the conditional D4 bad-place Tate-uniformization card

This file assembles the frozen D4 card of
`InitialThetaSource.PlaceQParameterUniformization.BadPlaceTateUniformizationCards`
from the *actual* source q-parameter `sourceQvCandidate` and from the S2682
split of the curve-indexed Tate uniformization.

## What is constructed

* `S2683D4Card` is the conditional card.  Its `parameter` field is, by
  definition, the actual `sourceQvCandidate` selected by the closed source
  q_v theorem at every finite place lying over the bad moduli set; no
  arbitrary DVR choice is made.  The genuinely missing inputs are kept as
  explicit hypotheses:

  - `hsplit : ∀ w hw, A.curve.HasSplitMultiplicativeReductionAt w`,
  - `hcomp : ∀ w hw, TateCurveComparison A.curve w
      (sourceQvCandidate w A.curve (hsplit w hw))`,
  - `horder : ∀ w hw, Nat.Coprime
      (sourceQvCandidate w A.curve (hsplit w hw)).order l.value`.

* `parameter_is_sourceQvCandidate` (and its pointwise `simp` form) records,
  by `rfl`, that the card parameter really is `sourceQvCandidate`.

* `tateCurveComparisonOfSplit` assembles a full `TateCurveComparison` from
  the S2682 coordinate half
  (`CurveIndexedTateUniformizationCoordinate`) together with the S2682
  analytic half (`CurveIndexedTateUniformizationAnalytic`).  The coordinate
  half has exactly the first three fields of `TateCurveComparison`
  (`canonicalIsElliptic`, `coordinateChange`, `realizesCurve`), and the
  analytic half has exactly the two fields of the nested
  `TatePointComparison` (`pointEquiv`, `galois_naturality`).  The `letI`
  binders in the S2682 analytic field types are unused by
  `PuncturedEllipticCurve.AlgebraicClosurePoint` and
  `PuncturedEllipticCurve.galoisActionOnPoint`, so the types are
  definitionally equal and the assembly is field-for-field.

* `S2683D4CardOfSplit` is the conditional card whose comparison hypothesis is
  replaced by the two S2682 halves: an actual coordinate half and the
  explicit analytic gap proposition
  `CurveIndexedTateUniformizationAnalyticGap`.  The gap is a hypothesis; no
  inhabitant of it is fabricated.

* `coordinateOfTateCurveComparison` and
  `analyticOfTateCurveComparison` project a full `TateCurveComparison` onto
  the two S2682 halves, and
  `tateCurveComparisonOfSplit_coordinateOf` shows the assembly is inverse to
  the projection.  Thus the split of the comparison used here is exact, not
  a weakening.

No instance of the D4 card is asserted: every construction below is
conditional on the displayed hypotheses, and every definition is a
kernel-checked structure assembly from those hypotheses.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.XiFPaper.SourceQvCandidateActual
open LeanFormal.IUT.XiFPaper.S2682CurveIndexedTateSplitActual

universe u

namespace LeanFormal.IUT.XiFPaper.S2683D4CardConditionalActual

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {P : SourcePlaceSelection A}

/-! ## The conditional D4 card with the actual q_v parameter -/

/-- The D4 bad-place Tate-uniformization card assembled conditionally from the
actual source q-parameter `sourceQvCandidate`.

The `parameter` field is the actual source q_v candidate (no arbitrary
choice), while the multiplicative-reduction hypothesis, the Tate-curve
comparison, and the prime-to-`l` order coprimality are kept as the explicit
hypotheses `hsplit`, `hcomp`, and `horder`. -/
noncomputable def S2683D4Card
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (hcomp : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      TateCurveComparison A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value) :
    BadPlaceTateUniformizationCards P where
  parameter := fun w hw =>
    sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)
  comparison := hcomp
  order_coprime := horder

/-- The card's parameter is exactly the actual `sourceQvCandidate`; this holds
by definition, not by an extra choice. -/
theorem parameter_is_sourceQvCandidate
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (hcomp : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      TateCurveComparison A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value) :
    (S2683D4Card (P := P) hsplit hcomp horder).parameter =
      (fun (w : NumberField.FinitePlace A.F)
        (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) =>
        sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)) :=
  rfl

/-- Pointwise form of `parameter_is_sourceQvCandidate`. -/
@[simp] theorem S2683D4Card_parameter_apply
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (hcomp : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      TateCurveComparison A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    (S2683D4Card (P := P) hsplit hcomp horder).parameter w hw =
      sourceQvCandidate (F := A.F) w A.curve (hsplit w hw) :=
  rfl

/-! ## Splitting the Tate-curve comparison along S2682 -/

section Split

variable {F : Type u} [Field F] [NumberField F]
variable {X : PuncturedEllipticCurve F}
variable {place : NumberField.FinitePlace F}
variable {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}

/-- Assemble the full `TateCurveComparison` from the two S2682 halves.

The coordinate half supplies `canonicalIsElliptic`, `coordinateChange`, and
`realizesCurve`; the analytic half supplies `pointEquiv` and
`galois_naturality` through its `pointUniformization` and
`pointUniformization_galoisEquivariant` fields.  Both halves have exactly the
types of the corresponding `TateCurveComparison` fields, so this is a
field-for-field assembly. -/
noncomputable def tateCurveComparisonOfSplit
    (coordinate : CurveIndexedTateUniformizationCoordinate X place parameter)
    (analytic : CurveIndexedTateUniformizationAnalytic X place parameter) :
    TateCurveComparison X place parameter where
  canonicalIsElliptic := coordinate.canonicalIsElliptic
  coordinateChange := coordinate.coordinateChange
  realizesCurve := coordinate.realizesCurve
  points :=
    { pointEquiv := analytic.pointUniformization
      galois_naturality := analytic.pointUniformization_galoisEquivariant }

/-- The coordinate half of a full `TateCurveComparison`. -/
noncomputable def coordinateOfTateCurveComparison
    (comparison : TateCurveComparison X place parameter) :
    CurveIndexedTateUniformizationCoordinate X place parameter where
  canonicalIsElliptic := comparison.canonicalIsElliptic
  coordinateChange := comparison.coordinateChange
  realizesCurve := comparison.realizesCurve

/-- The analytic half of a full `TateCurveComparison`. -/
noncomputable def analyticOfTateCurveComparison
    (comparison : TateCurveComparison X place parameter) :
    CurveIndexedTateUniformizationAnalytic X place parameter where
  pointUniformization := comparison.points.pointEquiv
  pointUniformization_galoisEquivariant := comparison.points.galois_naturality

/-- The assembly from the two S2682 halves is inverse to the projection: the
split used in this file is exact. -/
theorem tateCurveComparisonOfSplit_coordinateOf
    (comparison : TateCurveComparison X place parameter) :
    tateCurveComparisonOfSplit
        (coordinateOfTateCurveComparison comparison)
        (analyticOfTateCurveComparison comparison) = comparison := by
  cases comparison with
  | mk canonicalIsElliptic coordinateChange realizesCurve points =>
    cases points with
    | mk pointEquiv galois_naturality => rfl

/-- A full `TateCurveComparison` yields the explicit S2682 analytic gap. -/
theorem analyticGap_of_tateCurveComparison
    (comparison : TateCurveComparison X place parameter) :
    CurveIndexedTateUniformizationAnalyticGap X place parameter :=
  ⟨analyticOfTateCurveComparison comparison⟩

/-- A full `TateCurveComparison` yields the S2682 coordinate half. -/
theorem nonempty_coordinate_of_tateCurveComparison
    (comparison : TateCurveComparison X place parameter) :
    Nonempty (CurveIndexedTateUniformizationCoordinate X place parameter) :=
  ⟨coordinateOfTateCurveComparison comparison⟩

end Split

/-! ## The conditional card from the coordinate half and the analytic gap -/

/-- The conditional D4 card in its split form: the actual parameter
`sourceQvCandidate` is unchanged, while the full comparison hypothesis is
replaced by

* the actual coordinate half
  `CurveIndexedTateUniformizationCoordinate` at every bad place, and
* the explicit S2682 analytic gap
  `CurveIndexedTateUniformizationAnalyticGap` at every bad place.

The gap is a hypothesis; no analytic data is constructed here. -/
noncomputable def S2683D4CardOfSplit
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (hcoordinate : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hgap : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalyticGap A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value) :
    BadPlaceTateUniformizationCards P where
  parameter := fun w hw =>
    sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)
  comparison := fun w hw =>
    tateCurveComparisonOfSplit (hcoordinate w hw) (hgap w hw).some
  order_coprime := horder

/-- The split card's parameter is again exactly the actual
`sourceQvCandidate`. -/
theorem parameter_is_sourceQvCandidate_of_split
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (hcoordinate : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hgap : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalyticGap A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value) :
    (S2683D4CardOfSplit (P := P) hsplit hcoordinate hgap horder).parameter =
      (fun (w : NumberField.FinitePlace A.F)
        (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) =>
        sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)) :=
  rfl

/-- Every comparison of the split card is a full `TateCurveComparison`
assembled from the supplied coordinate half and analytic gap. -/
theorem S2683D4CardOfSplit_comparison_apply
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (hcoordinate : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hgap : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalyticGap A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    (S2683D4CardOfSplit (P := P) hsplit hcoordinate hgap horder).comparison w hw =
      tateCurveComparisonOfSplit (hcoordinate w hw) (hgap w hw).some :=
  rfl

/-! ## Axiom audit -/

#print axioms S2683D4Card
#print axioms parameter_is_sourceQvCandidate
#print axioms S2683D4Card_parameter_apply
#print axioms tateCurveComparisonOfSplit
#print axioms coordinateOfTateCurveComparison
#print axioms analyticOfTateCurveComparison
#print axioms tateCurveComparisonOfSplit_coordinateOf
#print axioms analyticGap_of_tateCurveComparison
#print axioms nonempty_coordinate_of_tateCurveComparison
#print axioms S2683D4CardOfSplit
#print axioms parameter_is_sourceQvCandidate_of_split
#print axioms S2683D4CardOfSplit_comparison_apply

end LeanFormal.IUT.XiFPaper.S2683D4CardConditionalActual
