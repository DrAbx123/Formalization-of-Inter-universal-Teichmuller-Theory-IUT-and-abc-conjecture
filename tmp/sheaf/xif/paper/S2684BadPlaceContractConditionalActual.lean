/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tmp.sheaf.xif.paper.SourceQvCandidateActual
import tmp.sheaf.xif.paper.S2682CurveIndexedTateSplitActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceTateComparisonSynthesis

/-!
# S2684: conditional actual construction of the bad-place uniformization contract

The frozen D4 card `BadPlaceUniformizationContract P`
(`LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceTateComparisonSynthesis.lean:98-107`)
has exactly three fields:

* `parameter   : ∀ w hw, FinitePlaceQCandidate w`              -- Definition 3.1(c);
* `realization : ∀ w hw, CurveIndexedTateUniformization A.curve w (parameter w hw)`;
* `order_coprime : ∀ w hw, Nat.Coprime (parameter w hw).order l.value`.

This file constructs the contract **conditionally**, with the parameter being the
*actual* q-parameter selected by the closed source q_v theorem
(`SourceQvCandidateActual.sourceQvCandidate`, IUT I, Definition 3.1(c)), and the
realization assembled from the S2682 split of the one-way Tate uniformization
contract:

* `S2684BadPlaceUniformizationContract` takes, for every bad place, the actual
  split-multiplicative reduction (`sourceQvCandidate` needs it), the order
  coprimality, the coordinate half and the analytic half, and returns the
  contract.  Nothing is postulated: the realization is
  `S2682CurveIndexedTateSplitActual.assemble` applied to the two halves.

* The projection equations `..._parameter` and `..._realization` are `rfl`
  lemmas, and the D4 card consumer
  `BadPlaceUniformizationContract.toTateUniformizationCards` is unfolded
  (`..._toTateUniformizationCards_uniformization`): the card's uniformization at
  a bad place is exactly `assemble` of the supplied halves.  The Clause (b)
  consumer `sourceClauseB_of_uniformizationContract` is instantiated as
  `sourceClauseB_of_sourceQvCandidate`.

* The analytic gap variant `S2684BadPlaceUniformizationContractOfGap` takes the
  analytic half as the explicit proposition
  `CurveIndexedTateUniformizationAnalyticGap`; the conversion functions
  `S2684BadPlaceAnalyticGap_to_analytic` (`Classical.choice`) and
  `S2684BadPlaceAnalyticGap_of_analytic` relate it to the structure-valued
  hypothesis.  They cannot be packaged as a propositional `↔`, because the
  structure-valued family is a `Type`.

* The S1280 specialization `S2684S1280BadPlaceUniformizationContract` sets
  `A := S1280Arithmetic l`, `P := S1280Selection l`, and discharges `hsplit`
  with the **actual** reduction cards `S1280ReductionCards l` (the curve has
  split multiplicative reduction at the concrete Gaussian place above 5), so the
  only remaining inputs are order coprimality, the coordinate half and the
  analytic half at `sourceQvCandidate`
  (`S2684S1280BadPlaceUniformizationContractOfGap` takes the latter as the
  S2682 gap proposition).  Its parameter is, definitionally, the
  same lambda as `S2688S1280BadParameter`.

## Boundary: the section-place coordinate

`S2682CurveIndexedTateSplitActual.coordinateOfS1493` constructs the coordinate
half **at the source-designated section K-place**:

  `CurveIndexedTateUniformizationCoordinate (kSideCurve (T := T))
     (sectionKPlace T b) (sectionQ T b)`.

This is a genuine actual coordinate, and `S2684SectionPlaceCoordinate_actual`
below records it.  It is **not** an instance of the constructor's `hcoord` at
the S1280 bad place.  The mismatch is exact:

* the curve is `kSideCurve T : PuncturedEllipticCurve T.arithmetic.K`, while
  `hcoord` is about `(S1280Arithmetic l).curve :
  PuncturedEllipticCurve (S1280Arithmetic l).F`; identifying them needs a source
  native datum `T` with `T.arithmetic = S1280Arithmetic l` (recorded as the open
  bridge `S2683NativeS1280Data`; S2683's direct `cases` attempt on this equation
  fails by dependent elimination) together with the `K = F` base-change
  self-identification;
* the place is `sectionKPlace T b : NumberField.FinitePlace T.arithmetic.K`,
  while `hcoord` is about a place `w : NumberField.FinitePlace A.F`; for the
  S1280 selection the only bad place is `concreteGaussianFivePlace`, so the
  places can be compared only after the datum identification;
* the parameter is `sectionQ T b`, the clause-(B) witness parameter
  (`sectionFQ T b` transported by `completionMap`), while `hcoord` requires the
  closed source q_v choice `sourceQvCandidate`; the two are independent
  `Classical.choice`s, and only their `q`-values could ever be compared.

The coordinate structure only sees `parameter.q`; the transport lemma
`curveIndexedTateUniformizationCoordinate_of_q_eq` below makes that precise.
No general `hcoord` is fabricated: `S2684S1280BadPlaceUniformizationContract`
keeps `hcoord` and `hanalytic` as explicit hypotheses.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2684BadPlaceContractConditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.XiFPaper.SourceQvCandidateActual
open LeanFormal.IUT.XiFPaper.S2682CurveIndexedTateSplitActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

universe u

variable {l : PrimeGeFive}

/-! ## 1. The conditional constructor -/

/-- Conditional construction of the bad-place uniformization contract from the
actual source q_v parameter and the S2682 split of the one-way Tate
uniformization contract.

* `parameter` is `sourceQvCandidate` (the closed source q_v choice), not an
  arbitrary DVR uniformizer;
* `realization` is `assemble` of the coordinate half and the analytic half at
  that parameter (the split is exact by S2682's `split_iff`);
* `order_coprime` is the supplied prime-to-`l` coprimality.

No Tate uniformization theorem is claimed: the coordinate and analytic halves
are explicit hypotheses.  `hsplit` is needed because `sourceQvCandidate` is
selected from the split-multiplicative closed source q_v theorem. -/
noncomputable def S2684BadPlaceUniformizationContract
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalytic A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw))) :
    BadPlaceUniformizationContract P where
  parameter := fun w hw =>
    sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)
  realization := fun w hw =>
    S2682CurveIndexedTateSplitActual.assemble (hcoord w hw) (hanalytic w hw)
  order_coprime := horder

/-! ## 2. Projection equations (definitional) -/

/-- The parameter field of the conditional contract is exactly the actual
closed-source q_v candidate. -/
@[simp] theorem S2684BadPlaceUniformizationContract_parameter
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalytic A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    (S2684BadPlaceUniformizationContract P hsplit horder hcoord hanalytic).parameter w hw =
      sourceQvCandidate (F := A.F) w A.curve (hsplit w hw) :=
  rfl

/-- The realization field of the conditional contract is exactly `assemble` of
the supplied coordinate and analytic halves. -/
@[simp] theorem S2684BadPlaceUniformizationContract_realization
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalytic A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    (S2684BadPlaceUniformizationContract P hsplit horder hcoord hanalytic).realization w hw =
      S2682CurveIndexedTateSplitActual.assemble (hcoord w hw) (hanalytic w hw) :=
  rfl

/-! ## 3. The D4 card consumer -/

/-- The D4 Tate-identification card built from the conditional contract has
the actual source q_v parameter. -/
@[simp] theorem S2684BadPlaceUniformizationContract_toTateUniformizationCards_parameter
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalytic A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    ((S2684BadPlaceUniformizationContract P hsplit horder hcoord hanalytic).toTateUniformizationCards).parameter
        w hw =
      sourceQvCandidate (F := A.F) w A.curve (hsplit w hw) :=
  rfl

/-- The comparison of the D4 card at a bad place is the comparison extracted
from `assemble`, i.e. its uniformization is literally the assembled contract. -/
theorem S2684BadPlaceUniformizationContract_toTateUniformizationCards_uniformization
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalytic A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    (((S2684BadPlaceUniformizationContract P hsplit horder hcoord hanalytic).toTateUniformizationCards).comparison
        w hw).toUniformization =
      S2682CurveIndexedTateSplitActual.assemble (hcoord w hw) (hanalytic w hw) :=
  BadPlaceUniformizationContract.toTateUniformizationCards_uniformization
    (S2684BadPlaceUniformizationContract P hsplit horder hcoord hanalytic) w hw

/-- Clause (b) assembly consuming the conditional contract: given the
sign-quotient bad set identification, the multiplicative-reduction function and
residue-characteristic coprimality, the source Clause (b) record is obtained
from the actual q_v parameter and the S2682 split. -/
theorem sourceClauseB_of_sourceQvCandidate
    {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A}
    {CA : SourceClauseA A S}
    (P : SourcePlaceSelection A)
    (hV_mod_bad : S.V_mod_bad = P.V_mod_bad)
    (multiplicative : ∀ (w : NumberField.FinitePlace A.F),
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt w)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalytic A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (residueCoprime : ∀ (w : NumberField.FinitePlace A.F),
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ S.V_mod_bad →
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) w))) :
    SourceClauseB A S CA :=
  sourceClauseB_of_uniformizationContract P hV_mod_bad multiplicative
    (S2684BadPlaceUniformizationContract P hsplit horder hcoord hanalytic)
    residueCoprime

/-! ## 4. Analytic-gap variant -/

/-- The analytic half as a proposition-valued hypothesis over the bad places:
the S2682 analytic gap at the actual source q_v parameter. -/
def S2684BadPlaceAnalyticGap
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w) : Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    CurveIndexedTateUniformizationAnalyticGap A.curve w
      (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw))

/-- The gap form implies the structure-valued analytic half, by
`Classical.choice`.  (The two forms cannot be related by a propositional
`↔`: the structure-valued family is a `Type`, not a `Prop`.) -/
noncomputable def S2684BadPlaceAnalyticGap_to_analytic
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (hgap : S2684BadPlaceAnalyticGap P hsplit) :
    ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalytic A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)) :=
  fun w hw => Classical.choice (hgap w hw)

/-- The structure-valued analytic half gives the gap proposition. -/
theorem S2684BadPlaceAnalyticGap_of_analytic
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (hanalytic : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationAnalytic A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw))) :
    S2684BadPlaceAnalyticGap P hsplit :=
  fun w hw => ⟨hanalytic w hw⟩

/-- The conditional constructor with the analytic half taken as the explicit
S2682 gap proposition. -/
noncomputable def S2684BadPlaceUniformizationContractOfGap
    {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A)
    (hsplit : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      A.curve.HasSplitMultiplicativeReductionAt w)
    (horder : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace A.F)
      (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformizationCoordinate A.curve w
        (sourceQvCandidate (F := A.F) w A.curve (hsplit w hw)))
    (hgap : S2684BadPlaceAnalyticGap P hsplit) :
    BadPlaceUniformizationContract P :=
  S2684BadPlaceUniformizationContract P hsplit horder hcoord
    (fun w hw => Classical.choice (hgap w hw))

/-! ## 5. The S1280 specialization

`A := S1280Arithmetic l = concreteGaussianInitialThetaArithmeticData l`,
`P := S1280Selection l`, and `hsplit` is discharged by the actual reduction
cards, whose split-multiplicative field comes from the concrete curve over
`Q(i)` at the place above `5`. -/

/-- The conditional bad-place uniformization contract for the actual S1280
selection: the q parameter is the closed source q_v candidate, the split
multiplicative reduction is the actual `S1280ReductionCards` field, and the
realization is assembled from the coordinate and analytic halves. -/
noncomputable def S2684S1280BadPlaceUniformizationContract (l : PrimeGeFive)
    (horder : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationCoordinate (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationAnalytic (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw))) :
    BadPlaceUniformizationContract (S1280Selection l) :=
  S2684BadPlaceUniformizationContract (S1280Selection l)
    (fun w hw => (S1280ReductionCards l).splitMultiplicativeReduction w hw)
    horder hcoord hanalytic

/-- The S1280 specialization with the analytic half as the explicit S2682
gap proposition instead of the structure. -/
noncomputable def S2684S1280BadPlaceUniformizationContractOfGap (l : PrimeGeFive)
    (horder : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationCoordinate (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)))
    (hgap : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationAnalyticGap (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw))) :
    BadPlaceUniformizationContract (S1280Selection l) :=
  S2684BadPlaceUniformizationContractOfGap (S1280Selection l)
    (fun w hw => (S1280ReductionCards l).splitMultiplicativeReduction w hw)
    horder hcoord hgap

/-- The S1280 parameter field is the actual closed source q_v candidate. -/
@[simp] theorem S2684S1280BadPlaceUniformizationContract_parameter
    (l : PrimeGeFive)
    (horder : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationCoordinate (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationAnalytic (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)))
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad) :
    (S2684S1280BadPlaceUniformizationContract l horder hcoord hanalytic).parameter w hw =
      sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
        ((S1280ReductionCards l).splitMultiplicativeReduction w hw) :=
  rfl

/-- The S1280 realization field is exactly `assemble` of the supplied halves. -/
@[simp] theorem S2684S1280BadPlaceUniformizationContract_realization
    (l : PrimeGeFive)
    (horder : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationCoordinate (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationAnalytic (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)))
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad) :
    (S2684S1280BadPlaceUniformizationContract l horder hcoord hanalytic).realization w hw =
      S2682CurveIndexedTateSplitActual.assemble (hcoord w hw) (hanalytic w hw) :=
  rfl

/-- The S1280 D4 card consumer: the uniformization of the card at the bad place
is the assembled contract. -/
theorem S2684S1280BadPlaceUniformizationContract_toTateUniformizationCards_uniformization
    (l : PrimeGeFive)
    (horder : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      Nat.Coprime
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)).order l.value)
    (hcoord : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationCoordinate (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)))
    (hanalytic : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
      (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad),
      CurveIndexedTateUniformizationAnalytic (S1280Arithmetic l).curve w
        (sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
          ((S1280ReductionCards l).splitMultiplicativeReduction w hw)))
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad) :
    (((S2684S1280BadPlaceUniformizationContract l horder hcoord hanalytic).toTateUniformizationCards).comparison
        w hw).toUniformization =
      S2682CurveIndexedTateSplitActual.assemble (hcoord w hw) (hanalytic w hw) :=
  S2684BadPlaceUniformizationContract_toTateUniformizationCards_uniformization
    (S1280Selection l)
    (fun w hw => (S1280ReductionCards l).splitMultiplicativeReduction w hw)
    horder hcoord hanalytic w hw

/-! ## 6. Transport of the two halves along equality of the q parameter -/

/-- The coordinate half only sees `parameter.q`: equal q-values give the same
coordinate structure.  (This is the precise form in which a section-place
coordinate could serve a different q-candidate.) -/
def curveIndexedTateUniformizationCoordinate_of_q_eq
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {p p' : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (hp : p.q = p'.q)
    (c : CurveIndexedTateUniformizationCoordinate X place p) :
    CurveIndexedTateUniformizationCoordinate X place p' where
  canonicalIsElliptic := hp ▸ c.canonicalIsElliptic
  coordinateChange := c.coordinateChange
  realizesCurve := hp ▸ c.realizesCurve

/-- The analytic half transports along full equality of the parameter (needed
because `pointUniformization` mentions the proof field `q_ne_zero`). -/
def curveIndexedTateUniformizationAnalytic_of_parameter_eq
    {F : Type u} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F}
    {place : NumberField.FinitePlace F}
    {p p' : NumberFieldFinitePlace.FinitePlaceQCandidate place}
    (hpp : p = p')
    (a : CurveIndexedTateUniformizationAnalytic X place p) :
    CurveIndexedTateUniformizationAnalytic X place p' :=
  hpp ▸ a

/-! ## 7. The actual section-place coordinate and its exact mismatch -/

section SectionPlace

open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1493KSideTateTransportActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

/-- The actual section-place coordinate half from S1493, restated at its exact
datum: it lives at `(kSideCurve T, sectionKPlace T b, sectionQ T b)`, not at the
S1280 bad place of the constructor. -/
theorem S2684SectionPlaceCoordinate_actual
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    Nonempty
      (CurveIndexedTateUniformizationCoordinate (kSideCurve (T := T))
        (sectionKPlace T b) (sectionQ T b)) :=
  S2682CurveIndexedTateSplitActual.nonempty_coordinate_atSection T b

end SectionPlace

/-! ## 8. Axiom checks -/

#print axioms S2684BadPlaceUniformizationContract
#print axioms S2684BadPlaceUniformizationContract_parameter
#print axioms S2684BadPlaceUniformizationContract_realization
#print axioms S2684BadPlaceUniformizationContract_toTateUniformizationCards_uniformization
#print axioms sourceClauseB_of_sourceQvCandidate
#print axioms S2684BadPlaceUniformizationContractOfGap
#print axioms S2684BadPlaceAnalyticGap_to_analytic
#print axioms S2684BadPlaceAnalyticGap_of_analytic
#print axioms S2684S1280BadPlaceUniformizationContract
#print axioms S2684S1280BadPlaceUniformizationContractOfGap
#print axioms S2684S1280BadPlaceUniformizationContract_parameter
#print axioms S2684S1280BadPlaceUniformizationContract_toTateUniformizationCards_uniformization
#print axioms curveIndexedTateUniformizationCoordinate_of_q_eq
#print axioms curveIndexedTateUniformizationAnalytic_of_parameter_eq
#print axioms S2684SectionPlaceCoordinate_actual
#print axioms sourceQvCandidate

end LeanFormal.IUT.XiFPaper.S2684BadPlaceContractConditionalActual

end
