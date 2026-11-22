import tmp.sheaf.xif.paper.S1266SourceInd3Actual
import tmp.sheaf.xif.paper.S1270NontrivialCapsuleActual

/-!
# S1297: the actual Ind3 log-shell carrier

S1266SourceInd3Actual constructs the actual (Ind3) times-mu stage data and
names the exact first missing source datum: the analytic log-shell carrier
`Ind3LogShellCarrier`, whose first field `shell` is the first field of
`SourceProcessionCapsule.LogShellFamily`.  S1270NontrivialCapsuleActual
constructs a non-PUnit actual capsule contract.  Its `actualLogShellFamily`
assigns to every capsule label, rational valuation and actual finite place the
rational span of the actual local log-shell datum.

This file uses that family to fill the first field.

## What is constructed

* `ActualPlaceTotal` is the total actual place type `(vQ, v)` of S1270.
* `actualInd3LogShellCarrier` is a genuine `Ind3LogShellCarrier` over that
  actual place type; its `shell` field is literally
  `(actualLogShellFamily I j).Shell i vQ v`.  No PUnit or arbitrary module is
  used.
* `actualInd3LogShellCarrierAt` is the same carrier on one valuation fiber.
* `ind3ToLogShellFamily` is the universe-correct version of S1266's
  `Ind3LogShellCarrier.toLogShellFamily`.  S1266's own version fixes the place
  type in `Type 0`; the actual finite-place fibers live in `Type ua`, so the
  generalized version is the one that applies.  Applying it to the carrier
  gives exactly S1270's `actualLogShellFamily`, hence exactly the contract's
  `logShell` field.
* `actualInd3LogShellCarrier_shell_nontrivial` proves each actual shell has at
  least two elements (0 and 1); it is not a one-point/PUnit model.

## Attachment to S1266's Ind3 stage and poly-isomorphism

S1266's `sourceInd3StageData` and `ind3StagePolyIso` are actual at the source
place type `V`.  The actual log-shell carrier is indexed by the actual places.
`ActualInd3SourceDatum` bundles the two actual pieces (with exact
projections); `ActualInd3SourceDatumAtV` does the same on `V` given the exact
place comparison.  The bundle does not assert a compatibility between the
times-mu stage and the analytic log-shell module: S1266 records that these are
different levels, and the one-sided (Ind3) comparison must come from the
log-shell/Kummer side.

## Exact first field for the ambient source place type `V`

`Ind3PlaceComparison` is the map `V -> (vQ, v)` needed to fill the carrier's
first field on `V`.  `Ind3PlaceComparisonRequired` is the corresponding open
proposition.  No inhabitant is constructed or asserted; in particular no
arbitrary constant place map is used.  Given such a map,
`actualInd3LogShellCarrierOfMap` fills the first field and
`ind3LogShellCarrierRequired_of_placeMap` closes S1266's
`Ind3LogShellCarrierRequired` at `V`.

No sorry, no new axiom, no PUnit, no one-point model.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1297Ind3LogShellActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.XiFPaper.S1270NontrivialCapsuleActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

universe ua uv upi umon ui uVQ uPlace uR uShell

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The total actual place type and the carrier -/

/-- The total actual place type of S1270: a rational valuation together with an
actual finite place over it. -/
abbrev ActualPlaceTotal : Type (max 0 ua) := (vQ : ActualValuation) × actualPlace I vQ

/-- The actual Ind3 log-shell carrier over the total actual place type.  Its
first field is literally the first field of S1270's `actualLogShellFamily`. -/
noncomputable def actualInd3LogShellCarrier (j : Nat) :
    Ind3LogShellCarrier.{max 0 ua, 0, ua} (V := ActualPlaceTotal I) (R := ℚ) j where
  shell i x := (actualLogShellFamily I j).Shell i x.1 x.2
  addCommMonoid i x := (actualLogShellFamily I j).addCommMonoid i x.1 x.2
  module i x := (actualLogShellFamily I j).module i x.1 x.2

/-- The first field of the carrier is literally the first field of the actual
log-shell family. -/
theorem actualInd3LogShellCarrier_shell (j : Nat) (i : Capsule j)
    (x : ActualPlaceTotal I) :
    (actualInd3LogShellCarrier I j).shell i x =
      (actualLogShellFamily I j).Shell i x.1 x.2 := rfl

/-- The carrier is an actual inhabitant of S1266's open carrier requirement at
the actual place type. -/
theorem actualInd3LogShellCarrierRequired_actual (j : Nat) :
    Ind3LogShellCarrierRequired.{max 0 ua, 0, ua}
      (V := ActualPlaceTotal I) (R := ℚ) j :=
  ⟨actualInd3LogShellCarrier I j⟩

/-- The fiberwise carrier at one rational valuation. -/
noncomputable def actualInd3LogShellCarrierAt (vQ : ActualValuation) (j : Nat) :
    Ind3LogShellCarrier.{ua, 0, ua} (V := actualPlace I vQ) (R := ℚ) j where
  shell i v := (actualLogShellFamily I j).Shell i vQ v
  addCommMonoid i v := (actualLogShellFamily I j).addCommMonoid i vQ v
  module i v := (actualLogShellFamily I j).module i vQ v

theorem actualInd3LogShellCarrierAt_shell (vQ : ActualValuation) (j : Nat)
    (i : Capsule j) (v : actualPlace I vQ) :
    (actualInd3LogShellCarrierAt I vQ j).shell i v =
      (actualLogShellFamily I j).Shell i vQ v := rfl

/-- The total carrier restricts to the fiber carrier. -/
theorem actualInd3LogShellCarrier_restrict (j : Nat) (i : Capsule j)
    (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualInd3LogShellCarrier I j).shell i ⟨vQ, v⟩ =
      (actualInd3LogShellCarrierAt I vQ j).shell i v := rfl

/-! ## 2. Exactness of the first field at the log-shell-family level -/

/-- Universe-correct form of S1266's `Ind3LogShellCarrier.toLogShellFamily`.
S1266's version fixes `Place : VQ -> Type` in `Type 0`; the actual finite-place
fibers live in `Type ua`. -/
noncomputable def ind3ToLogShellFamily
    {R : Type uR} [CommSemiring R] {j : Nat}
    (L : Ind3LogShellCarrier.{uv, uR, uShell} (V := V) (R := R) j)
    {VQ : Type uVQ} (Place : VQ → Type uPlace) (p : ∀ vQ, Place vQ → V) :
    LogShellFamily.{uR, uVQ, uPlace, uShell} R Place j where
  Shell i vQ v := L.shell i (p vQ v)
  addCommMonoid i vQ v := L.addCommMonoid i (p vQ v)
  module i vQ v := L.module i (p vQ v)

/-- The actual log-shell family induced by the actual carrier. -/
noncomputable def actualInd3LogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℚ (actualPlace I) j :=
  ind3ToLogShellFamily (actualInd3LogShellCarrier I j) (actualPlace I)
    (fun vQ v => ⟨vQ, v⟩)

theorem actualInd3LogShellFamily_shell (j : Nat) (i : Capsule j)
    (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualInd3LogShellFamily I j).Shell i vQ v =
      (actualLogShellFamily I j).Shell i vQ v := rfl

/-- The induced family is exactly S1270's actual family. -/
theorem actualInd3LogShellFamily_eq_actualLogShellFamily (j : Nat) :
    actualInd3LogShellFamily I j = actualLogShellFamily I j := rfl

/-- Hence its first field is exactly the contract's log-shell field. -/
theorem actualInd3LogShellFamily_eq_contract_logShell
    (j : Fin (capsuleLevels l)) :
    actualInd3LogShellFamily I j.val = (actualCapsuleContract I).logShell j := by
  rw [actualCapsuleContract_logShell]
  exact actualInd3LogShellFamily_eq_actualLogShellFamily I j.val

/-- The literal first-field form at the contract's capsule level. -/
theorem actualInd3LogShellCarrier_shell_eq_contract
    (j : Fin (capsuleLevels l)) (i : Capsule j.val)
    (x : ActualPlaceTotal I) :
    (actualInd3LogShellCarrier I j.val).shell i x =
      ((actualCapsuleContract I).logShell j).Shell i x.1 x.2 := rfl

/-! ## 3. Non-PUnit: the shells are actual log-shell spans -/

/-- The total actual place type is nonempty: the actual finite-place fiber
over the rational prime 5 is nonempty. -/
theorem actualPlaceTotal_five_nonempty :
    Nonempty (ActualPlaceTotal I) := by
  let vQ : ActualValuation := ⟨5, by norm_num⟩
  have h : Nonempty (actualPlace I vQ) := actualPlace_five_nonempty I
  obtain ⟨v⟩ := h
  exact ⟨vQ, v⟩

/-- The carrier's first field is exactly S1270's actual IQ-span at each
capsule label and actual place. -/
theorem actualInd3LogShellCarrier_shell_eq_IQSpan
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualInd3LogShellCarrier I j).shell i ⟨vQ, v⟩ =
      (actualLocalLogShellDatum I vQ v).IQSpan := rfl

/-- Equivalently, the carrier's shell is the rational span of the actual
integral log-shell of the common-prime completion. -/
theorem actualInd3LogShellCarrier_shell_eq_span
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualInd3LogShellCarrier I j).shell i ⟨vQ, v⟩ =
      ↥(Submodule.span ℚ
        (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v))) :=
  actualShell_eq_carrier_span I j i vQ v

/-- The actual integral log-shell contains 1. -/
theorem one_mem_actualIntegralLogShell
    (vQ : ActualValuation) (v : actualPlace I vQ) :
    (1 : CommonPrimeCompletion v) ∈ actualIntegralLogShell I vQ v := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  exact integers_subset_integralLogShell (p := vQ.1)
    ((Integers (CommonPrimeCompletion v)).one_mem)

/-- The underlying span of each actual shell contains 1. -/
theorem one_mem_actualShellSpan
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    (1 : CommonPrimeCompletion v) ∈
      (Submodule.span ℚ
        (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) :
        Set (CommonPrimeCompletion v)) := by
  exact Submodule.subset_span (one_mem_actualIntegralLogShell I vQ v)

/-- Each actual shell is nontrivial, so it is not the one-point PUnit model. -/
theorem actualInd3LogShellCarrier_shell_nontrivial
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    Nontrivial ((actualLogShellFamily I j).Shell i vQ v) := by
  rw [actualShell_eq_carrier_span]
  refine ⟨⟨1, one_mem_actualShellSpan I j i vQ v⟩,
    ⟨0, Submodule.zero_mem _⟩, ?_⟩
  intro h
  have h1 : (1 : CommonPrimeCompletion v) = 0 := congrArg Subtype.val h
  exact one_ne_zero h1

/-- The same nontriviality for the carrier's own first field. -/
theorem actualInd3LogShellCarrier_shell_nontrivial'
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    Nontrivial ((actualInd3LogShellCarrier I j).shell i ⟨vQ, v⟩) :=
  actualInd3LogShellCarrier_shell_nontrivial I j i vQ v

/-! ## 4. Exact first field for the ambient source place type `V` -/

/-- A place comparison from the source place type to the actual places of
S1270.  This is the exact first field needed to make the carrier live on the
same place index as S1266's Ind3 stage and poly-isomorphism. -/
abbrev Ind3PlaceComparison : Type (max uv (max 0 ua)) := V → ActualPlaceTotal I

/-- The exact first field, as a proposition.  No inhabitant is constructed or
asserted in this file. -/
def Ind3PlaceComparisonRequired : Prop := Nonempty (Ind3PlaceComparison I)

/-- Conditional V-indexed actual carrier: fill the first field with S1270's
actual log-shell family along a place comparison. -/
noncomputable def actualInd3LogShellCarrierOfMap (j : Nat)
    (p : V → ActualPlaceTotal I) :
    Ind3LogShellCarrier.{uv, 0, ua} (V := V) (R := ℚ) j where
  shell i v := (actualLogShellFamily I j).Shell i (p v).1 (p v).2
  addCommMonoid i v :=
    (actualLogShellFamily I j).addCommMonoid i (p v).1 (p v).2
  module i v := (actualLogShellFamily I j).module i (p v).1 (p v).2

/-- The conditional carrier's first field is S1270's shell composed with the
place comparison. -/
theorem actualInd3LogShellCarrierOfMap_shell (j : Nat)
    (p : V → ActualPlaceTotal I) (i : Capsule j) (v : V) :
    (actualInd3LogShellCarrierOfMap I j p).shell i v =
      (actualLogShellFamily I j).Shell i (p v).1 (p v).2 := rfl

/-- Conditional closure of S1266's open carrier requirement at the source
place type `V`, from the exact place comparison. -/
theorem ind3LogShellCarrierRequired_of_placeMap (j : Nat)
    (p : V → ActualPlaceTotal I) :
    Ind3LogShellCarrierRequired.{uv, 0, ua} (V := V) (R := ℚ) j :=
  ⟨actualInd3LogShellCarrierOfMap I j p⟩

/-! ## 5. Attachment to S1266's Ind3 stage and poly-isomorphism -/

/-- Actual Ind3 source data at the actual places: S1270's actual log-shell
carrier together with S1266's actual stage data and stage poly-isomorphisms.
The carrier is indexed by the actual places; the stage data and poly-isomorphism
are indexed by the source place type `V`.  No identification of the two index
types is asserted. -/
structure ActualInd3SourceDatum (n : Int) (j : Nat) where
  logShell :
    Ind3LogShellCarrier.{max 0 ua, 0, ua} (V := ActualPlaceTotal I) (R := ℚ) j
  stageData : ∀ v : V, SourceInd3StageData I n v
  stagePolyIso : ∀ m : Int,
    SourceFTimesMuPrimeStripEquivalence (ind3TimesMuStrip I n m)
      (ind3TimesMuStrip I n 0)

/-- The actual Ind3 source datum, assembled from S1270's carrier and S1266's
stage/poly-isomorphism data. -/
noncomputable def actualInd3SourceDatum (n : Int) (j : Nat) :
    ActualInd3SourceDatum I n j where
  logShell := actualInd3LogShellCarrier I j
  stageData v := sourceInd3StageData I n v
  stagePolyIso m := ind3StagePolyIso I n m

@[simp] theorem actualInd3SourceDatum_logShell (n : Int) (j : Nat) :
    (actualInd3SourceDatum I n j).logShell =
      actualInd3LogShellCarrier I j := rfl

@[simp] theorem actualInd3SourceDatum_stageData (n : Int) (j : Nat) (v : V) :
    (actualInd3SourceDatum I n j).stageData v =
      sourceInd3StageData I n v := rfl

@[simp] theorem actualInd3SourceDatum_stagePolyIso (n : Int) (j : Nat) (m : Int) :
    (actualInd3SourceDatum I n j).stagePolyIso m =
      ind3StagePolyIso I n m := rfl

/-- The attached stage comparison is S1266's actual stage comparison. -/
@[simp] theorem actualInd3SourceDatum_stageCompare
    (n : Int) (j : Nat) (v : V) (m : Int) :
    ((actualInd3SourceDatum I n j).stageData v).compare m =
      ind3StageComparison I n m v := rfl

/-- The attached stage action is S1266's actual times-mu action. -/
@[simp] theorem actualInd3SourceDatum_stageAction
    (n : Int) (j : Nat) (v : V) (m : Int) :
    ((actualInd3SourceDatum I n j).stageData v).action m =
      ind3StageAction I n m v := rfl

/-- Conditional V-indexed actual Ind3 source datum: all three fields live on
`V`, with the log-shell carrier filled from S1270 along the exact place
comparison `p`. -/
structure ActualInd3SourceDatumAtV (p : Ind3PlaceComparison I) (n : Int)
    (j : Nat) where
  logShell : Ind3LogShellCarrier.{uv, 0, ua} (V := V) (R := ℚ) j
  stageData : ∀ v : V, SourceInd3StageData I n v
  stagePolyIso : ∀ m : Int,
    SourceFTimesMuPrimeStripEquivalence (ind3TimesMuStrip I n m)
      (ind3TimesMuStrip I n 0)

/-- The conditional V-indexed actual Ind3 source datum. -/
noncomputable def actualInd3SourceDatumAtV (p : Ind3PlaceComparison I)
    (n : Int) (j : Nat) : ActualInd3SourceDatumAtV I p n j where
  logShell := actualInd3LogShellCarrierOfMap I j p
  stageData v := sourceInd3StageData I n v
  stagePolyIso m := ind3StagePolyIso I n m

@[simp] theorem actualInd3SourceDatumAtV_logShell
    (p : Ind3PlaceComparison I) (n : Int) (j : Nat) :
    (actualInd3SourceDatumAtV I p n j).logShell =
      actualInd3LogShellCarrierOfMap I j p := rfl

@[simp] theorem actualInd3SourceDatumAtV_stageData
    (p : Ind3PlaceComparison I) (n : Int) (j : Nat) (v : V) :
    (actualInd3SourceDatumAtV I p n j).stageData v =
      sourceInd3StageData I n v := rfl

@[simp] theorem actualInd3SourceDatumAtV_stagePolyIso
    (p : Ind3PlaceComparison I) (n : Int) (j : Nat) (m : Int) :
    (actualInd3SourceDatumAtV I p n j).stagePolyIso m =
      ind3StagePolyIso I n m := rfl

/-- S1270's actual poly-isomorphism acts on the actual Ind3 log-shell family. -/
noncomputable def actualInd3PolyIso (j : Nat) :
    PolyIsoAction (actualInd3LogShellFamily I j) :=
  actualPolyIso I j

theorem actualInd3PolyIso_labelPerm (j : Nat) :
    (actualInd3PolyIso I j).labelPerm = Fin.revPerm := rfl

theorem actualInd3PolyIso_labelPerm_ne_refl :
    (actualInd3PolyIso I 1).labelPerm ≠ Equiv.refl (Capsule 1) := by
  simpa [actualInd3PolyIso] using actualPolyIso_labelPerm_ne_refl I

theorem actualInd3PolyIso_ne_refl :
    actualInd3PolyIso I 1 ≠ PolyIsoAction.refl (actualInd3LogShellFamily I 1) := by
  change actualPolyIso I 1 ≠ PolyIsoAction.refl (actualLogShellFamily I 1)
  exact actualPolyIso_ne_refl I

/-- The tensor packet of the actual Ind3 family is exactly the contract's
tensor packet. -/
theorem actualInd3LogShellFamily_tensorPacket
    (j : Fin (capsuleLevels l)) (vQ : ActualValuation) :
    TensorPacket (actualInd3LogShellFamily I j.val) vQ =
      SourceProcessionCapsuleContract.tensorPacket ℚ (actualCapsuleContract I)
        j vQ := by
  rw [actualInd3LogShellFamily_eq_actualLogShellFamily]
  rfl

/-! ## 6. Axiom probes -/

#print axioms actualInd3LogShellCarrier
#print axioms actualInd3LogShellCarrierRequired_actual
#print axioms actualInd3LogShellFamily_eq_actualLogShellFamily
#print axioms actualInd3LogShellFamily_eq_contract_logShell
#print axioms actualPlaceTotal_five_nonempty
#print axioms actualInd3LogShellCarrier_shell_eq_IQSpan
#print axioms actualInd3LogShellCarrier_shell_eq_span
#print axioms actualInd3LogShellCarrier_shell_nontrivial
#print axioms actualInd3SourceDatum
#print axioms actualInd3SourceDatum_stageCompare
#print axioms actualInd3SourceDatum_stageAction
#print axioms actualInd3SourceDatumAtV
#print axioms actualInd3PolyIso_ne_refl
#print axioms actualInd3LogShellFamily_tensorPacket
#print axioms ind3LogShellCarrierRequired_of_placeMap

end LeanFormal.IUT.XiFPaper.S1297Ind3LogShellActual
