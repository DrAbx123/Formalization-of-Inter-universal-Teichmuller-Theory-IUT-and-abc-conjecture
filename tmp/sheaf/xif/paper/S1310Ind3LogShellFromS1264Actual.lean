import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual
import tmp.sheaf.xif.paper.S1266SourceInd3Actual

/-!
# S1310: actual Ind3 log-shell carrier from S1264's actual capsule contract

S1264SourceCapsuleInd1Actual constructs, for every `I : OriginalInput l V`, an
actual `SourceProcessionCapsuleContract ℚ_[l.value] l V I` with
`VQ = RationalPlaceAt l`, `place = ActualPlace I`, and a `logShell` whose shell
at every capsule label and actual place is the actual common-prime completion
`CommonPrimeCompletion v`.  This file uses that contract, and only that
contract, to fill the first field of S1266's `Ind3LogShellCarrier` and of the
`LogShellFamily` it induces.

## What is constructed

* `actualInd3LogShellCarrier`: the actual `Ind3LogShellCarrier` at the actual
  finite places `ActualPlace I`, with `shell i v = CommonPrimeCompletion v`;
* `actualInd3LogShellFamily`: the `LogShellFamily` first field, proved
  definitionally equal to `(actualContract I n).logShell j`;
* `actualInd3LogShellCarrierRequired`: the exact Prop left open by S1266 is
  now inhabited at the actual places;
* `actualInd3PolyIso`: the actual poly-isomorphism of S1264's contract, label
  reversal `Fin.revPerm` plus the reflexive shell equivalences;
* the actual local log-shell is the actual integral log-shell
  (`actualInd3LogShell_local_eq_integralLogShell`);
* the induced tensor packet is S1264's contract tensor packet.

No `PUnit`, no `IQSpan`/`Q`-span, no `True` gate, no new axiom and no `sorry`
is used.  The only `Nonempty` occurrence is the explicit exact-field Prop
`Ind3StagePlaceEquivRequired`, for which no inhabitant is asserted.

## Stage place model

S1266's times-mu stage, stage action and stage poly-isomorphism live at the
Hodge-theater place type `V` of `I`, while the actual completions live at
`ActualPlace I`.  The exact first field identifying the two place models is an
equivalence `e : V ≃ ActualPlace I` (in particular a place assignment
`V → ActualPlace I`); `OriginalInput` has no such field.  Given `e`, the carrier
is transferred to `V` (`...OfPlaceEquiv`), and
`ActualInd3LogShellStageData` records the transferred actual carrier family,
the actual poly-isomorphism, S1266's actual stage data and S1266's actual stage
poly-isomorphism on the same place type.  No inhabitant of
`Ind3StagePlaceEquiv` is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1310Ind3LogShellFromS1264Actual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual

universe ua uv upi umon ui uW uVQ uPlace uR uShell

variable {l : PrimeGeFive} {V : Type uv}

local instance factPrimeOfPrimeGeFive (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The actual Ind3 log-shell carrier -/

/-- The actual Ind3 log-shell carrier at the actual finite places of `K` above
    `l`: the shell at every capsule label and actual place is the actual
    common-prime completion.  This is exactly S1264's contract shell. -/
noncomputable def actualInd3LogShellCarrier (j : Nat) :
    Ind3LogShellCarrier.{ua, 0, ua} (V := ActualPlace I) (R := ℚ_[l.value]) j where
  shell i v := CommonPrimeCompletion v
  addCommMonoid i v := inferInstance
  module i v := inferInstance

/-- The first field of the carrier is literally the actual completion. -/
theorem actualInd3LogShellCarrier_shell (j : Nat) (i : Capsule j)
    (v : ActualPlace I) :
    (actualInd3LogShellCarrier I j).shell i v = CommonPrimeCompletion v := rfl

/-- The shell is a field, not a `PUnit` or a rational span. -/
@[reducible] noncomputable def actualInd3LogShellCarrier_shellField (j : Nat) (i : Capsule j)
    (v : ActualPlace I) :
    Field ((actualInd3LogShellCarrier I j).shell i v) := by
  change Field (CommonPrimeCompletion v)
  infer_instance

/-- The shell is nontrivial: it contains `0` and `1`. -/
theorem actualInd3LogShellCarrier_nontrivial (j : Nat) (i : Capsule j)
    (v : ActualPlace I) :
    Nontrivial ((actualInd3LogShellCarrier I j).shell i v) := by
  change Nontrivial (CommonPrimeCompletion v)
  infer_instance

/-- The zero and one of the actual shell are distinct. -/
theorem actualInd3LogShellCarrier_shell_zero_ne_one (v : ActualPlace I) :
    (0 : CommonPrimeCompletion v) ≠ 1 :=
  zero_ne_one

/-! ## 2. The `LogShellFamily` first field -/

/-- Universe-correct version of S1266's `Ind3LogShellCarrier.toLogShellFamily`.
    S1266's function restricts the place type to `Type`; the actual finite
    places live in `Type ua`, so the place universe is generalized here. -/
noncomputable def ind3ToLogShellFamily
    {R : Type uR} [CommSemiring R] {j : Nat}
    {W : Type uW} (L : Ind3LogShellCarrier.{uW, uR, uShell} (V := W) (R := R) j)
    {VQ : Type uVQ} (Place : VQ -> Type uPlace) (p : (vQ : VQ) -> Place vQ -> W) :
    LogShellFamily.{uR, uVQ, uPlace, uShell} R Place j where
  Shell i vQ v := L.shell i (p vQ v)
  addCommMonoid i vQ v := L.addCommMonoid i (p vQ v)
  module i vQ v := L.module i (p vQ v)

/-- When the places are in `Type`, the generalized function is literally
    S1266's `toLogShellFamily`; nothing in its first field is changed. -/
theorem ind3ToLogShellFamily_eq_toLogShellFamily
    {R : Type uR} [CommSemiring R] {j : Nat}
    {W : Type uW} (L : Ind3LogShellCarrier.{uW, uR, uShell} (V := W) (R := R) j)
    {VQ : Type} (Place : VQ -> Type) (p : (vQ : VQ) -> Place vQ -> W) :
    ind3ToLogShellFamily L Place p =
      Ind3LogShellCarrier.toLogShellFamily R j L VQ Place p := rfl

/-- The `LogShellFamily` first field of S1266 filled by the actual carrier. -/
noncomputable def actualInd3LogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℚ_[l.value]
      (fun _ : RationalPlaceAt l => ActualPlace I) j :=
  ind3ToLogShellFamily (actualInd3LogShellCarrier I j)
    (fun _ : RationalPlaceAt l => ActualPlace I) (fun _ v => v)

theorem actualInd3LogShellFamily_shell (j : Nat) (i : Capsule j)
    (vQ : RationalPlaceAt l) (v : ActualPlace I) :
    (actualInd3LogShellFamily I j).Shell i vQ v = CommonPrimeCompletion v := rfl

/-! ## 3. Exactness against S1264's actual contract -/

/-- The first field of the carrier is exactly S1264's contract shell at every
    capsule label, rational place and actual place. -/
theorem actualInd3LogShellCarrier_shell_eq_contract (n : Int)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val)
    (vQ : RationalPlaceAt l) (v : ActualPlace I) :
    (actualInd3LogShellCarrier I j.val).shell i v =
      ((actualContract I n).logShell j).Shell i vQ v := rfl

/-- The first field of the actual family is exactly S1264's contract shell at
    every capsule label, rational place and actual place. -/
theorem actualInd3LogShellFamily_shell_eq_contract (n : Int)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val)
    (vQ : RationalPlaceAt l) (v : ActualPlace I) :
    (actualInd3LogShellFamily I j.val).Shell i vQ v =
      ((actualContract I n).logShell j).Shell i vQ v := rfl

/-- The whole `LogShellFamily` is definitionally S1264's contract field. -/
theorem actualInd3LogShellFamily_eq_contract_logShell (n : Int)
    (j : Fin (capsuleLevels l)) :
    actualInd3LogShellFamily I j.val = (actualContract I n).logShell j := rfl

/-- S1266's open predicate is now inhabited at the actual places. -/
theorem actualInd3LogShellCarrierRequired (j : Nat) :
    Ind3LogShellCarrierRequired.{ua, 0, ua} (V := ActualPlace I)
      (R := ℚ_[l.value]) j :=
  ⟨actualInd3LogShellCarrier I j⟩

/-! ## 4. Nontriviality and the actual local log-shell -/

/-- The local log-shell at an actual place is the actual integral log-shell
    of the common-prime completion, by S1264's source local datum theorem. -/
theorem actualInd3LogShell_local_eq_integralLogShell (v : ActualPlace I) :
    actualLocalLogShell I v =
      (integralLogShell (K := CommonPrimeCompletion v) (p := l.value) :
        Set (CommonPrimeCompletion v)) :=
  actualLocalLogShell_eq_integralLogShell I v

/-! ## 5. The actual poly-isomorphism -/

/-- The actual poly-isomorphism on the actual Ind3 log-shell family: label
    reversal together with the reflexive shell equivalences, exactly S1264's
    `actualContract` poly-isomorphism. -/
noncomputable def actualInd3PolyIso (n : Int) (j : Fin (capsuleLevels l)) :
    PolyIsoAction (actualInd3LogShellFamily I j.val) :=
  (actualContract I n).polyIso j

theorem actualInd3PolyIso_eq_actualPolyIso (n : Int) (j : Fin (capsuleLevels l)) :
    actualInd3PolyIso I n j = actualPolyIso I j.val := rfl

theorem actualInd3PolyIso_labelPerm (n : Int) (j : Fin (capsuleLevels l)) :
    (actualInd3PolyIso I n j).labelPerm = Fin.revPerm := rfl

theorem actualInd3PolyIso_shellEquiv (n : Int) (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : RationalPlaceAt l) (v : ActualPlace I) :
    (actualInd3PolyIso I n j).shellEquiv i vQ v =
      LinearEquiv.refl ℚ_[l.value]
        ((actualInd3LogShellFamily I j.val).Shell i vQ v) := rfl

theorem actualInd3PolyIso_labelPerm_nontrivial (n : Int) :
    (actualInd3PolyIso I n ⟨1, one_lt_capsuleLevels l⟩).labelPerm ≠ Equiv.refl (Capsule 1) :=
  actualPolyIso_labelPerm_nontrivial I

/-- The induced tensor packet is literally S1264's contract tensor packet. -/
abbrev actualInd3TensorPacket (j : Nat) (vQ : RationalPlaceAt l) :=
  TensorPacket (actualInd3LogShellFamily I j) vQ

theorem actualInd3TensorPacket_eq_contract (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : RationalPlaceAt l) :
    actualInd3TensorPacket I j.val vQ =
      SourceProcessionCapsuleContract.tensorPacket ℚ_[l.value]
        (actualContract I n) j vQ := rfl

/-! ## 6. The stage place model and S1266's stage/poly-isomorphism -/

/-- The exact first field identifying the Hodge-theater place type `V` of
    S1266's stage with the actual finite places of S1264's contract.  This is
    an equivalence of place types, not a field of `OriginalInput`. -/
abbrev Ind3StagePlaceEquiv (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Type (max uv ua) :=
  V ≃ ActualPlace I

/-- The exact first field is required as an explicit datum; no inhabitant is
    asserted here. -/
def Ind3StagePlaceEquivRequired (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (Ind3StagePlaceEquiv (l := l) (V := V) I)

/-- The actual Ind3 log-shell carrier at the S1266 stage places, transferred
    along the place equivalence `e`. -/
noncomputable def actualInd3LogShellCarrierOfPlaceEquiv
    (e : V ≃ ActualPlace I) (j : Nat) :
    Ind3LogShellCarrier.{uv, 0, ua} (V := V) (R := ℚ_[l.value]) j where
  shell i v := CommonPrimeCompletion (e v)
  addCommMonoid i v := inferInstance
  module i v := inferInstance

/-- The corresponding `LogShellFamily` first field at the stage places. -/
noncomputable def actualInd3LogShellFamilyOfPlaceEquiv
    (e : V ≃ ActualPlace I) (j : Nat) :
    LogShellFamily.{0, 0, uv, ua} ℚ_[l.value]
      (fun _ : RationalPlaceAt l => V) j :=
  ind3ToLogShellFamily (actualInd3LogShellCarrierOfPlaceEquiv I e j)
    (fun _ : RationalPlaceAt l => V) (fun _ v => v)

theorem actualInd3LogShellCarrierOfPlaceEquiv_shell
    (e : V ≃ ActualPlace I) (j : Nat) (i : Capsule j) (v : V) :
    (actualInd3LogShellCarrierOfPlaceEquiv I e j).shell i v =
      CommonPrimeCompletion (e v) := rfl

theorem actualInd3LogShellFamilyOfPlaceEquiv_shell
    (e : V ≃ ActualPlace I) (j : Nat) (i : Capsule j)
    (vQ : RationalPlaceAt l) (v : V) :
    (actualInd3LogShellFamilyOfPlaceEquiv I e j).Shell i vQ v =
      CommonPrimeCompletion (e v) := rfl

/-- The stage-place shell is exactly S1264's contract shell at the actual
    place attached to the stage place by `e`. -/
theorem actualInd3LogShellFamilyOfPlaceEquiv_shell_eq_contract
    (e : V ≃ ActualPlace I) (n : Int) (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : RationalPlaceAt l) (v : V) :
    (actualInd3LogShellFamilyOfPlaceEquiv I e j.val).Shell i vQ v =
      ((actualContract I n).logShell j).Shell i vQ (e v) := rfl

/-- The actual poly-isomorphism at the stage places: label reversal and
    reflexive shell equivalences, the same formula as S1264's action. -/
noncomputable def actualInd3PolyIsoOfPlaceEquiv
    (e : V ≃ ActualPlace I) (j : Fin (capsuleLevels l)) :
    PolyIsoAction (actualInd3LogShellFamilyOfPlaceEquiv I e j.val) where
  labelPerm := Fin.revPerm
  shellEquiv i vQ v := LinearEquiv.refl ℚ_[l.value]
    ((actualInd3LogShellFamilyOfPlaceEquiv I e j.val).Shell i vQ v)

theorem actualInd3PolyIsoOfPlaceEquiv_labelPerm
    (e : V ≃ ActualPlace I) (j : Fin (capsuleLevels l)) :
    (actualInd3PolyIsoOfPlaceEquiv I e j).labelPerm = Fin.revPerm := rfl

theorem actualInd3PolyIsoOfPlaceEquiv_labelPerm_nontrivial
    (e : V ≃ ActualPlace I) :
    (actualInd3PolyIsoOfPlaceEquiv I e ⟨1, one_lt_capsuleLevels l⟩).labelPerm ≠ Equiv.refl (Capsule 1) := by
  rw [actualInd3PolyIsoOfPlaceEquiv_labelPerm]
  intro h
  have h0 := congrArg (fun f : Capsule 1 ≃ Capsule 1 => f 0) h
  simp [Fin.revPerm_apply, Fin.rev] at h0

/-- S1266's actual stage data, re-exported at the same stage places. -/
def actualInd3StageDataAtStagePlaces (n : Int) (v : V) : SourceInd3StageData I n v :=
  sourceInd3StageData I n v

theorem actualInd3StageDataAtStagePlaces_eq (n : Int) (v : V) :
    actualInd3StageDataAtStagePlaces I n v = sourceInd3StageData I n v := rfl

/-- S1266's actual stage poly-isomorphism, re-exported at the same stage
    places. -/
def actualInd3StagePolyIsoAtStagePlaces (n m : Int) :
    SourceFTimesMuPrimeStripEquivalence
      (ind3TimesMuStrip I n m) (ind3TimesMuStrip I n 0) :=
  ind3StagePolyIso I n m

theorem actualInd3StagePolyIsoAtStagePlaces_eq (n m : Int) :
    actualInd3StagePolyIsoAtStagePlaces I n m = ind3StagePolyIso I n m := rfl

/-- The stage-place attachment: the actual log-shell carrier and its actual
    poly-isomorphism are placed at the same place type as S1266's actual stage
    data and stage poly-isomorphism.  Every field is pinned to its actual
    construction; this is an attachment of the two actual data layers at a
    common place model, not a new compatibility theorem. -/
structure ActualInd3LogShellStageData
    (e : V ≃ ActualPlace I) (n : Int) where
  carrier : (j : Nat) → Ind3LogShellCarrier.{uv, 0, ua} (V := V) (R := ℚ_[l.value]) j
  carrier_eq : carrier = actualInd3LogShellCarrierOfPlaceEquiv I e
  family : (j : Nat) → LogShellFamily.{0, 0, uv, ua} ℚ_[l.value]
    (fun _ : RationalPlaceAt l => V) j
  family_eq : family = actualInd3LogShellFamilyOfPlaceEquiv I e
  polyIso : (j : Fin (capsuleLevels l)) →
    PolyIsoAction (actualInd3LogShellFamilyOfPlaceEquiv I e j.val)
  polyIso_eq : polyIso = actualInd3PolyIsoOfPlaceEquiv I e
  stage : (v : V) → SourceInd3StageData I n v
  stage_eq : stage = sourceInd3StageData I n
  stagePolyIso : (m : Int) → SourceFTimesMuPrimeStripEquivalence
    (ind3TimesMuStrip I n m) (ind3TimesMuStrip I n 0)
  stagePolyIso_eq : stagePolyIso = ind3StagePolyIso I n

noncomputable def actualInd3LogShellStageData
    (e : V ≃ ActualPlace I) (n : Int) : ActualInd3LogShellStageData I e n where
  carrier := actualInd3LogShellCarrierOfPlaceEquiv I e
  carrier_eq := rfl
  family := actualInd3LogShellFamilyOfPlaceEquiv I e
  family_eq := rfl
  polyIso := actualInd3PolyIsoOfPlaceEquiv I e
  polyIso_eq := rfl
  stage := sourceInd3StageData I n
  stage_eq := rfl
  stagePolyIso := ind3StagePolyIso I n
  stagePolyIso_eq := rfl

/-! ## 7. Axiom probes -/

#print axioms actualInd3LogShellCarrier
#print axioms actualInd3LogShellCarrier_shell_eq_contract
#print axioms actualInd3LogShellFamily
#print axioms actualInd3LogShellFamily_eq_contract_logShell
#print axioms actualInd3LogShellCarrierRequired
#print axioms actualInd3LogShellCarrier_nontrivial
#print axioms actualInd3LogShell_local_eq_integralLogShell
#print axioms actualInd3PolyIso
#print axioms actualInd3PolyIso_labelPerm_nontrivial
#print axioms actualInd3TensorPacket_eq_contract
#print axioms actualInd3LogShellFamilyOfPlaceEquiv
#print axioms actualInd3LogShellStageData

end LeanFormal.IUT.XiFPaper.S1310Ind3LogShellFromS1264Actual

end