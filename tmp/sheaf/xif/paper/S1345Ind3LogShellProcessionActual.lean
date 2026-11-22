import tmp.sheaf.xif.paper.S1327Ind3IntegralLogShellActual
import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary

/-!
# S1345: actual (Ind3) stage data on the genuine integral log-shell packet

S1315 assembled the actual Ind1/Ind2/Ind3 native actions and recorded the
first field of the target `DPrimeStripProcession` that the Fmod tensor packet
does not supply: `ind3`, whose target type is `Nat -> T -> T`, while the actual
S1266 (Ind3) datum is the times-mu stage comparison

  `(m : Int) -> Ind3Stage I n m v =* Ind3Stage I n 0 v`.

This file works on the genuine integral log-shell tensor packet of S1313 and
the integral Ind3 carrier of S1327.

1. The integral packet `ActualTensorPacket (actualIntegralCapsuleContract I) j vQ`
   has as its shell at every label and actual place exactly the integral
   log-shell of S1313.

2. S1264's actual Ind1 candidate gives a literal Z-linear reindexing of this
   packet by `PiTensorProduct.reindex`, with its exact formula recorded.

3. S1266's actual comparison/action and the S1327 integral carrier are packaged
   with the integral packet in `IntegralSourceIndActionData`: the multi-carrier
   `SourceIndActionData` shape over the integral packet.  Its `ind3Compare` and
   `ind3Action` areas are literally S1266's comparison and action.

4. The exact mismatch is recorded in `IntegralInd3FieldMismatch`: the target
   needs `Nat -> T -> T` on the packet, while the actual comparison has type
   `(m : Int) -> Ind3Stage m =* Ind3Stage 0`.  We prove the comparison at 0 is
   the identity, that comparison-then-inverse is the identity endomorphism of
   the core stage, and that the comparison is onto the core stage.

5. Nevertheless the actual data carry a genuine non-identity Nat-action on the
   actual total stage carrier `(m : Int) x Ind3Stage I n m v`: the k-fold
   iterate of the actual one-stage comparison.  The unit, multiplication and
   level laws are proved, and `ind3StageShiftTotal_one_ne` proves that the
   one-step action differs from the identity on every element.  Hence the
   obstruction to the target procession is exactly the carrier (packet versus
   Int-indexed total stage), not a fake identity.

## Scope boundary on Ind2

S1265's actual Ind2 construction is an action of the Fmod-unit copies on a
tensor packet over a coefficient ring R with [Field R] and [Algebra Fmod R].
The integral log-shell packet of S1313 has coefficient ring Z.  No field
structure or Fmod-algebra structure on Z is constructed or asserted here, and
the actual Ind2 action is not replaced by the identity: the integral record
below has Ind1 and Ind3 fields only.  This is an independent coefficient-ring
obstruction, not the ind3 stage-comparison issue.

No sorry, no new axiom, no PUnit/one-point model, no IQSpan/Q-span and no
arbitrary constant is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1345Ind3LogShellProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual
open LeanFormal.IUT.XiFPaper.S1327Ind3IntegralLogShellActual
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open scoped TensorProduct

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

local instance s1345ValuationFact (vQ : ActualIntegralValuation) :
    Fact vQ.1.Prime := ⟨vQ.2⟩

local instance s1345PrimeFact (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. The genuine integral log-shell tensor packet -/

abbrev IntegralTensorPacket (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) : Type ua :=
  ActualTensorPacket (actualIntegralCapsuleContract I) j vQ

theorem integralTensorPacket_eq_tensorPacket (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ) :
    IntegralTensorPacket I n j vQ =
      SourceProcessionCapsuleContract.tensorPacket ℤ
        (actualIntegralCapsuleContract I) j vQ := rfl

theorem integralTensorPacket_logShell (j : Fin (capsuleLevels l)) :
    (actualIntegralCapsuleContract I).logShell j = integralLogShellFamily I j.val := rfl

theorem integralTensorPacket_shell (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    ((actualIntegralCapsuleContract I).logShell j).Shell i vQ v =
      ↥(actualIntegralLogShell I vQ v) := rfl

theorem integralTensorPacket_shell_nontrivial (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    Nontrivial (((actualIntegralCapsuleContract I).logShell j).Shell i vQ v) :=
  integralShell_nontrivial I vQ v

/-! ## 2. The actual Ind1 Z-linear action on the integral packet -/

noncomputable def integralInd1Tensor (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) :
    IntegralTensorPacket I n j vQ ≃ₗ[ℤ]
      (⨂[ℤ] i : Capsule j.val,
        DirectSumFactor ((actualIntegralCapsuleContract I).logShell j) vQ
          ((ind1Candidate I n j).perm.symm i)) :=
  PiTensorProduct.reindex (R := ℤ)
    (s := fun i =>
      DirectSumFactor ((actualIntegralCapsuleContract I).logShell j) vQ i)
    (e := (ind1Candidate I n j).perm)

theorem integralInd1Tensor_eq_reindex (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) :
    integralInd1Tensor I n j vQ =
      PiTensorProduct.reindex (R := ℤ)
        (s := fun i =>
          DirectSumFactor ((actualIntegralCapsuleContract I).logShell j) vQ i)
        (e := (ind1Candidate I n j).perm) := rfl

theorem integralPacket_permuted_eq (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) :
    (⨂[ℤ] i : Capsule j.val,
        DirectSumFactor ((actualIntegralCapsuleContract I).logShell j) vQ
          ((ind1Candidate I n j).perm.symm i)) =
      IntegralTensorPacket I n j vQ := rfl

theorem integralInd1Tensor_tprod (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ)
    (x : (i : Capsule j.val) →
      DirectSumFactor ((actualIntegralCapsuleContract I).logShell j) vQ i) :
    integralInd1Tensor I n j vQ (PiTensorProduct.tprod ℤ x) =
      PiTensorProduct.tprod ℤ
        (fun i => x ((ind1Candidate I n j).perm.symm i)) := by
  rw [integralInd1Tensor_eq_reindex]
  rw [PiTensorProduct.reindex_tprod]

theorem integralInd1Tensor_map_add (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ)
    (x y : IntegralTensorPacket I n j vQ) :
    integralInd1Tensor I n j vQ (x + y) =
      integralInd1Tensor I n j vQ x + integralInd1Tensor I n j vQ y :=
  map_add (integralInd1Tensor I n j vQ) x y

theorem integralInd1Tensor_map_smul (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (a : ℤ)
    (x : IntegralTensorPacket I n j vQ) :
    integralInd1Tensor I n j vQ (a • x) = a • integralInd1Tensor I n j vQ x :=
  map_smul (integralInd1Tensor I n j vQ) a x

theorem integralInd1Tensor_perm (n : Int) (j : Fin (capsuleLevels l)) :
    (ind1Candidate I n j).perm = Fin.revPerm := rfl

/-! ## 3. The actual S1266 stage comparison and action -/

noncomputable def ind3Compare (n : Int) (v : V) (m : Int) :
    Ind3Stage I n m v ≃* Ind3Stage I n 0 v :=
  ind3StageComparison I n m v

noncomputable def ind3Action (n : Int) (v : V) (m : Int) :
    (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →* MulAut (Ind3Stage I n m v) :=
  ind3StageAction I n m v

@[simp] theorem ind3Compare_eq (n : Int) (v : V) (m : Int) :
    ind3Compare I n v m = ind3StageComparison I n m v := rfl

@[simp] theorem ind3Action_eq (n : Int) (v : V) (m : Int) :
    ind3Action I n v m = ind3StageAction I n m v := rfl

theorem ind3Compare_zero (n : Int) (v : V) :
    ind3Compare I n v 0 = MulEquiv.refl (Ind3Stage I n 0 v) :=
  ind3StageComparison_zero I n v

theorem ind3Compare_action (n : Int) (v : V) (m : Int)
    (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v)
    (x : Ind3Stage I n m v) :
    ind3Compare I n v m (ind3Action I n v m g x) =
      ind3Action I n v 0 ((I.fLinkAt n m n 0).isoPi v g)
        (ind3Compare I n v m x) :=
  ind3StageComparison_action I n m v g x

theorem ind3Compare_image_univ (n : Int) (v : V) (m : Int) :
    ind3Compare I n v m '' (Set.univ : Set (Ind3Stage I n m v)) = Set.univ :=
  ind3StageComparison_image_univ I n m v

theorem ind3Compare_roundtrip_identity (n : Int) (v : V) (m : Int) :
    (ind3Compare I n v m).trans (ind3Compare I n v m).symm =
      MulEquiv.refl (Ind3Stage I n m v) :=
  MulEquiv.self_trans_symm _

/-! ## 4. Comparisons between arbitrary stages -/

noncomputable def stageEquiv (n : Int) (m m' : Int) (v : V) :
    Ind3Stage I n m v ≃* Ind3Stage I n m' v :=
  (ind3StageComparison I n m v).trans (ind3StageComparison I n m' v).symm

theorem stageEquiv_refl (n : Int) (m : Int) (v : V) :
    stageEquiv I n m m v = MulEquiv.refl (Ind3Stage I n m v) := by
  simp only [stageEquiv]
  rw [MulEquiv.self_trans_symm]

theorem stageEquiv_trans (n : Int) (m m' m'' : Int) (v : V) :
    (stageEquiv I n m m' v).trans (stageEquiv I n m' m'' v) =
      stageEquiv I n m m'' v := by
  simp only [stageEquiv]
  ext x
  simp [MulEquiv.trans_apply]

theorem stageEquiv_core (n : Int) (m : Int) (v : V) :
    stageEquiv I n m 0 v = ind3StageComparison I n m v := by
  simp only [stageEquiv, ind3StageComparison_zero]
  ext x
  simp [MulEquiv.trans_apply]

theorem stageEquiv_zero_stage (n : Int) (k : Int) (v : V) :
    stageEquiv I n 0 k v = (ind3StageComparison I n k v).symm := by
  simp only [stageEquiv, ind3StageComparison_zero]
  ext x
  simp [MulEquiv.trans_apply]

/-! ## 5. The actual non-identity Nat-action on the total stage carrier -/

abbrev Ind3StageTotal (n : Int) (v : V) : Type umon :=
  (m : Int) × Ind3Stage I n m v

noncomputable def ind3StageSucc (n : Int) (v : V) :
    Ind3StageTotal I n v → Ind3StageTotal I n v :=
  fun c => ⟨c.1 + 1, stageEquiv I n c.1 (c.1 + 1) v c.2⟩

noncomputable def ind3StageShiftTotal (n : Int) (v : V) (k : Nat) :
    Ind3StageTotal I n v → Ind3StageTotal I n v :=
  (ind3StageSucc I n v)^[k]

theorem ind3StageShiftTotal_zero (n : Int) (v : V) :
    ind3StageShiftTotal I n v 0 = id := rfl

theorem ind3StageShiftTotal_add (n : Int) (v : V) (m k : Nat) :
    ind3StageShiftTotal I n v (m + k) =
      (ind3StageShiftTotal I n v k) ∘ (ind3StageShiftTotal I n v m) := by
  simp only [ind3StageShiftTotal]
  rw [Nat.add_comm m k, Function.iterate_add]

theorem ind3StageShiftTotal_one (n : Int) (v : V) :
    ind3StageShiftTotal I n v 1 = ind3StageSucc I n v :=
  Function.iterate_one _

theorem ind3StageSucc_fst (n : Int) (v : V) (c : Ind3StageTotal I n v) :
    (ind3StageSucc I n v c).1 = c.1 + 1 := rfl

theorem ind3StageShiftTotal_one_ne (n : Int) (v : V)
    (c : Ind3StageTotal I n v) :
    ind3StageShiftTotal I n v 1 c ≠ c := by
  intro h
  have hfst : (ind3StageShiftTotal I n v 1 c).1 = c.1 := congrArg Sigma.fst h
  rw [ind3StageShiftTotal_one, ind3StageSucc_fst] at hfst
  omega

theorem ind3StageShiftTotal_fst_ge (n : Int) (v : V) (k : Nat)
    (c : Ind3StageTotal I n v) :
    c.1 ≤ (ind3StageShiftTotal I n v k c).1 := by
  induction k with
  | zero =>
      rw [ind3StageShiftTotal_zero]
      rfl
  | succ k ih =>
      rw [ind3StageShiftTotal_add I n v k 1]
      change c.1 ≤ (ind3StageShiftTotal I n v 1
        (ind3StageShiftTotal I n v k c)).1
      rw [ind3StageShiftTotal_one, ind3StageSucc_fst]
      omega

def ind3StageLevel (n : Int) (v : V) (c : Ind3StageTotal I n v) : Nat :=
  c.1.toNat

theorem ind3StageShiftTotal_level (n : Int) (v : V) (k : Nat)
    (c : Ind3StageTotal I n v) :
    ind3StageLevel I n v c ≤ ind3StageLevel I n v
      (ind3StageShiftTotal I n v k c) := by
  unfold ind3StageLevel
  exact Int.toNat_le_toNat (ind3StageShiftTotal_fst_ge I n v k c)

/-! ## 6. The integral Ind3 carrier of S1327 and the native data package -/

abbrev IntegralInd3Carrier (j : Nat) :
    Ind3LogShellCarrier.{max 0 ua, 0, ua} (V := IntegralPlaceTotal I) (R := ℤ) j :=
  integralInd3LogShellCarrier I j

theorem integralInd3CarrierRequired (j : Nat) :
    Ind3LogShellCarrierRequired.{max 0 ua, 0, ua} (V := IntegralPlaceTotal I)
      (R := ℤ) j :=
  integralInd3LogShellCarrierRequired_actual I j

theorem integralInd3Carrier_shell_eq_contract (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (x : IntegralPlaceTotal I) :
    (IntegralInd3Carrier I j.val).shell i x =
      ((actualIntegralCapsuleContract I).logShell j).Shell i x.1 x.2 :=
  integralInd3LogShellCarrier_shell_eq_contract I j i x

structure IntegralSourceIndActionData
    (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) where
  ind1Candidate : PrcAutomorphism (canonicalCapsuleTheaterAssignment I n) j
  ind1Tensor : IntegralTensorPacket I n j vQ ≃ₗ[ℤ]
    (⨂[ℤ] i : Capsule j.val,
      DirectSumFactor ((actualIntegralCapsuleContract I).logShell j) vQ
        (ind1Candidate.perm.symm i))
  ind1Tensor_eq : ind1Tensor = integralInd1Tensor I n j vQ
  ind3Carrier : Ind3LogShellCarrier.{max 0 ua, 0, ua} (V := IntegralPlaceTotal I)
    (R := ℤ) j.val
  ind3Carrier_eq : ind3Carrier = integralInd3LogShellCarrier I j.val
  ind3Compare : (m : Int) → Ind3Stage I n m v ≃* Ind3Stage I n 0 v
  ind3Compare_eq : ind3Compare = fun m => ind3StageComparison I n m v
  ind3Action : (m : Int) →
    (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →* MulAut (Ind3Stage I n m v)
  ind3Action_eq : ind3Action = fun m => ind3StageAction I n m v
  ind3_action_compat : ∀ (m : Int)
    (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v)
    (x : Ind3Stage I n m v),
    ind3Compare m (ind3Action m g x) =
      ind3Action 0 ((I.fLinkAt n m n 0).isoPi v g) (ind3Compare m x)

noncomputable def integralSourceIndActionData (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) : IntegralSourceIndActionData I n j vQ v where
  ind1Candidate := ind1Candidate I n j
  ind1Tensor := integralInd1Tensor I n j vQ
  ind1Tensor_eq := rfl
  ind3Carrier := integralInd3LogShellCarrier I j.val
  ind3Carrier_eq := rfl
  ind3Compare := fun m => ind3StageComparison I n m v
  ind3Compare_eq := rfl
  ind3Action := fun m => ind3StageAction I n m v
  ind3Action_eq := rfl
  ind3_action_compat := fun m g x => ind3StageComparison_action I n m v g x

@[simp] theorem integralSourceIndActionData_ind1Tensor (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralSourceIndActionData I n j vQ v).ind1Tensor =
      integralInd1Tensor I n j vQ := rfl

@[simp] theorem integralSourceIndActionData_ind3Carrier (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralSourceIndActionData I n j vQ v).ind3Carrier =
      integralInd3LogShellCarrier I j.val := rfl

@[simp] theorem integralSourceIndActionData_ind3Compare (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) (m : Int) :
    (integralSourceIndActionData I n j vQ v).ind3Compare m =
      ind3StageComparison I n m v := rfl

@[simp] theorem integralSourceIndActionData_ind3Action (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) (m : Int) :
    (integralSourceIndActionData I n j vQ v).ind3Action m =
      ind3StageAction I n m v := rfl

/-! ## 7. The exact first field/type mismatch for DPrimeStripProcession -/

inductive SourceIndField where
  | base
  | level
  | ind1
  | ind2
  | ind3
  deriving DecidableEq, Repr

def SourceIndField.name : SourceIndField → String
  | .base => "base"
  | .level => "level"
  | .ind1 => "ind1"
  | .ind2 => "ind2"
  | .ind3 => "ind3"

abbrev TargetInd3TypeAtIntegralPacket (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) : Type ua :=
  Nat → IntegralTensorPacket I n j vQ → IntegralTensorPacket I n j vQ

abbrev ActualInd3ComparisonType (n : Int) (v : V) : Type umon :=
  (m : Int) → Ind3Stage I n m v ≃* Ind3Stage I n 0 v

abbrev ActualInd3ActionType (n : Int) (v : V) : Type (max upi umon) :=
  (m : Int) → (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →
    MulAut (Ind3Stage I n m v)

abbrev ActualInd3StageShiftType (n : Int) (v : V) : Type umon :=
  Nat → Ind3StageTotal I n v → Ind3StageTotal I n v

structure IntegralInd3FieldMismatch
    (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) where
  firstField : SourceIndField
  firstField_eq : firstField = SourceIndField.ind3
  requiredType : Type ua
  requiredType_eq : requiredType = TargetInd3TypeAtIntegralPacket I n j vQ
  actualComparison : ActualInd3ComparisonType I n v
  actualComparison_eq : actualComparison = fun m => ind3StageComparison I n m v
  actualAction : (m : Int) →
    (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →* MulAut (Ind3Stage I n m v)
  actualAction_eq : actualAction = fun m => ind3StageAction I n m v
  actualShift : ActualInd3StageShiftType I n v
  actualShift_eq : actualShift = fun k => ind3StageShiftTotal I n v k
  comparison_zero : actualComparison 0 = MulEquiv.refl (Ind3Stage I n 0 v)
  shift_nonidentity : ∀ c : Ind3StageTotal I n v, actualShift 1 c ≠ c

noncomputable def integralInd3FieldMismatch (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) : IntegralInd3FieldMismatch I n j vQ v where
  firstField := SourceIndField.ind3
  firstField_eq := rfl
  requiredType := TargetInd3TypeAtIntegralPacket I n j vQ
  requiredType_eq := rfl
  actualComparison := fun m => ind3StageComparison I n m v
  actualComparison_eq := rfl
  actualAction := fun m => ind3StageAction I n m v
  actualAction_eq := rfl
  actualShift := fun k => ind3StageShiftTotal I n v k
  actualShift_eq := rfl
  comparison_zero := ind3StageComparison_zero I n v
  shift_nonidentity := fun c => ind3StageShiftTotal_one_ne I n v c

@[simp] theorem integralInd3FieldMismatch_firstField (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralInd3FieldMismatch I n j vQ v).firstField = SourceIndField.ind3 := rfl

theorem integralInd3FieldMismatch_firstField_name (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralInd3FieldMismatch I n j vQ v).firstField.name = "ind3" := rfl

theorem integralInd3FieldMismatch_requiredType (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralInd3FieldMismatch I n j vQ v).requiredType =
      (Nat → IntegralTensorPacket I n j vQ →
        IntegralTensorPacket I n j vQ) := rfl

theorem integralInd3FieldMismatch_actualComparison (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralInd3FieldMismatch I n j vQ v).actualComparison =
      (fun m => ind3StageComparison I n m v) := rfl

theorem integralInd3FieldMismatch_actualAction (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralInd3FieldMismatch I n j vQ v).actualAction =
      (fun m => ind3StageAction I n m v) := rfl

theorem integralInd3FieldMismatch_comparison_zero (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralInd3FieldMismatch I n j vQ v).actualComparison 0 =
      MulEquiv.refl (Ind3Stage I n 0 v) :=
  ind3StageComparison_zero I n v

theorem integralInd3FieldMismatch_shift_nonidentity (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) (c : Ind3StageTotal I n v) :
    (integralInd3FieldMismatch I n j vQ v).actualShift 1 c ≠ c :=
  ind3StageShiftTotal_one_ne I n v c

theorem integralInd3_exact_mismatch_summary (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (actualIntegralCapsuleContract I).VQ)
    (v : V) :
    (integralInd3FieldMismatch I n j vQ v).firstField = SourceIndField.ind3 ∧
      (integralInd3FieldMismatch I n j vQ v).requiredType =
        (Nat → IntegralTensorPacket I n j vQ →
          IntegralTensorPacket I n j vQ) ∧
      (integralInd3FieldMismatch I n j vQ v).actualComparison =
        (fun m => ind3StageComparison I n m v) ∧
      (integralInd3FieldMismatch I n j vQ v).actualComparison 0 =
        MulEquiv.refl (Ind3Stage I n 0 v) ∧
      (∀ c : Ind3StageTotal I n v,
        (integralInd3FieldMismatch I n j vQ v).actualShift 1 c ≠ c) :=
  ⟨rfl, rfl, rfl, ind3StageComparison_zero I n v,
    fun c => ind3StageShiftTotal_one_ne I n v c⟩

/-! ## 8. The exact coefficient datum required by the actual Ind2 action

S1265 constructs the actual Ind2 action only for a coefficient ring R which is
a field and carries an Fmod-algebra structure.  The integral log-shell packet
has R = Z.  The record below is the exact datum that datum requires; no
inhabitant at Z is constructed or asserted. -/

structure Ind2CoefficientData (R : Type) [CommSemiring R] where
  /-- The coefficient ring is a field. -/
  field : Field R
  /-- The coefficient ring is an algebra over the source base field Fmod. -/
  algebra : Algebra (I.initial.arithmetic.Fmod) R

/-! ## 8. Axiom probes -/

#print axioms integralTensorPacket_shell
#print axioms integralTensorPacket_shell_nontrivial
#print axioms integralInd1Tensor
#print axioms integralInd1Tensor_tprod
#print axioms ind3Compare_action
#print axioms ind3Compare_image_univ
#print axioms stageEquiv_trans
#print axioms stageEquiv_core
#print axioms stageEquiv_zero_stage
#print axioms ind3StageShiftTotal_zero
#print axioms ind3StageShiftTotal_add
#print axioms ind3StageShiftTotal_one_ne
#print axioms ind3StageShiftTotal_level
#print axioms integralInd3CarrierRequired
#print axioms integralSourceIndActionData
#print axioms integralInd3FieldMismatch
#print axioms integralInd3_exact_mismatch_summary

end LeanFormal.IUT.XiFPaper.S1345Ind3LogShellProcessionActual
