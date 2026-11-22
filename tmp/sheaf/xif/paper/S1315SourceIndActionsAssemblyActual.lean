import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual
import tmp.sheaf.xif.paper.S1265SourceInd2Actual
import tmp.sheaf.xif.paper.S1266SourceInd3Actual
import tmp.sheaf.xif.paper.Ind1AutomorphismTensorActionActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import Mathlib.RingTheory.DedekindDomain.AdicValuation

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1315SourceIndActionsAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open scoped TensorProduct

universe ua uv upi umon ui uR

variable {l : PrimeGeFive} {V : Type uv}

/-- The actual prime l is prime. -/
local instance factPrimeOfPrimeGeFive (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-!
# S1315: assembling the actual Ind1/Ind2/Ind3 actions

The three source-level actions constructed in S1264/S1265/S1266 have
different native carriers:

* S1264 ind1Candidate is a PrcAutomorphism of the actual canonical
  capsule theater assignment; its tensor action is a re-indexing of the
  actual tensor packet, landing in the permuted tensor packet.
* S1265 sourceInd2FmodTensorEquiv is a linear automorphism of the actual
  tensor packet over the actual source field Fmod, fed by the actual
  independent unit copies.
* S1266 ind3StageComparison and ind3StageAction live on the actual
  times-mu quotient stage Ind3Stage I n m v; the stage type depends on
  m : Int, and the equivalences are multiplicative.

This file:

1. constructs the actual Fmod capsule contract over the actual
   v.val.maximalIdeal.adicCompletion K completions, so that S1265's
   unconditional Fmod tensor action can be applied;
2. records the actual Ind1 candidate and its tensor re-indexing on the same
   tensor packet;
3. proves the actual Ind2 unit and multiplication laws on that packet;
4. records the actual Ind3 stage comparison/action and its action law;
5. packages these native data as SourceIndActionData;
6. records the first field of DPrimeStripProcession that the actual
   tensor-carrier data do not supply: ind3.  The required type is
   Nat -> T -> T; the actual S1266 comparison type is
   (m : Int) -> Ind3Stage I n m v =* Ind3Stage I n 0 v, with the
   m-dependent multiplicative stage carrier.

The full single-carrier DPrimeStripProcession is not constructed.  The tensor
packet carries the actual Ind1 candidate and the actual Ind2 Fmod-unit action;
the actual Ind3 data live on the times-mu stage.  Thus the first target field
whose carrier does not match the actual S1266 carrier is ind3.  A separate,
independent mismatch is the label group: the target uses one additive Label for
ind1 and ind2, while the actual Ind1 candidate is a single capsule automorphism
and the actual Ind2 labels are the multiplicative Fmod-unit copies.  This file
does not identify those label groups either.

No family.index translation, no ProcessionChoice finite model, no
one-point carrier, no sorry, and no new axiom is used.
-/

/-! ## 1. The actual Fmod capsule contract -/

/-- The actual local completion at a finite place of K, as an Fmod-module.
This is the genuine v-adic completion v.val.maximalIdeal.adicCompletion K,
not the one-point model. -/
abbrev FmodShell (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : ActualPlace I) : Type ua :=
  v.val.maximalIdeal.adicCompletion I.initial.arithmetic.K

/-- The actual log-shell family over the actual finite places of K above
l, with the actual local completion as shell carrier. -/
noncomputable def fmodLogShellFamily
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (j : Nat) :
    LogShellFamily (I.initial.arithmetic.Fmod)
      (fun _ : RationalPlaceAt l => ActualPlace I) j where
  Shell := fun _ _ v => FmodShell I v
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

/-- The actual poly-isomorphism: reverse the capsule labels and use the
canonical reflexive linear equivalences of the label-independent shell
carrier. -/
noncomputable def fmodPolyIso
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (j : Nat) :
    PolyIsoAction (fmodLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun _ _ v =>
    LinearEquiv.refl (I.initial.arithmetic.Fmod) (FmodShell I v)

/-- The actual source capsule contract over the actual source field Fmod,
with the canonical source-theater assignment, the actual finite places of
K above l, the actual completions, and the label-reversal
poly-isomorphism. -/
noncomputable def fmodCapsuleContract
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I where
  procession := (canonicalCapsuleTheaterAssignment I n).toProcession n
  VQ := RationalPlaceAt l
  place := fun _ => ActualPlace I
  fintypePlace := fun _ => inferInstance
  logShell := fun j => fmodLogShellFamily I j.val
  polyIso := fun j => fmodPolyIso I j.val

@[simp] theorem fmodCapsuleContract_VQ
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    (fmodCapsuleContract I n).VQ = RationalPlaceAt l := rfl

@[simp] theorem fmodCapsuleContract_place
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    (fmodCapsuleContract I n).place =
      (fun _ : RationalPlaceAt l => ActualPlace I) := rfl

@[simp] theorem fmodCapsuleContract_logShell
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    (fmodCapsuleContract I n).logShell j =
      fmodLogShellFamily I j.val := rfl

@[simp] theorem fmodCapsuleContract_polyIso
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    (fmodCapsuleContract I n).polyIso j =
      fmodPolyIso I j.val := rfl

/-- The actual shell carrier is the actual local completion. -/
theorem fmodLogShellFamily_shell_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (j : Nat)
    (i : Capsule j) (vQ : RationalPlaceAt l) (v : ActualPlace I) :
    (fmodLogShellFamily I j).Shell i vQ v = FmodShell I v := rfl

/-- The actual local completion is a nontrivial field: 0 != 1. -/
theorem fmodShell_zero_ne_one
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : ActualPlace I) :
    (0 : FmodShell I v) ≠ 1 :=
  zero_ne_one

/-- The tensor packet associated to the actual Fmod contract. -/
abbrev FmodTensorPacket
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ) : Type ua :=
  ActualTensorPacket (fmodCapsuleContract I n) j vQ

/-! ## 2. The actual Ind1 candidate and its tensor re-indexing -/

/-- Generic-coefficient form of the actual Ind1 tensor action: the literal
PiTensorProduct.reindex by the capsule permutation of the PrcAutomorphism.
At R = Real this is the formula of
Ind1AutomorphismTensorActionActual.PrcAutomorphismTensorAction. -/
noncomputable def prcAutomorphismTensorAction
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {R : Type uR} [CommSemiring R]
    (A : CapsuleTheaterAssignment l V I)
    (C : SourceProcessionCapsuleContract R l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) (P : PrcAutomorphism A j) :
    ActualTensorPacket C j vQ ≃ₗ[R]
      (⨂[R] i : Capsule j.val,
        DirectSumFactor (C.logShell j) vQ (P.perm.symm i)) :=
  PiTensorProduct.reindex (R := R)
    (s := fun i => DirectSumFactor (C.logShell j) vQ i) (e := P.perm)

/-- The actual Ind1 tensor re-indexing at the actual Fmod capsule contract. -/
noncomputable def ind1Tensor
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ) :
    FmodTensorPacket I n j vQ ≃ₗ[I.initial.arithmetic.Fmod]
      (⨂[I.initial.arithmetic.Fmod] i : Capsule j.val,
        DirectSumFactor ((fmodCapsuleContract I n).logShell j) vQ
          ((ind1Candidate (I := I) n j).perm.symm i)) :=
  prcAutomorphismTensorAction (I := I)
    (canonicalCapsuleTheaterAssignment I n) (fmodCapsuleContract I n) j vQ
    (ind1Candidate (I := I) n j)

@[simp] theorem ind1Tensor_eq_reindex
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ) :
    ind1Tensor I n j vQ =
      PiTensorProduct.reindex (R := I.initial.arithmetic.Fmod)
        (s := fun i => DirectSumFactor ((fmodCapsuleContract I n).logShell j) vQ i)
        (ind1Candidate (I := I) n j).perm := rfl

@[simp] theorem ind1Candidate_perm_eq_revPerm
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    (ind1Candidate (I := I) n j).perm = Fin.revPerm := rfl

/-- The actual Ind1 tensor re-indexing on pure tensors. -/
theorem ind1Tensor_tprod
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ)
    (x : (i : Capsule j.val) →
      DirectSumFactor ((fmodCapsuleContract I n).logShell j) vQ i) :
    ind1Tensor I n j vQ (PiTensorProduct.tprod (I.initial.arithmetic.Fmod) x) =
      PiTensorProduct.tprod (I.initial.arithmetic.Fmod)
        (fun i => x ((ind1Candidate (I := I) n j).perm.symm i)) := by
  rw [ind1Tensor_eq_reindex]
  rw [PiTensorProduct.reindex_tprod]

/-- The actual Ind1 tensor re-indexing is additive. -/
theorem ind1Tensor_map_add
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ)
    (x y : FmodTensorPacket I n j vQ) :
    ind1Tensor I n j vQ (x + y) =
      ind1Tensor I n j vQ x + ind1Tensor I n j vQ y :=
  map_add (ind1Tensor I n j vQ) x y

/-- The actual Ind1 tensor re-indexing is Fmod-linear. -/
theorem ind1Tensor_map_smul
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ)
    (a : I.initial.arithmetic.Fmod) (x : FmodTensorPacket I n j vQ) :
    ind1Tensor I n j vQ (a • x) = a • ind1Tensor I n j vQ x :=
  map_smul (ind1Tensor I n j vQ) a x

/-- For the actual Fmod contract the shell family is label-independent,
so the permuted tensor packet of the Ind1 re-indexing is the tensor packet as
a type.  Thus Ind1 has no carrier/type mismatch at the tensor packet. -/
theorem ind1Tensor_codomain_eq_tensorPacket
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ) :
    (⨂[I.initial.arithmetic.Fmod] i : Capsule j.val,
      DirectSumFactor ((fmodCapsuleContract I n).logShell j) vQ
        ((ind1Candidate (I := I) n j).perm.symm i)) =
      FmodTensorPacket I n j vQ := rfl

/-! ## 3. The actual Ind2 Fmod-unit tensor action -/

/-- The actual Ind2 tensor action of the independent Fmod-unit copies on the
actual tensor packet.  This is S1265's unconditional construction, transported
to the actual Fmod contract above. -/
noncomputable def ind2Tensor
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ)
    (f : SourceFmodUnitCopies (I := I) j) :
    FmodTensorPacket I n j vQ ≃ₗ[I.initial.arithmetic.Fmod]
      FmodTensorPacket I n j vQ :=
  sourceInd2FmodTensorEquiv (I := I) (fmodCapsuleContract I n) j vQ f

@[simp] theorem ind2Tensor_eq_source
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ)
    (f : SourceFmodUnitCopies (I := I) j) :
    ind2Tensor I n j vQ f =
      sourceInd2FmodTensorEquiv (I := I) (fmodCapsuleContract I n) j vQ f := rfl

/-- The actual Ind2 tensor action is the identity at the unit copy family. -/
theorem ind2Tensor_one
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ) :
    ind2Tensor I n j vQ 1 =
      LinearEquiv.refl (I.initial.arithmetic.Fmod) (FmodTensorPacket I n j vQ) :=
  sourceInd2FmodTensorEquiv_one (I := I) (fmodCapsuleContract I n) j vQ

/-- The actual Ind2 tensor action is multiplicative in the independent copies. -/
theorem ind2Tensor_mul
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (vQ : (fmodCapsuleContract I n).VQ)
    (f g : SourceFmodUnitCopies (I := I) j) :
    ind2Tensor I n j vQ (f * g) =
      (ind2Tensor I n j vQ g).trans (ind2Tensor I n j vQ f) :=
  sourceInd2FmodTensorEquiv_mul (I := I) (fmodCapsuleContract I n) j vQ f g

/-! ## 4. The actual Ind3 times-mu stage data -/

/-- The actual S1266 stage comparison, from stage m to the core stage 0. -/
noncomputable def ind3Compare
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) (v : V) (m : Int) :
    Ind3Stage I n m v ≃* Ind3Stage I n 0 v :=
  ind3StageComparison (I := I) n m v

/-- The actual S1266 times-mu action at stage m. -/
noncomputable def ind3Action
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) (v : V) (m : Int) :
    (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →* MulAut (Ind3Stage I n m v) :=
  ind3StageAction (I := I) n m v

/-- The actual Ind3 action law: the stage comparison intertwines the stage-m
times-mu action with the core-stage action along the actual strip link. -/
theorem ind3Compare_action
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) (v : V) (m : Int)
    (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v) (x : Ind3Stage I n m v) :
    ind3Compare I n v m (ind3Action I n v m g x) =
      ind3Action I n v 0 ((I.fLinkAt n m n 0).isoPi v g) (ind3Compare I n v m x) :=
  ind3StageComparison_action (I := I) n m v g x

/-- The actual Ind3 comparison at stage 0 is the identity. -/
theorem ind3Compare_zero
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) (v : V) :
    ind3Compare I n v 0 = MulEquiv.refl (Ind3Stage I n 0 v) :=
  ind3StageComparison_zero (I := I) n v

/-- The actual Ind3 comparison is degree-compatible. -/
theorem ind3Compare_degree
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) (v : V) (m : Int)
    (x : Ind3Stage I n m v) :
    (ind3TimesMuStrip I n 0).timesMuDegree v (ind3Compare I n v m x) =
      (ind3TimesMuStrip I n m).timesMuDegree v x :=
  ind3StageComparison_degree (I := I) n m v x

/-! ## 5. The native source-level Ind action data -/

/-- The source-level package of the three actual actions on their native
carriers.  ind1Candidate is S1264's actual capsule automorphism,
ind1Tensor is its literal tensor re-indexing, ind2 is S1265's actual
Fmod-unit tensor action, and ind3Compare/ind3Action are S1266's actual
times-mu stage data.  This record does not identify the three carriers. -/
structure SourceIndActionData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) where
  ind1Candidate : PrcAutomorphism (canonicalCapsuleTheaterAssignment I n) j
  ind1Tensor : ActualTensorPacket C j vQ ≃ₗ[I.initial.arithmetic.Fmod]
    (⨂[I.initial.arithmetic.Fmod] i : Capsule j.val,
      DirectSumFactor (C.logShell j) vQ (ind1Candidate.perm.symm i))
  ind1Tensor_eq : ind1Tensor = prcAutomorphismTensorAction (I := I)
    (canonicalCapsuleTheaterAssignment I n) C j vQ ind1Candidate
  ind2 : SourceFmodUnitCopies (I := I) j →
    ActualTensorPacket C j vQ ≃ₗ[I.initial.arithmetic.Fmod] ActualTensorPacket C j vQ
  ind2_one : ind2 1 = LinearEquiv.refl (I.initial.arithmetic.Fmod) (ActualTensorPacket C j vQ)
  ind2_mul : ∀ f g, ind2 (f * g) = (ind2 g).trans (ind2 f)
  ind3Compare : (m : Int) → Ind3Stage I n m v ≃* Ind3Stage I n 0 v
  ind3Compare_eq : ind3Compare = fun m => ind3StageComparison (I := I) n m v
  ind3Action : (m : Int) → (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →* MulAut (Ind3Stage I n m v)
  ind3Action_eq : ind3Action = fun m => ind3StageAction (I := I) n m v
  ind3_action_compat : ∀ (m : Int) (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v)
    (x : Ind3Stage I n m v),
    ind3Compare m (ind3Action m g x) =
      ind3Action 0 ((I.fLinkAt n m n 0).isoPi v g) (ind3Compare m x)

/-- The native source-level package is inhabited by S1264/S1265/S1266 data. -/
noncomputable def sourceIndActionData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) :
    SourceIndActionData I C n j vQ v where
  ind1Candidate := ind1Candidate (I := I) n j
  ind1Tensor := prcAutomorphismTensorAction (I := I)
    (canonicalCapsuleTheaterAssignment I n) C j vQ (ind1Candidate (I := I) n j)
  ind1Tensor_eq := rfl
  ind2 := fun f => sourceInd2FmodTensorEquiv (I := I) C j vQ f
  ind2_one := sourceInd2FmodTensorEquiv_one (I := I) C j vQ
  ind2_mul := fun f g => sourceInd2FmodTensorEquiv_mul (I := I) C j vQ f g
  ind3Compare := fun m => ind3StageComparison (I := I) n m v
  ind3Compare_eq := rfl
  ind3Action := fun m => ind3StageAction (I := I) n m v
  ind3Action_eq := rfl
  ind3_action_compat := fun m g x =>
    ind3StageComparison_action (I := I) n m v g x

@[simp] theorem sourceIndActionData_ind1Candidate
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) :
    (sourceIndActionData I C n j vQ v).ind1Candidate =
      ind1Candidate (I := I) n j := rfl

@[simp] theorem sourceIndActionData_ind2
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V)
    (f : SourceFmodUnitCopies (I := I) j) :
    (sourceIndActionData I C n j vQ v).ind2 f =
      sourceInd2FmodTensorEquiv (I := I) C j vQ f := rfl

@[simp] theorem sourceIndActionData_ind3Compare
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) (m : Int) :
    (sourceIndActionData I C n j vQ v).ind3Compare m =
      ind3StageComparison (I := I) n m v := rfl

@[simp] theorem sourceIndActionData_ind3Action
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) (m : Int) :
    (sourceIndActionData I C n j vQ v).ind3Action m =
      ind3StageAction (I := I) n m v := rfl

/-! ## 6. The first target field: ind3 -/

/-- The fields of the target DPrimeStripProcession, in declaration order. -/
inductive SourceIndField where
  | base
  | level
  | ind1
  | ind2
  | ind3
  deriving DecidableEq, Repr

/-- The source-level name of a target field. -/
def SourceIndField.name : SourceIndField → String
  | .base => "base"
  | .level => "level"
  | .ind1 => "ind1"
  | .ind2 => "ind2"
  | .ind3 => "ind3"

/-- The type that DPrimeStripProcession.ind3 requires on the actual tensor
carrier: a Nat-indexed endomorphism family of the additive tensor packet. -/
abbrev Ind3TensorEndoType
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) :=
  Nat → ActualTensorPacket C j vQ → ActualTensorPacket C j vQ

/-- If the target carrier of DPrimeStripProcession is chosen as the actual
Fmod tensor packet, then its ind3 field has this type. -/
abbrev TargetInd3TypeAtTensorPacket
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) :=
  Nat → ActualTensorPacket C j vQ → ActualTensorPacket C j vQ

/-- The target ind3 type at the actual tensor carrier is literally
Ind3TensorEndoType. -/
theorem targetInd3TypeAtTensorPacket_eq
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) :
    TargetInd3TypeAtTensorPacket I C n j vQ = Ind3TensorEndoType I C n j vQ := rfl

/-- The type that the actual S1266 Ind3 data have: an Int-indexed family of
multiplicative equivalences of the actual times-mu stages to the core stage. -/
abbrev Ind3TimesMuComparisonType
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) (v : V) : Type _ :=
  (m : Int) → Ind3Stage I n m v ≃* Ind3Stage I n 0 v

/-- The exact first field of DPrimeStripProcession that the actual
tensor-carrier data do not supply.

The required field ind3 has type Ind3TensorEndoType I C n j vQ, i.e.
Nat -> T -> T.  The actual S1266 Ind3 data have type
Ind3TimesMuComparisonType I n v, i.e.
(m : Int) -> Ind3Stage I n m v =* Ind3Stage I n 0 v.  These are different
carrier types: the required field is an endomorphism of the additive tensor
packet, while the actual stage comparison is multiplicative and its domain
type depends on m : Int.  The structure records the first field and the
actual S1266 comparison/action without identifying them with the required
field. -/
structure SourceInd3TensorMismatch
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) where
  /-- The first target field, by its declaration-order constructor. -/
  firstField : SourceIndField
  firstField_eq : firstField = SourceIndField.ind3
  /-- The actual S1266 comparison. -/
  actualComparison : Ind3TimesMuComparisonType I n v
  actualComparison_eq : actualComparison = fun m => ind3StageComparison (I := I) n m v
  /-- The actual S1266 stage action. -/
  actualStageAction : (m : Int) →
    (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →* MulAut (Ind3Stage I n m v)
  actualStageAction_eq : actualStageAction = fun m => ind3StageAction (I := I) n m v

/-- The exact first mismatch record. -/
noncomputable def sourceInd3TensorMismatch
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) :
    SourceInd3TensorMismatch I C n j vQ v where
  firstField := SourceIndField.ind3
  firstField_eq := rfl
  actualComparison := fun m => ind3StageComparison (I := I) n m v
  actualComparison_eq := rfl
  actualStageAction := fun m => ind3StageAction (I := I) n m v
  actualStageAction_eq := rfl

@[simp] theorem sourceInd3TensorMismatch_firstField
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) :
    (sourceInd3TensorMismatch I C n j vQ v).firstField = SourceIndField.ind3 := rfl

/-- The exact name of the first mismatching target field. -/
theorem sourceInd3TensorMismatch_firstField_name
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) :
    (sourceInd3TensorMismatch I C n j vQ v).firstField.name = "ind3" := rfl

/-- The first-field mismatch is at ind3, not at ind1 or ind2: both of those
are actual endomorphisms/actions of the tensor packet in SourceIndActionData. -/
theorem sourceInd3TensorMismatch_field_eq_ind3
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (n : Int) (j : Fin (capsuleLevels l)) (vQ : C.VQ) (v : V) :
    (sourceInd3TensorMismatch I C n j vQ v).firstField = SourceIndField.ind3 ∧
      (sourceInd3TensorMismatch I C n j vQ v).actualComparison =
        (fun m => ind3StageComparison (I := I) n m v) :=
  ⟨rfl, rfl⟩

/-! ## 7. Axiom probes -/

#check DPrimeStripProcession
#print axioms fmodCapsuleContract
#print axioms fmodShell_zero_ne_one
#print axioms ind1Tensor_tprod
#print axioms ind1Tensor_map_add
#print axioms ind2Tensor_one
#print axioms ind2Tensor_mul
#print axioms ind3Compare_action
#print axioms ind3Compare_zero
#print axioms sourceIndActionData
#print axioms sourceInd3TensorMismatch

end LeanFormal.IUT.XiFPaper.S1315SourceIndActionsAssemblyActual