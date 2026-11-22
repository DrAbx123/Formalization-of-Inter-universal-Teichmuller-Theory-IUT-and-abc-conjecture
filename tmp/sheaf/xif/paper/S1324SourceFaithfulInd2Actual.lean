import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S1324: the source-faithful Ind2 summand action

## Source anchor

IUT III, Theorem 3.11, (i), lines 9258--9272 of the corpus text: (Ind2) is
induced, for each v_Q and each capsule level j, by the action of

* independent copies of Ism at the nonarchimedean places (IUT II,
  Proposition 1.2, (vi)), and
* copies of the order-two automorphisms at the archimedean places (IUT II,
  Proposition 1.2, (vii)),

on each of the direct summands of the j+1 tensor factors appearing in
I_Q(S^+-_{j+1}; n, D^vdash_{v_Q}).

The earlier S1265 file uses scalar units of the source base field (or a
real coefficient field) as the per-factor group.  That is not the source
group: Ism is the group of Kummer isometries of the times-mu quotient, and
the archimedean indeterminacy is the independent sign group, not a
field-unit scalar action.

This file constructs the source-faithful shape:

* NonarchimedeanInd2SummandSymmetry M carries an actual G ->* MulAut U and
  the actual subgroup TimesMuKummer.Ism rho <= MulAut (TimesMuQuotient U),
  together with its Q-linear action on the summand M;
* ArchimedeanInd2SummandSymmetry M carries the actual group
  factorIndex -> Multiplicative (ZMod 2), together with its Q-linear
  action on M;
* SourceInd2SummandSymmetry M kind is the source alternative, with GroupType
  definitionally equal to the two actual groups above.

The direct-sum action on the places over v_Q and the tensor-packet action on
the j+1 factors are then derived, with the proved laws.  The action on a
single summand is the prescribed one and every other summand/factor is fixed
(the factor action is componentwise; the tensor action is the PiTensorProduct
of the factor actions).

## The exact first field

The remaining source input is exactly the per-summand symmetry datum
SourceFaithfulInd2SummandSymmetryField, i.e. the field

  symmetry : (i : Capsule j.val) -> (v : C.place vQ) ->
    SourceInd2SummandSymmetry (Shell i vQ v) kind

of SourceFaithfulInd2SummandAction.  The log-shell carrier itself is already
the actual C.logShell j of the capsule contract.  No field-unit or real-unit
scalar replacement is used anywhere in this file.

No proof placeholder and no new axiom is used.
-/

namespace LeanFormal.IUT.XiFPaper.S1324SourceFaithfulInd2Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open scoped TensorProduct

universe u ua uv upi umon ui uShell

/-! ## 1. The two actual source symmetry groups -/

/-- The place kind distinguishing the two (Ind2) alternatives. -/
inductive SourceInd2Kind where
  | nonarchimedean
  | archimedean
  deriving DecidableEq, Repr

/-- The actual nonarchimedean Ism action on one direct summand.

rho : G ->* MulAut U is the actual local action on the times-mu module of the
source place (the source Kummer data).  The group is literally
TimesMuKummer.Ism rho, a subgroup of MulAut (TimesMuQuotient U), and action
is its Q-linear action on the summand M. -/
structure NonarchimedeanInd2SummandSymmetry (M : Type u)
    [AddCommMonoid M] [Module ℚ M] where
  G : Type u
  [groupG : Group G]
  [topologicalSpaceG : TopologicalSpace G]
  U : Type u
  [commGroupU : CommGroup U]
  rho : G →* MulAut U
  action : TimesMuKummer.Ism rho → M ≃ₗ[ℚ] M
  action_one : ∀ value, action 1 value = value
  action_mul :
    ∀ first second value,
      action (first * second) value = action first (action second value)

attribute [instance]
  NonarchimedeanInd2SummandSymmetry.groupG
  NonarchimedeanInd2SummandSymmetry.topologicalSpaceG
  NonarchimedeanInd2SummandSymmetry.commGroupU

/-- The actual archimedean order-two action on one direct summand.

The group is literally factorIndex -> Multiplicative (ZMod 2): one
independent sign for every archimedean direct factor, as in IUT II,
Proposition 1.2, (vii). -/
structure ArchimedeanInd2SummandSymmetry (M : Type u)
    [AddCommMonoid M] [Module ℚ M] where
  factorIndex : Type u
  [fintypeFactorIndex : Fintype factorIndex]
  action : (factorIndex → Multiplicative (ZMod 2)) → M ≃ₗ[ℚ] M
  action_one : ∀ value, action 1 value = value
  action_mul :
    ∀ first second value,
      action (first * second) value = action first (action second value)

attribute [instance]
  ArchimedeanInd2SummandSymmetry.fintypeFactorIndex

/-- The source-faithful Ind2 symmetry on one direct summand: the actual
nonarchimedean Ism subgroup or the actual archimedean sign group, with its
Q-linear action. -/
inductive SourceInd2SummandSymmetry (M : Type u)
    [AddCommMonoid M] [Module ℚ M] : SourceInd2Kind → Type (u + 1) where
  | nonarchimedean (data : NonarchimedeanInd2SummandSymmetry M) :
      SourceInd2SummandSymmetry M .nonarchimedean
  | archimedean (data : ArchimedeanInd2SummandSymmetry M) :
      SourceInd2SummandSymmetry M .archimedean

/-- The finite ZMod 2 addition law used for the archimedean order-two
condition. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

namespace SourceInd2SummandSymmetry

variable {M : Type u} [AddCommMonoid M] [Module ℚ M]
variable {kind : SourceInd2Kind}

/-- The actual group carried by a source symmetry datum.  In the
nonarchimedean case this is TimesMuKummer.Ism rho; in the archimedean case
it is factorIndex -> Multiplicative (ZMod 2). -/
def GroupType (data : SourceInd2SummandSymmetry M kind) : Type u :=
  match data with
  | .nonarchimedean d => TimesMuKummer.Ism d.rho
  | .archimedean d => d.factorIndex → Multiplicative (ZMod 2)

/-- The nonarchimedean group is literally the actual Ism subgroup of the
times-mu quotient. -/
@[simp] theorem groupType_nonarchimedean
    (d : NonarchimedeanInd2SummandSymmetry M) :
    (SourceInd2SummandSymmetry.nonarchimedean d).GroupType =
      TimesMuKummer.Ism d.rho := rfl

/-- The archimedean group is literally the independent sign group. -/
@[simp] theorem groupType_archimedean
    (d : ArchimedeanInd2SummandSymmetry M) :
    (SourceInd2SummandSymmetry.archimedean d).GroupType =
      (d.factorIndex → Multiplicative (ZMod 2)) := rfl

instance instGroup (data : SourceInd2SummandSymmetry M kind) :
    Group data.GroupType := by
  cases data with
  | nonarchimedean d =>
      change Group (TimesMuKummer.Ism d.rho)
      infer_instance
  | archimedean d =>
      change Group (d.factorIndex → Multiplicative (ZMod 2))
      infer_instance

/-- The Q-linear action of the actual source group on the summand. -/
def action (data : SourceInd2SummandSymmetry M kind) :
    data.GroupType → M ≃ₗ[ℚ] M :=
  match data with
  | .nonarchimedean d => d.action
  | .archimedean d => d.action

theorem action_one (data : SourceInd2SummandSymmetry M kind) (value : M) :
    data.action 1 value = value := by
  cases data with
  | nonarchimedean d => exact d.action_one value
  | archimedean d => exact d.action_one value

theorem action_mul (data : SourceInd2SummandSymmetry M kind)
    (first second : data.GroupType) (value : M) :
    data.action (first * second) value =
      data.action first (data.action second value) := by
  cases data with
  | nonarchimedean d => exact d.action_mul first second value
  | archimedean d => exact d.action_mul first second value

/-- At an archimedean place every source Ind2 symmetry has order dividing two. -/
theorem square_of_archimedean (data : SourceInd2SummandSymmetry M kind)
    (hkind : kind = .archimedean) (choice : data.GroupType) :
    choice * choice = 1 := by
  cases data with
  | nonarchimedean d => cases hkind
  | archimedean d =>
      funext factor
      apply Multiplicative.toAdd.injective
      change (choice factor).toAdd + (choice factor).toAdd =
        (1 : Multiplicative (ZMod 2)).toAdd
      rw [show (1 : Multiplicative (ZMod 2)).toAdd = 0 by rfl]
      exact zmod2_add_self (choice factor).toAdd

end SourceInd2SummandSymmetry

/-! ## 2. The source-faithful per-summand datum on the actual log-shell family -/

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The source-faithful (Ind2) summand datum for one tensor factor over v_Q.

The symmetry field is the exact first field: for every capsule label i and
every place v over v_Q, the actual source symmetry on the actual log-shell
Shell i vQ v of the capsule contract.  The field type is
SourceInd2SummandSymmetry, so the nonarchimedean case is literally
TimesMuKummer.Ism rho and the archimedean case is literally
factorIndex -> Multiplicative (ZMod 2). -/
structure SourceFaithfulInd2SummandAction (kind : SourceInd2Kind)
    (C : SourceProcessionCapsuleContract ℚ l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) where
  symmetry : (i : Capsule j.val) → (v : C.place vQ) →
    SourceInd2SummandSymmetry ((C.logShell j).Shell i vQ v) kind

namespace SourceFaithfulInd2SummandAction

variable {kind : SourceInd2Kind}
variable {C : SourceProcessionCapsuleContract ℚ l V I}
variable {j : Fin (capsuleLevels l)} {vQ : C.VQ}

/-- The actual source group at one summand. -/
abbrev summandSymmetry (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val) (v : C.place vQ) : Type uShell :=
  (D.symmetry i v).GroupType

instance summandSymmetryGroup (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val) (v : C.place vQ) : Group (D.summandSymmetry i v) :=
  SourceInd2SummandSymmetry.instGroup (D.symmetry i v)

/-- The Q-linear action of the actual source group on its own summand. -/
def summandAction (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val) (v : C.place vQ) :
    D.summandSymmetry i v →
      (C.logShell j).Shell i vQ v ≃ₗ[ℚ] (C.logShell j).Shell i vQ v :=
  (D.symmetry i v).action

theorem summandAction_one (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val) (v : C.place vQ)
    (value : (C.logShell j).Shell i vQ v) :
    D.summandAction i v 1 value = value :=
  (D.symmetry i v).action_one value

theorem summandAction_mul (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val) (v : C.place vQ)
    (first second : D.summandSymmetry i v)
    (value : (C.logShell j).Shell i vQ v) :
    D.summandAction i v (first * second) value =
      D.summandAction i v first (D.summandAction i v second value) :=
  (D.symmetry i v).action_mul first second value

/-- The archimedean order-two condition, transported to the source-faithful
summand datum. -/
theorem summandSymmetry_square_of_archimedean
    (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (hkind : kind = .archimedean)
    (i : Capsule j.val) (v : C.place vQ)
    (choice : D.summandSymmetry i v) :
    choice * choice = 1 :=
  (D.symmetry i v).square_of_archimedean hkind choice

/-! ## 3. The direct-sum factor action over the places above v_Q -/

/-- The action on the direct sum of the log-shells over all places above v_Q.
It is componentwise: the summand (i, v) receives its own source symmetry and
every other summand is fixed. -/
noncomputable def factorAction (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val)
    (choices : (v : C.place vQ) → D.summandSymmetry i v) :
    DirectSumFactor (C.logShell j) vQ i ≃ₗ[ℚ]
      DirectSumFactor (C.logShell j) vQ i :=
  LinearEquiv.piCongrRight (fun v => D.summandAction i v (choices v))

@[simp] theorem factorAction_apply
    (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val)
    (choices : (v : C.place vQ) → D.summandSymmetry i v)
    (x : DirectSumFactor (C.logShell j) vQ i) (v : C.place vQ) :
    D.factorAction i choices x v = D.summandAction i v (choices v) (x v) :=
  LinearEquiv.piCongrRight_apply (fun v => D.summandAction i v (choices v)) x v

theorem factorAction_one (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val)
    (x : DirectSumFactor (C.logShell j) vQ i) :
    D.factorAction i (1 : (v : C.place vQ) → D.summandSymmetry i v) x = x := by
  ext v
  rw [factorAction_apply]
  exact D.summandAction_one i v (x v)

theorem factorAction_mul (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val)
    (first second : (v : C.place vQ) → D.summandSymmetry i v)
    (x : DirectSumFactor (C.logShell j) vQ i) :
    D.factorAction i (first * second) x =
      D.factorAction i first (D.factorAction i second x) := by
  ext v
  rw [factorAction_apply, factorAction_apply, factorAction_apply, Pi.mul_apply]
  exact D.summandAction_mul i v (first v) (second v) (x v)

/-- If the v-component of x is zero, then the factor action keeps the
v-component zero: the action is on the direct sum and fixes each other
summand. -/
theorem factorAction_apply_of_eq_zero
    (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val)
    (choices : (v : C.place vQ) → D.summandSymmetry i v)
    (x : DirectSumFactor (C.logShell j) vQ i) (v : C.place vQ)
    (hx : x v = 0) :
    D.factorAction i choices x v = 0 := by
  rw [factorAction_apply, hx, map_zero]

/-- The other-summands-are-fixed law: a vector supported away from the
summand w remains supported away from w after the factor action. -/
theorem factorAction_fixes_other_summand
    (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val)
    (choices : (v : C.place vQ) → D.summandSymmetry i v)
    (w : C.place vQ) (x : DirectSumFactor (C.logShell j) vQ i)
    (hx : ∀ v, v ≠ w → x v = 0) :
    ∀ v, v ≠ w → D.factorAction i choices x v = 0 := by
  intro v hv
  exact D.factorAction_apply_of_eq_zero i choices x v (hx v hv)

/-- On the single summand w, the factor action is exactly the prescribed
source action: the inclusion of the w-summand is natural for the action. -/
theorem factorAction_single [DecidableEq (C.place vQ)]
    (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val)
    (choices : (v : C.place vQ) → D.summandSymmetry i v)
    (w : C.place vQ) (value : (C.logShell j).Shell i vQ w) :
    D.factorAction i choices (Pi.single w value) =
      Pi.single w (D.summandAction i w (choices w) value) := by
  ext v
  by_cases hv : v = w
  · subst hv
    rw [factorAction_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [factorAction_apply, Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, map_zero]

/-! ## 4. The tensor-packet action on the j+1 factors -/

/-- The actual tensor-packet action: the PiTensorProduct of the factor
actions.  Each factor uses only its own independent source symmetry. -/
noncomputable def packetAction (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (choices : (i : Capsule j.val) →
      (v : C.place vQ) → D.summandSymmetry i v) :
    TensorPacket (C.logShell j) vQ ≃ₗ[ℚ]
      TensorPacket (C.logShell j) vQ :=
  PiTensorProduct.congr (fun i => D.factorAction i (choices i))

/-- Compatibility with pure tensors: the tensor-packet action is the tensor
product of the factor actions. -/
theorem packetAction_tprod (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (choices : (i : Capsule j.val) →
      (v : C.place vQ) → D.summandSymmetry i v)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    D.packetAction choices (PiTensorProduct.tprod ℚ x) =
      PiTensorProduct.tprod ℚ
        (fun i => D.factorAction i (choices i) (x i)) :=
  PiTensorProduct.congr_tprod (fun i => D.factorAction i (choices i)) x

/-- The identity source choice acts by the identity on the tensor packet. -/
theorem packetAction_one (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (x : TensorPacket (C.logShell j) vQ) :
    D.packetAction 1 x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [map_smul, packetAction_tprod]
      have hfun : (fun i => D.factorAction i
          ((1 : (i : Capsule j.val) → (v : C.place vQ) →
            D.summandSymmetry i v) i) (x i)) = x := by
        funext i
        exact D.factorAction_one i (x i)
      rw [hfun]
  | add x y hx hy =>
      rw [map_add, hx, hy]

/-- The tensor-packet action is multiplicative: first applying second and
then first is the action of the coordinatewise product. -/
theorem packetAction_mul (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (first second : (i : Capsule j.val) →
      (v : C.place vQ) → D.summandSymmetry i v)
    (x : TensorPacket (C.logShell j) vQ) :
    D.packetAction (first * second) x =
      D.packetAction first (D.packetAction second x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [map_smul, map_smul, map_smul, packetAction_tprod,
        packetAction_tprod, packetAction_tprod]
      have hfun : (fun i => D.factorAction i ((first * second) i) (x i)) =
          (fun i => D.factorAction i (first i)
            (D.factorAction i (second i) (x i))) := by
        funext i
        exact D.factorAction_mul i (first i) (second i) (x i)
      rw [hfun]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]

/-- A factor whose source choice is the identity is fixed pointwise: the
tensor action does not mix the factors. -/
theorem packetAction_tprod_factor_fixed
    (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (choices : (i : Capsule j.val) →
      (v : C.place vQ) → D.summandSymmetry i v)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i)
    (i : Capsule j.val) (hchoice : choices i = 1) :
    D.factorAction i (choices i) (x i) = x i := by
  rw [hchoice, D.factorAction_one]

/-! ## 5. The exact first field: symmetry on the actual log-shell carrier -/

/-- The exact first field of the source-faithful (Ind2) datum: for every
capsule label i and every place v over v_Q, the actual source symmetry
on the actual log-shell Shell i vQ v.

The carrier is already the actual C.logShell j; this field is precisely the
per-summand source symmetry datum.  It is the symmetry field of
SourceFaithfulInd2SummandAction. -/
abbrev SourceFaithfulInd2SummandSymmetryField (kind : SourceInd2Kind)
    (C : SourceProcessionCapsuleContract ℚ l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :=
  (i : Capsule j.val) → (v : C.place vQ) →
    SourceInd2SummandSymmetry ((C.logShell j).Shell i vQ v) kind

/-- The exact first field, named explicitly: the per-summand source
symmetry datum on the actual log-shell carrier. -/
abbrev SourceFaithfulInd2FirstField (kind : SourceInd2Kind)
    (C : SourceProcessionCapsuleContract ℚ l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :=
  SourceFaithfulInd2SummandSymmetryField kind C j vQ

/-- The exact first field is literally the symmetry field of the full
source-faithful summand action. -/
theorem sourceFaithfulInd2FirstField_eq_symmetry
    (D : SourceFaithfulInd2SummandAction kind C j vQ) :
    (D.symmetry : SourceFaithfulInd2FirstField kind C j vQ) =
      D.symmetry := rfl

/-- The full source-faithful Ind2 summand action is exactly its first field. -/
def ofSymmetryField
    (F : SourceFaithfulInd2SummandSymmetryField kind C j vQ) :
    SourceFaithfulInd2SummandAction kind C j vQ where
  symmetry := F

/-- The first field of a source-faithful Ind2 summand action. -/
def toSymmetryField (D : SourceFaithfulInd2SummandAction kind C j vQ) :
    SourceFaithfulInd2SummandSymmetryField kind C j vQ :=
  D.symmetry

@[simp] theorem toSymmetryField_ofSymmetryField
    (F : SourceFaithfulInd2SummandSymmetryField kind C j vQ) :
    (ofSymmetryField F).toSymmetryField = F := rfl

@[simp] theorem ofSymmetryField_toSymmetryField
    (D : SourceFaithfulInd2SummandAction kind C j vQ) :
    ofSymmetryField D.toSymmetryField = D := rfl

/-- The exact first field, exposed at one summand. -/
abbrev SourceInd2SummandSymmetryField (kind : SourceInd2Kind)
    (M : Type uShell) [AddCommMonoid M] [Module ℚ M] : Type (uShell + 1) :=
  SourceInd2SummandSymmetry M kind

/-- Exactness at one summand: the symmetry field of the packet datum is
literally the per-summand source symmetry datum. -/
theorem symmetryField_apply (D : SourceFaithfulInd2SummandAction kind C j vQ)
    (i : Capsule j.val) (v : C.place vQ) :
    D.toSymmetryField i v = D.symmetry i v := rfl

end SourceFaithfulInd2SummandAction

/-! ## 6. Axiom probes -/

#print axioms SourceInd2SummandSymmetry.groupType_nonarchimedean
#print axioms SourceInd2SummandSymmetry.groupType_archimedean
#print axioms SourceInd2SummandSymmetry.action_one
#print axioms SourceInd2SummandSymmetry.action_mul
#print axioms SourceInd2SummandSymmetry.square_of_archimedean
#print axioms SourceFaithfulInd2SummandAction.summandAction_one
#print axioms SourceFaithfulInd2SummandAction.factorAction
#print axioms SourceFaithfulInd2SummandAction.factorAction_one
#print axioms SourceFaithfulInd2SummandAction.factorAction_mul
#print axioms SourceFaithfulInd2SummandAction.factorAction_fixes_other_summand
#print axioms SourceFaithfulInd2SummandAction.factorAction_single
#print axioms SourceFaithfulInd2SummandAction.packetAction
#print axioms SourceFaithfulInd2SummandAction.packetAction_tprod
#print axioms SourceFaithfulInd2SummandAction.packetAction_one
#print axioms SourceFaithfulInd2SummandAction.packetAction_mul
#print axioms SourceFaithfulInd2SummandAction.packetAction_tprod_factor_fixed
#print axioms SourceFaithfulInd2SummandAction.toSymmetryField_ofSymmetryField
#print axioms SourceFaithfulInd2SummandAction.sourceFaithfulInd2FirstField_eq_symmetry

end LeanFormal.IUT.XiFPaper.S1324SourceFaithfulInd2Actual

end
/-! ## 7. Non-vacuity models for the two actual source groups -/

namespace LeanFormal.IUT.XiFPaper.S1324SourceFaithfulInd2Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1324SourceFaithfulInd2Actual

namespace Models

universe uM

/-- The nontrivial element of the archimedean sign group. -/
abbrev zmod2Sign : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem mul_zmod2_eq_one_or_sign (s : Multiplicative (ZMod 2)) :
    s = 1 ∨ s = zmod2Sign := by
  have h : s.toAdd = 0 ∨ s.toAdd = 1 := by
    generalize h' : s.toAdd = a
    fin_cases a
    · left; rfl
    · right; rfl
  rcases h with h | h
  · left
    apply Multiplicative.toAdd.injective
    simpa [zmod2Sign] using h
  · right
    apply Multiplicative.toAdd.injective
    simpa [zmod2Sign] using h

/-- The order-two sign action on a single factor module. -/
noncomputable def signLinearEquiv {N : Type uM} [AddCommMonoid N] [Module ℚ N]
    (s : Multiplicative (ZMod 2)) : N ≃ₗ[ℚ] N := by
  letI := Module.addCommMonoidToAddCommGroup ℚ (M := N)
  exact if s = 1 then LinearEquiv.refl ℚ N else LinearEquiv.neg ℚ

theorem signLinearEquiv_one {N : Type uM} [AddCommMonoid N] [Module ℚ N] :
    signLinearEquiv (N := N) 1 = LinearEquiv.refl ℚ N := by
  unfold signLinearEquiv
  simp

theorem zmod2Sign_mul_self : zmod2Sign * zmod2Sign = 1 := by
  apply Multiplicative.toAdd.injective
  change (1 : ZMod 2) + 1 = 0
  decide

theorem signLinearEquiv_mul {N : Type uM} [AddCommMonoid N] [Module ℚ N]
    (s t : Multiplicative (ZMod 2)) :
    signLinearEquiv (N := N) (s * t) =
      (signLinearEquiv (N := N) t).trans (signLinearEquiv (N := N) s) := by
  letI := Module.addCommMonoidToAddCommGroup ℚ (M := N)
  rcases mul_zmod2_eq_one_or_sign s with rfl | rfl <;>
    rcases mul_zmod2_eq_one_or_sign t with rfl | rfl <;>
    simp [signLinearEquiv, zmod2Sign_mul_self]
  · ext value
    simp [LinearEquiv.trans_apply]

/-- The actual archimedean sign action on a direct product of one local factor
for every archimedean direct factor.  This is a genuine instance of the
archimedean branch of SourceInd2SummandSymmetry; it is the source-shaped
product module, not a scalar surrogate. -/
noncomputable def archimedeanProductSymmetry {ι : Type uM} [Fintype ι]
    (N : Type uM) [AddCommMonoid N] [Module ℚ N] :
    ArchimedeanInd2SummandSymmetry (ι → N) where
  factorIndex := ι
  fintypeFactorIndex := inferInstance
  action σ := LinearEquiv.piCongrRight (fun i => signLinearEquiv (N := N) (σ i))
  action_one value := by
    ext i
    simp [signLinearEquiv_one]
  action_mul first second value := by
    ext i
    simp [signLinearEquiv_mul]

/-- The archimedean branch is inhabited by the actual sign group and its
product action. -/
theorem archimedeanProductSymmetry_nonempty {ι : Type uM} [Fintype ι]
    (N : Type uM) [AddCommMonoid N] [Module ℚ N] :
    Nonempty (SourceInd2SummandSymmetry (ι → N) .archimedean) :=
  ⟨.archimedean (archimedeanProductSymmetry N)⟩

/-- The regular representation of the actual source Ism subgroup on the group
algebra of the actual times-mu quotient.  This is a genuine Q-linear action of
the actual source group, built from the quotient; it is not a field-unit or
real-unit scalar action. -/
noncomputable def regularIsmRepresentation
    {G U : Type uM} [Group G] [TopologicalSpace G] [CommGroup U]
    (rho : G →* MulAut U) :
    TimesMuKummer.Ism rho →*
      (MonoidAlgebra ℚ (TimesMuQuotient U) ≃ₐ[ℚ]
        MonoidAlgebra ℚ (TimesMuQuotient U)) :=
  (MonoidAlgebra.domCongrAut (R := ℚ) (A := ℚ)
    (M := TimesMuQuotient U)).comp (Subgroup.subtype (TimesMuKummer.Ism rho))

/-- The regular representation, viewed as a Q-linear equivalence. -/
noncomputable def regularIsmAction
    {G U : Type uM} [Group G] [TopologicalSpace G] [CommGroup U]
    (rho : G →* MulAut U) (g : TimesMuKummer.Ism rho) :
    MonoidAlgebra ℚ (TimesMuQuotient U) ≃ₗ[ℚ]
      MonoidAlgebra ℚ (TimesMuQuotient U) :=
  (regularIsmRepresentation rho g).toLinearEquiv

theorem regularIsmAction_one
    {G U : Type uM} [Group G] [TopologicalSpace G] [CommGroup U]
    (rho : G →* MulAut U) (value : MonoidAlgebra ℚ (TimesMuQuotient U)) :
    regularIsmAction rho 1 value = value := by
  change (regularIsmRepresentation rho 1).toLinearEquiv value = value
  rw [map_one, AlgEquiv.aut_one]
  rfl

theorem regularIsmAction_mul
    {G U : Type uM} [Group G] [TopologicalSpace G] [CommGroup U]
    (rho : G →* MulAut U) (first second : TimesMuKummer.Ism rho)
    (value : MonoidAlgebra ℚ (TimesMuQuotient U)) :
    regularIsmAction rho (first * second) value =
      regularIsmAction rho first (regularIsmAction rho second value) := by
  change (regularIsmRepresentation rho (first * second)).toLinearEquiv value =
    (regularIsmRepresentation rho first).toLinearEquiv
      ((regularIsmRepresentation rho second).toLinearEquiv value)
  rw [map_mul, AlgEquiv.aut_mul]
  rfl

/-- The source-faithful nonarchimedean symmetry data on the group algebra of
the actual times-mu quotient.  The group is exactly TimesMuKummer.Ism rho. -/
noncomputable def regularNonarchimedeanSymmetry
    {G U : Type uM} [Group G] [TopologicalSpace G] [CommGroup U]
    (rho : G →* MulAut U) :
    NonarchimedeanInd2SummandSymmetry (MonoidAlgebra ℚ (TimesMuQuotient U)) where
  G := G
  groupG := inferInstance
  topologicalSpaceG := inferInstance
  U := U
  commGroupU := inferInstance
  rho := rho
  action := regularIsmAction rho
  action_one := regularIsmAction_one rho
  action_mul := regularIsmAction_mul rho

/-- The nonarchimedean branch is inhabited by the actual Ism subgroup and its
regular Q-linear action. -/
theorem regularNonarchimedeanSymmetry_nonempty
    {G U : Type uM} [Group G] [TopologicalSpace G] [CommGroup U]
    (rho : G →* MulAut U) :
    Nonempty (SourceInd2SummandSymmetry
      (MonoidAlgebra ℚ (TimesMuQuotient U)) .nonarchimedean) :=
  ⟨.nonarchimedean (regularNonarchimedeanSymmetry rho)⟩

end Models



/-! ## 8. Axiom probes for the non-vacuity models -/

#print axioms Models.signLinearEquiv
#print axioms Models.archimedeanProductSymmetry
#print axioms Models.archimedeanProductSymmetry_nonempty
#print axioms Models.regularIsmRepresentation
#print axioms Models.regularIsmAction
#print axioms Models.regularIsmAction_one
#print axioms Models.regularIsmAction_mul
#print axioms Models.regularNonarchimedeanSymmetry
#print axioms Models.regularNonarchimedeanSymmetry_nonempty

end LeanFormal.IUT.XiFPaper.S1324SourceFaithfulInd2Actual