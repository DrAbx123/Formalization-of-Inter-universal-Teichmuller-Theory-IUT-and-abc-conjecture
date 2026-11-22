import tmp.sheaf.xif.paper.S1324SourceFaithfulInd2Actual
import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

/-!
# S1426: the actual per-summand analytic-shell Ind2 symmetry

Source anchor: IUT III, Theorem 3.11, (i), text lines 9258--9272.  (Ind2) is
induced, for each v_Q and each capsule level j, by independent copies of Ism at
the nonarchimedean places (IUT II, Proposition 1.2, (vi)) and copies of the
order-two automorphisms at the archimedean places (IUT II, Proposition 1.2,
(vii)), acting on each direct summand of the j+1 tensor factors in
I_Q(S^+-_{j+1}; n, D^vdash_{v_Q}).

S1324 records the source-faithful Ind2 assembly and leaves exactly the first
field

  symmetry : (i : Capsule j.val) -> (v : C.place vQ) ->
    SourceInd2SummandSymmetry ((C.logShell j).Shell i vQ v) kind.

This file constructs the actual analytic-shell symmetry representation behind
that field, without a Fmod-unit or real-unit scalar substitute:

* the nonarchimedean group is pinned to the actual local Kummer datum of a
  source F-prime-strip: the value group F.Mon w, the actual local action
  F.action w, and the actual Kummer isometry subgroup Ism (F.action w);
* the analytic-shell carrier is the actual capsule log-shell
  (C.logShell j).Shell i vQ v, and the local datum SourceLogShellDatum gives
  the actual log-coordinate field, invariant units, and log map.  The
  representation is on the actual IQSpan of that local log-shell and is
  transported to the capsule carrier only along an explicit Q-linear
  equivalence;
* the archimedean group is the actual independent sign group
  factorIndex -> Multiplicative (ZMod 2), and the concrete model uses the
  actual archimedean local field Complex with its order-two conjugation.

The exact remaining first field is named NonarchimedeanAnalyticShellDatum /
ArchimedeanAnalyticShellDatum: the per-summand representation of the actual
local Kummer group on the actual IQSpan (respectively, the Q-linear
identification with the actual archimedean conjugation model), together with the
Q-linear identification of the capsule shell.  The file proves that this datum
literally produces the S1324 symmetry and that its group type is
definitionally the actual Ism, respectively the actual sign group.

No proof placeholder, no new axiom, and no Fmod/Real scalar replacement.
-/

namespace LeanFormal.IUT.XiFPaper.S1426Ind2AnalyticSymmetryActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1324SourceFaithfulInd2Actual
open LeanFormal.IUT.XiFPaper.S1324SourceFaithfulInd2Actual.SourceFaithfulInd2SummandAction
open scoped TensorProduct

universe u v

/-! ## 1. The actual local Kummer datum at one source place -/

/-- The actual local Kummer input: a source F-prime-strip together with the
place whose local value group carries Ism.  The extra group and topology fields
record the actual local units and the local group topology; the generic
FPrimeStrip only records a commutative value monoid. -/
structure ActualLocalKummerDatum (V : Type v) where
  localF : FPrimeStrip.{u, v, u} V
  place : V
  U : Type u
  [commGroupU : CommGroup U]
  rho : localF.Pi place →* MulAut U
  [topologicalSpaceG : TopologicalSpace (localF.Pi place)]

attribute [instance] ActualLocalKummerDatum.commGroupU
  ActualLocalKummerDatum.topologicalSpaceG

namespace ActualLocalKummerDatum

variable {V : Type v} (L : ActualLocalKummerDatum.{u, v} V)

/-- The actual local Kummer group. -/
abbrev G : Type u := L.localF.Pi L.place

/-- The actual Kummer isometry group Ism of the local action. -/
abbrev Ism : Type u := ↥(TimesMuKummer.Ism L.rho)

theorem ism_def : L.Ism = ↥(TimesMuKummer.Ism L.rho) := rfl

/-- The concrete local Kummer datum at a rational prime, from the actual local
F-prime-strip.  The topology is the discrete topology used by the formal local
Galois layer. -/
noncomputable def localKummerDatumAtPrime (p : Nat) [Fact p.Prime] :
    ActualLocalKummerDatum (V := RationalPrimePlace) := by
  letI : CommGroup ((AlgebraicClosure ℚ_[p])ˣ) := inferInstance
  exact
    { localF := localFPrimeStrip
      place := ⟨p, Fact.out⟩
      U := (AlgebraicClosure ℚ_[p])ˣ
      commGroupU := inferInstance
      rho := localFPrimeStrip.action ⟨p, Fact.out⟩
      topologicalSpaceG := ⊥ }

end ActualLocalKummerDatum

/-! ## 2. Transport of a raw linear action across a Q-linear equivalence -/

/-- Transport a linear automorphism of N to M along e : M ~= N.  The direction
is chosen so that the transported action reads e.symm (a (e x)), exactly the
action on the source analytic shell. -/
noncomputable def transportAction {M N : Type u} [AddCommMonoid M] [Module ℚ M]
    [AddCommMonoid N] [Module ℚ N] (e : M ≃ₗ[ℚ] N) (a : N ≃ₗ[ℚ] N) :
    M ≃ₗ[ℚ] M :=
  e.trans (a.trans e.symm)

theorem transportAction_apply {M N : Type u} [AddCommMonoid M] [Module ℚ M]
    [AddCommMonoid N] [Module ℚ N] (e : M ≃ₗ[ℚ] N) (a : N ≃ₗ[ℚ] N) (x : M) :
    transportAction e a x = e.symm (a (e x)) := by
  simp [transportAction, LinearEquiv.trans_apply]

theorem transportAction_one {M N : Type u} [AddCommMonoid M] [Module ℚ M]
    [AddCommMonoid N] [Module ℚ N] (e : M ≃ₗ[ℚ] N) (x : M) :
    transportAction e (1 : N ≃ₗ[ℚ] N) x = x := by
  rw [transportAction_apply]
  change e.symm (e x) = x
  exact e.symm_apply_apply x

/-- Pointwise multiplicativity of a raw action transports across e.  The
hypothesis is exactly the source action law, so no convention on the
multiplication of linear equivalences is assumed. -/
theorem transportAction_mul {M N : Type u} [AddCommMonoid M] [Module ℚ M]
    [AddCommMonoid N] [Module ℚ N] (e : M ≃ₗ[ℚ] N) (a b : N ≃ₗ[ℚ] N)
    (h : ∀ y : N, (a * b) y = a (b y)) (x : M) :
    transportAction e (a * b) x =
      transportAction e a (transportAction e b x) := by
  rw [transportAction_apply, transportAction_apply, transportAction_apply]
  rw [h (e x), e.apply_symm_apply]

/-- Transport the identity law of a raw action, stated directly for the source
action family so that no multiplication convention is used. -/
theorem transportAction_one_of_action {M N G : Type u} [AddCommMonoid M]
    [Module ℚ M] [AddCommMonoid N] [Module ℚ N] [One G]
    (e : M ≃ₗ[ℚ] N) (action : G → N ≃ₗ[ℚ] N)
    (h : ∀ y : N, action 1 y = y) (x : M) :
    transportAction e (action 1) x = x := by
  rw [transportAction_apply, h, e.symm_apply_apply]

/-- Transport the multiplication law of a raw action, stated directly for the
source action family so that no multiplication convention is used. -/
theorem transportAction_mul_of_action {M N G : Type u} [AddCommMonoid M]
    [Module ℚ M] [AddCommMonoid N] [Module ℚ N] [Mul G]
    (e : M ≃ₗ[ℚ] N) (action : G → N ≃ₗ[ℚ] N)
    (h : ∀ (a b : G) (y : N), action (a * b) y = action a (action b y))
    (a b : G) (x : M) :
    transportAction e (action (a * b)) x =
      transportAction e (action a) (transportAction e (action b) x) := by
  rw [transportAction_apply, transportAction_apply, transportAction_apply]
  rw [h a b (e x), e.apply_symm_apply]

/-! ## 3. The actual nonarchimedean per-summand symmetry -/

/-- The source-faithful nonarchimedean Ind2 symmetry on one summand.  The group
is literally TimesMuKummer.Ism local.rho for an actual source F-prime-strip. -/
structure NonarchimedeanActualInd2Symmetry (V : Type v) (M : Type u)
    [AddCommMonoid M] [Module ℚ M] where
  kummer : ActualLocalKummerDatum.{u, v} V
  action : kummer.Ism → M ≃ₗ[ℚ] M
  action_one : ∀ value, action 1 value = value
  action_mul : ∀ first second value,
    action (first * second) value = action first (action second value)

namespace NonarchimedeanActualInd2Symmetry

variable {V : Type v} {M : Type u} [AddCommMonoid M] [Module ℚ M]

/-- The S1324 nonarchimedean summand symmetry, with its group pinned to the
actual local Kummer datum. -/
def toS1324 (D : NonarchimedeanActualInd2Symmetry V M) :
    NonarchimedeanInd2SummandSymmetry M where
  G := D.kummer.G
  groupG := inferInstance
  topologicalSpaceG := D.kummer.topologicalSpaceG
  U := D.kummer.U
  commGroupU := D.kummer.commGroupU
  rho := D.kummer.rho
  action := D.action
  action_one := D.action_one
  action_mul := D.action_mul

/-- The group type of the produced S1324 symmetry is definitionally the actual
local Ism subgroup. -/
@[simp] theorem toS1324_groupType (D : NonarchimedeanActualInd2Symmetry V M) :
    (SourceInd2SummandSymmetry.nonarchimedean D.toS1324).GroupType =
      D.kummer.Ism := rfl

/-- The action is exactly the actual analytic-shell representation. -/
@[simp] theorem toS1324_action (D : NonarchimedeanActualInd2Symmetry V M) :
    D.toS1324.action = D.action := rfl

/-- Transport the actual symmetry across a Q-linear equivalence of the
carrier.  The local Kummer datum and the acting group are untouched. -/
noncomputable def transport (D : NonarchimedeanActualInd2Symmetry V M)
    {N : Type u} [AddCommMonoid N] [Module ℚ N] (e : M ≃ₗ[ℚ] N) :
    NonarchimedeanActualInd2Symmetry V N where
  kummer := D.kummer
  action g := transportAction e.symm (D.action g)
  action_one value :=
    transportAction_one_of_action e.symm D.action D.action_one value
  action_mul first second value :=
    transportAction_mul_of_action e.symm D.action D.action_mul
      first second value

end NonarchimedeanActualInd2Symmetry

/-! ## 4. The actual archimedean per-summand symmetry -/

/-- The source-faithful archimedean Ind2 symmetry on one summand: the actual
independent sign group, one order-two factor per direct summand. -/
structure ArchimedeanActualInd2Symmetry (M : Type u)
    [AddCommMonoid M] [Module ℚ M] where
  factorIndex : Type u
  [fintypeFactorIndex : Fintype factorIndex]
  action : (factorIndex → Multiplicative (ZMod 2)) → M ≃ₗ[ℚ] M
  action_one : ∀ value, action 1 value = value
  action_mul : ∀ first second value,
    action (first * second) value = action first (action second value)

attribute [instance] ArchimedeanActualInd2Symmetry.fintypeFactorIndex

namespace ArchimedeanActualInd2Symmetry

variable {M : Type u} [AddCommMonoid M] [Module ℚ M]

/-- The S1324 archimedean summand symmetry, with the actual sign group. -/
def toS1324 (D : ArchimedeanActualInd2Symmetry M) :
    ArchimedeanInd2SummandSymmetry M where
  factorIndex := D.factorIndex
  fintypeFactorIndex := D.fintypeFactorIndex
  action := D.action
  action_one := D.action_one
  action_mul := D.action_mul

@[simp] theorem toS1324_groupType (D : ArchimedeanActualInd2Symmetry M) :
    (SourceInd2SummandSymmetry.archimedean D.toS1324).GroupType =
      (D.factorIndex → Multiplicative (ZMod 2)) := rfl

@[simp] theorem toS1324_action (D : ArchimedeanActualInd2Symmetry M) :
    D.toS1324.action = D.action := rfl

/-- Transport the actual archimedean symmetry across a Q-linear equivalence of
the analytic-shell carrier. -/
noncomputable def transport (D : ArchimedeanActualInd2Symmetry M)
    {N : Type u} [AddCommMonoid N] [Module ℚ N] (e : M ≃ₗ[ℚ] N) :
    ArchimedeanActualInd2Symmetry N where
  factorIndex := D.factorIndex
  fintypeFactorIndex := D.fintypeFactorIndex
  action g := transportAction e.symm (D.action g)
  action_one value :=
    transportAction_one_of_action e.symm D.action D.action_one value
  action_mul first second value :=
    transportAction_mul_of_action e.symm D.action D.action_mul
      first second value

end ArchimedeanActualInd2Symmetry

/-! ## 5. The exact first field of the actual assembly -/

variable {l : PrimeGeFive} {V : Type v}
variable {I : OriginalInput.{u, v, u, u, u} l V}

/-- The exact nonarchimedean first field: for every capsule label and every
place over v_Q, an actual local Kummer datum together with its representation on
the actual log-shell carrier. -/
abbrev NonarchimedeanActualField
    (C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) (Vk : Type v) :=
  (i : Capsule j.val) → (v : C.place vQ) →
    NonarchimedeanActualInd2Symmetry Vk ((C.logShell j).Shell i vQ v)

/-- The exact archimedean first field. -/
abbrev ArchimedeanActualField
    (C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :=
  (i : Capsule j.val) → (v : C.place vQ) →
    ArchimedeanActualInd2Symmetry ((C.logShell j).Shell i vQ v)

namespace NonarchimedeanActualField

variable {C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I}
variable {j : Fin (capsuleLevels l)} {vQ : C.VQ} {Vk : Type v}

/-- The exact first field produces the S1324 nonarchimedean first field. -/
def toS1324 (F : NonarchimedeanActualField C j vQ Vk) :
    SourceFaithfulInd2SummandSymmetryField .nonarchimedean C j vQ :=
  fun i v => .nonarchimedean ((F i v).toS1324)

theorem toS1324_groupType (F : NonarchimedeanActualField C j vQ Vk)
    (i : Capsule j.val) (v : C.place vQ) :
    (SourceInd2SummandSymmetry.nonarchimedean ((F i v).toS1324)).GroupType =
      (F i v).kummer.Ism := rfl

theorem toS1324_action (F : NonarchimedeanActualField C j vQ Vk)
    (i : Capsule j.val) (v : C.place vQ) :
    ((F i v).toS1324).action = (F i v).action := rfl

end NonarchimedeanActualField

namespace ArchimedeanActualField

variable {C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I}
variable {j : Fin (capsuleLevels l)} {vQ : C.VQ}

/-- The exact first field produces the S1324 archimedean first field. -/
def toS1324 (F : ArchimedeanActualField C j vQ) :
    SourceFaithfulInd2SummandSymmetryField .archimedean C j vQ :=
  fun i v => .archimedean ((F i v).toS1324)

theorem toS1324_groupType (F : ArchimedeanActualField C j vQ)
    (i : Capsule j.val) (v : C.place vQ) :
    (SourceInd2SummandSymmetry.archimedean ((F i v).toS1324)).GroupType =
      ((F i v).factorIndex → Multiplicative (ZMod 2)) := rfl

theorem toS1324_action (F : ArchimedeanActualField C j vQ)
    (i : Capsule j.val) (v : C.place vQ) :
    ((F i v).toS1324).action = (F i v).action := rfl

end ArchimedeanActualField

/-! ## 6. The exact per-summand analytic-shell datum on IQSpan -/

/-- The exact nonarchimedean analytic-shell datum at one summand: the actual
local Kummer datum, the actual local log-shell datum, the Q-linear
identification of the capsule shell with the actual IQSpan, and the
representation of the actual Ism on that IQSpan. -/
structure NonarchimedeanAnalyticShellDatum (Vk : Type v) (M : Type u)
    [AddCommMonoid M] [Module ℚ M] where
  kummer : ActualLocalKummerDatum.{u, v} Vk
  shell : SourceLogShellDatum.{u}
  shellEquiv : M ≃ₗ[ℚ] shell.IQSpan
  action : kummer.Ism → shell.IQSpan ≃ₗ[ℚ] shell.IQSpan
  action_one : ∀ value, action 1 value = value
  action_mul : ∀ first second value,
    action (first * second) value = action first (action second value)

namespace NonarchimedeanAnalyticShellDatum

variable {Vk : Type v} {M : Type u} [AddCommMonoid M] [Module ℚ M]

/-- The actual action on the IQSpan, as a summand symmetry on the local
log-shell Q-span. -/
def toIQSpanActual (D : NonarchimedeanAnalyticShellDatum Vk M) :
    NonarchimedeanActualInd2Symmetry Vk D.shell.IQSpan where
  kummer := D.kummer
  action := D.action
  action_one := D.action_one
  action_mul := D.action_mul

/-- The actual symmetry on the capsule carrier, transported from the IQSpan
along the explicit shell identification. -/
noncomputable def toActual (D : NonarchimedeanAnalyticShellDatum Vk M) :
    NonarchimedeanActualInd2Symmetry Vk M :=
  (D.toIQSpanActual).transport D.shellEquiv.symm

/-- The group is the actual local Ism. -/
@[simp] theorem toActual_groupType (D : NonarchimedeanAnalyticShellDatum Vk M) :
    D.toActual.kummer.Ism = D.kummer.Ism := rfl

/-- The actual carrier is the capsule shell, and the action is transported
from the actual IQSpan representation. -/
theorem toActual_action_apply (D : NonarchimedeanAnalyticShellDatum Vk M)
    (g : D.kummer.Ism) (x : M) :
    D.toActual.action g x =
      D.shellEquiv.symm (D.action g (D.shellEquiv x)) := by
  change transportAction D.shellEquiv (D.action g) x = _
  rw [transportAction_apply]

end NonarchimedeanAnalyticShellDatum

/-- The exact nonarchimedean first field stated in terms of the actual local
log-shell datum and its IQSpan. -/
abbrev NonarchimedeanAnalyticShellField
    (C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) (Vk : Type v) :=
  (i : Capsule j.val) → (v : C.place vQ) →
    NonarchimedeanAnalyticShellDatum Vk ((C.logShell j).Shell i vQ v)

namespace NonarchimedeanAnalyticShellField

variable {C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I}
variable {j : Fin (capsuleLevels l)} {vQ : C.VQ} {Vk : Type v}

/-- The exact analytic-shell datum produces the exact first field. -/
noncomputable def toActualField (F : NonarchimedeanAnalyticShellField C j vQ Vk) :
    NonarchimedeanActualField C j vQ Vk :=
  fun i v => (F i v).toActual

/-- The exact analytic-shell datum literally produces the S1324 first field. -/
noncomputable def toS1324 (F : NonarchimedeanAnalyticShellField C j vQ Vk) :
    SourceFaithfulInd2SummandSymmetryField .nonarchimedean C j vQ :=
  (F.toActualField).toS1324

/-- At each summand the produced symmetry's group is the actual local Ism. -/
theorem toS1324_groupType (F : NonarchimedeanAnalyticShellField C j vQ Vk)
    (i : Capsule j.val) (v : C.place vQ) :
    (((F.toS1324 i v)).GroupType) = (F i v).kummer.Ism := rfl

end NonarchimedeanAnalyticShellField

/-- The exact archimedean analytic-shell datum: a finite factor index and a
Q-linear identification of the capsule shell with the actual archimedean
conjugation model factorIndex -> Complex. -/
structure ArchimedeanAnalyticShellDatum (M : Type u)
    [AddCommMonoid M] [Module ℚ M] where
  factorIndex : Type u
  [fintypeFactorIndex : Fintype factorIndex]
  shellEquiv : M ≃ₗ[ℚ] (factorIndex → ℂ)

attribute [instance] ArchimedeanAnalyticShellDatum.fintypeFactorIndex

namespace ArchimedeanAnalyticShellDatum

variable {M : Type u} [AddCommMonoid M] [Module ℚ M]
variable (D : ArchimedeanAnalyticShellDatum M)

end ArchimedeanAnalyticShellDatum

/-- The exact archimedean first field. -/
abbrev ArchimedeanAnalyticShellField
    (C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :=
  (i : Capsule j.val) → (v : C.place vQ) →
    ArchimedeanAnalyticShellDatum ((C.logShell j).Shell i vQ v)

/-! ## 7. The actual regular representation of the local Kummer Ism -/

/-- The regular analytic shell of an actual local Kummer datum: the group
algebra of the actual times-mu quotient. -/
abbrev KummerRegularShell {V : Type v} (L : ActualLocalKummerDatum.{u, v} V) :
    Type u := by
  letI := L.commGroupU
  exact MonoidAlgebra ℚ (TimesMuQuotient L.U)

/-- The actual regular representation of the local Kummer Ism on the group
algebra of the times-mu quotient. -/
noncomputable def regularAction {V : Type v} (L : ActualLocalKummerDatum.{u, v} V)
    (g : L.Ism) : KummerRegularShell L ≃ₗ[ℚ] KummerRegularShell L := by
  letI := L.commGroupU
  letI := L.topologicalSpaceG
  exact Models.regularIsmAction L.rho g

theorem regularAction_one {V : Type v} (L : ActualLocalKummerDatum.{u, v} V)
    (value : KummerRegularShell L) :
    regularAction L 1 value = value := by
  letI := L.commGroupU
  letI := L.topologicalSpaceG
  exact Models.regularIsmAction_one L.rho value

theorem regularAction_mul {V : Type v} (L : ActualLocalKummerDatum.{u, v} V)
    (first second : L.Ism) (value : KummerRegularShell L) :
    regularAction L (first * second) value =
      regularAction L first (regularAction L second value) := by
  letI := L.commGroupU
  letI := L.topologicalSpaceG
  exact Models.regularIsmAction_mul L.rho first second value

/-- The actual nonarchimedean regular-model symmetry. -/
noncomputable def regularActual {V : Type v} (L : ActualLocalKummerDatum.{u, v} V) :
    NonarchimedeanActualInd2Symmetry V (KummerRegularShell L) where
  kummer := L
  action := regularAction L
  action_one := regularAction_one L
  action_mul := regularAction_mul L

theorem regularActual_nonempty {V : Type v} (L : ActualLocalKummerDatum.{u, v} V) :
    Nonempty (NonarchimedeanActualInd2Symmetry V (KummerRegularShell L)) :=
  ⟨regularActual L⟩

/-- The regular model on an arbitrary capsule shell, given the explicit
Q-linear identification of that shell with the regular representation. -/
noncomputable def regularActualOfEquiv {V : Type v} (L : ActualLocalKummerDatum.{u, v} V)
    {M : Type u} [AddCommMonoid M] [Module ℚ M]
    (e : M ≃ₗ[ℚ] KummerRegularShell L) :
    NonarchimedeanActualInd2Symmetry V M :=
  (regularActual L).transport e.symm

/-! ## 8. The actual archimedean conjugation model -/

/-- Complex conjugation as a Q-linear equivalence of the actual archimedean
local field Complex. -/
noncomputable def complexConjLinear : ℂ ≃ₗ[ℚ] ℂ where
  toFun z := star z
  invFun z := star z
  left_inv z := by simp
  right_inv z := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem complexConjLinear_apply (z : ℂ) : complexConjLinear z = star z := rfl

theorem complexConjLinear_trans_self :
    complexConjLinear.trans complexConjLinear = LinearEquiv.refl ℚ ℂ := by
  ext z
  simp [complexConjLinear]

/-- The order-two sign action on Complex. -/
noncomputable def archSignEquiv (s : Multiplicative (ZMod 2)) : ℂ ≃ₗ[ℚ] ℂ :=
  if s = 1 then LinearEquiv.refl ℚ ℂ else complexConjLinear

@[simp] theorem archSignEquiv_one : archSignEquiv 1 = LinearEquiv.refl ℚ ℂ := by
  simp [archSignEquiv]

theorem archSignEquiv_mul (s t : Multiplicative (ZMod 2)) :
    archSignEquiv (s * t) = (archSignEquiv t).trans (archSignEquiv s) := by
  rcases Models.mul_zmod2_eq_one_or_sign s with rfl | rfl <;>
    rcases Models.mul_zmod2_eq_one_or_sign t with rfl | rfl <;>
    simp [archSignEquiv, Models.zmod2Sign_mul_self, complexConjLinear_trans_self]

/-- The actual independent sign action on a finite product of archimedean local
fields. -/
noncomputable def archimedeanConjAction (ι : Type u) [Fintype ι] :
    (ι → Multiplicative (ZMod 2)) → (ι → ℂ) ≃ₗ[ℚ] (ι → ℂ) :=
  fun σ => LinearEquiv.piCongrRight (fun i => archSignEquiv (σ i))

theorem archimedeanConjAction_one (ι : Type u) [Fintype ι]
    (value : ι → ℂ) :
    archimedeanConjAction ι 1 value = value := by
  ext i
  simp [archimedeanConjAction]

theorem archimedeanConjAction_mul (ι : Type u) [Fintype ι]
    (first second : ι → Multiplicative (ZMod 2)) (value : ι → ℂ) :
    archimedeanConjAction ι (first * second) value =
      archimedeanConjAction ι first (archimedeanConjAction ι second value) := by
  ext i
  simp [archimedeanConjAction, Pi.mul_apply, archSignEquiv_mul]

/-- The actual archimedean symmetry on a finite product of copies of Complex. -/
noncomputable def archimedeanComplexActual (ι : Type u) [Fintype ι] :
    ArchimedeanActualInd2Symmetry (ι → ℂ) where
  factorIndex := ι
  fintypeFactorIndex := inferInstance
  action := archimedeanConjAction ι
  action_one := archimedeanConjAction_one ι
  action_mul := archimedeanConjAction_mul ι

theorem archimedeanComplexActual_nonempty (ι : Type u) [Fintype ι] :
    Nonempty (ArchimedeanActualInd2Symmetry (ι → ℂ)) :=
  ⟨archimedeanComplexActual ι⟩

/-- The actual archimedean symmetry on an arbitrary capsule shell, given the
explicit Q-linear identification with the finite product of archimedean local
fields. -/
noncomputable def archimedeanComplexActualOfEquiv (ι : Type u) [Fintype ι]
    {M : Type u} [AddCommMonoid M] [Module ℚ M]
    (e : M ≃ₗ[ℚ] (ι → ℂ)) :
    ArchimedeanActualInd2Symmetry M :=
  (archimedeanComplexActual ι).transport e.symm

/-- The exact archimedean analytic-shell datum produces the actual
archimedean symmetry on the capsule carrier. -/
noncomputable def ArchimedeanAnalyticShellDatum.toActual
    {M : Type u} [AddCommMonoid M] [Module ℚ M]
    (D : ArchimedeanAnalyticShellDatum M) :
    ArchimedeanActualInd2Symmetry M := by
  letI := D.fintypeFactorIndex
  exact archimedeanComplexActualOfEquiv D.factorIndex D.shellEquiv

namespace ArchimedeanAnalyticShellField

variable {C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I}
variable {j : Fin (capsuleLevels l)} {vQ : C.VQ}

/-- The exact archimedean field produces the exact first field. -/
noncomputable def toActualField (F : ArchimedeanAnalyticShellField C j vQ) :
    ArchimedeanActualField C j vQ :=
  fun i v => (F i v).toActual

/-- The exact archimedean field literally produces the S1324 first field. -/
noncomputable def toS1324 (F : ArchimedeanAnalyticShellField C j vQ) :
    SourceFaithfulInd2SummandSymmetryField .archimedean C j vQ :=
  (F.toActualField).toS1324

/-- At each summand the group is the actual independent sign group. -/
theorem toS1324_groupType (F : ArchimedeanAnalyticShellField C j vQ)
    (i : Capsule j.val) (v : C.place vQ) :
    (((F.toS1324 i v)).GroupType) =
      ((F i v).factorIndex → Multiplicative (ZMod 2)) := rfl

end ArchimedeanAnalyticShellField

/-! ## 9. Non-vacuity of the exact first fields -/

theorem nonarchimedeanAnalyticShellField_nonempty
    {C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I}
    {j : Fin (capsuleLevels l)} {vQ : C.VQ} {Vk : Type v}
    (F : NonarchimedeanAnalyticShellField C j vQ Vk) :
    Nonempty (SourceFaithfulInd2SummandSymmetryField .nonarchimedean C j vQ) :=
  ⟨F.toS1324⟩

theorem archimedeanAnalyticShellField_nonempty
    {C : SourceProcessionCapsuleContract.{u, v, u, u, u, 0, 0, u, u} ℚ l V I}
    {j : Fin (capsuleLevels l)} {vQ : C.VQ}
    (F : ArchimedeanAnalyticShellField C j vQ) :
    Nonempty (SourceFaithfulInd2SummandSymmetryField .archimedean C j vQ) :=
  ⟨F.toS1324⟩

theorem regularModel_nonempty {Vk : Type v} (L : ActualLocalKummerDatum.{u, v} Vk) :
    Nonempty (NonarchimedeanActualInd2Symmetry Vk (KummerRegularShell L)) :=
  regularActual_nonempty L

theorem archimedeanModel_nonempty (ι : Type u) [Fintype ι] :
    Nonempty (ArchimedeanActualInd2Symmetry (ι → ℂ)) :=
  archimedeanComplexActual_nonempty ι

/-! ## 10. Axiom probes -/

#print axioms ActualLocalKummerDatum
#print axioms ActualLocalKummerDatum.localKummerDatumAtPrime
#print axioms transportAction
#print axioms transportAction_one
#print axioms transportAction_mul
#print axioms NonarchimedeanActualInd2Symmetry.toS1324
#print axioms NonarchimedeanActualInd2Symmetry.toS1324_groupType
#print axioms NonarchimedeanActualInd2Symmetry.transport
#print axioms ArchimedeanActualInd2Symmetry.toS1324
#print axioms ArchimedeanActualInd2Symmetry.toS1324_groupType
#print axioms ArchimedeanActualInd2Symmetry.transport
#print axioms NonarchimedeanAnalyticShellDatum.toActual
#print axioms NonarchimedeanAnalyticShellField.toS1324
#print axioms regularActual
#print axioms regularActual_nonempty
#print axioms complexConjLinear
#print axioms archSignEquiv
#print axioms archSignEquiv_mul
#print axioms archimedeanComplexActual
#print axioms archimedeanComplexActual_nonempty
#print axioms archimedeanAnalyticShellField_nonempty

end LeanFormal.IUT.XiFPaper.S1426Ind2AnalyticSymmetryActual

end
