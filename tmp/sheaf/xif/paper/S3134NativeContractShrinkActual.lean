import tmp.sheaf.xif.paper.S3134SameCBridgeActual

/-!
# S3134 task-16: shrinking the native-to-contract missing data field by field

Continuation of `S3134SameCBridgeActual` (task-12).  The same-C bridge
`SourceNativeInitialThetaData l` -> `OriginalInput` was recorded with four data
slots.  This file constructs three of them from actual native data and leaves
exactly one as an exact smaller Missing:

(1) `badFinite` — the finiteness of `V^bad_mod`.  The native bad-place type
    `S3134NativeBadPlaces T = {p : FinitePlace Fmod // p in V^bad_mod}` is
    definitionally the mainline same-C input's bad-place type
    `Bad (nativePlaceSelection T)` (IUT I, Definition 3.1(b), corpus
    `I-T.txt:3141-3147`).  Hence the source input's own finiteness datum
    `[Fintype (Bad (nativePlaceSelection T))]` (the fixed input C of the qVFamily
    / S3131QC side) is exactly the required Fintype.  Constructed:
    `S3134NativeBadFinite`.  (Without that same-C input datum, this finite
    support is the source obligation of clause (b); then it stays a Missing
    hypothesis, not a consequence of the native record.)

(2) `stableReduction` + `∀`-proof — constructed from the actual native
    reduction data: IUT I, Definition 3.1(b), `I-T.txt:3131-3133` states that
    `X_F` admits stable reduction over all nonarchimedean `v in V(F)`;
    in the tree this is `T.clauseA.stable_reduction_nonarchimedean`
    (`SourceClauseA`, `SourceDefinition31Quantifiers.lean:891`).
    Constructed: `S3134NativeStableReduction` + its universal proof.

(3) `torsionImage` + proof — constructed from the actual l-torsion
    representation data: IUT I, Definition 3.1(c), `I-T.txt:3176-3184` states
    that the image of `G_F -> GL_2(F_l)` contains `SL_2(F_l)`; in the tree
    this is `T.clauseC.image_contains_SL2`
    (`SourceClauseC`, `SourceDefinition31Quantifiers.lean:1023-1026`).
    Constructed: `S3134NativeTorsionImage` + its proof.

(4) `cuspParameter : Real` + positivity — NOT constructed: IUT I,
    Definition 3.1, tuple entry and clause (f) (`I-T.txt:3123-3126`,
    `:3273-3282`) describe `epsilon` as the *geometric cusp* of `C_K`.  The
    native record carries exactly that geometric object
    (`SourceSignQuotientData.epsilon : Iut.OrbicurveBoundaryCusp cK`,
    `SourceDefinition31Quantifiers.lean:631`), which has no real-valued cusp
    parameter; the abstract contract's `cusp.epsilon : Real` is a numerical
    encoding of the same cusp.  Exact smaller Missing:
    `S3134NativeCuspParameterMissing` (real + positivity), with the geometric
    cusp `T.tuple.source.epsilon` as the fixed source object.

Result: the reduced Missing `S3134NativeContractMissingReduced` has exactly one
data field (the real cusp parameter) instead of four; the bridge with the
reduced Missing implies the task-12 bridge, and the 3.11.5 => 3.12 mainline
consumer is re-exported with the reduced Missing.  No sorry/axiom/arbitrary
carrier/toy; no renaming of missing into progress.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134SameCBridgeActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual

namespace LeanFormal.IUT.XiFPaper.S3134NativeContractShrinkActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## (1) badFinite: from the same-C input's finite bad support -/

/-- The native bad-place type is definitionally mainline's same-C bad-place
type `Bad (nativePlaceSelection T)`; the fixed input's finiteness datum is
therefore exactly the required Fintype (IUT I, Def. 3.1(b), `I-T.txt:3141-3147`
for the finite bad support; the record itself is the source input C). -/
theorem S3134NativeBadPlaces_eq_bad :
    S3134NativeBadPlaces T = Bad (nativePlaceSelection T) := rfl

/-- Constructed slot (1): the finite bad support of the native datum, as
supplied by the same-C source input. -/
noncomputable def S3134NativeBadFinite : Fintype (S3134NativeBadPlaces T) :=
  show Fintype (Bad (nativePlaceSelection T)) from inferInstance

/-! ## (2) stableReduction: from the actual native reduction data -/

/-- Constructed slot (2): the native stable-reduction predicate on bad places.
A bad place `b` satisfies it when every place of `F` above `b` has stable
reduction; the clause (b) data is `T.clauseA.stable_reduction_nonarchimedean`. -/
def S3134NativeStableReduction : S3134NativeBadPlaces T → Prop :=
  fun b => ∀ p : NumberField.FinitePlace T.arithmetic.F,
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) p = b.1 →
      T.arithmetic.curve.HasStableReductionAt p

/-- Constructed slot (2), proof: IUT I Def. 3.1(b) (`I-T.txt:3131-3133`). -/
theorem S3134NativeStableReduction_proved
    (b : S3134NativeBadPlaces T) :
    S3134NativeStableReduction T b :=
  fun p _hp => (T.clauseA).stable_reduction_nonarchimedean p

/-! ## (3) torsionImage: from the actual l-torsion representation data -/

/-- Constructed slot (3): the paper's l-torsion SL_2 image proposition
(IUT I, Def. 3.1(c), `I-T.txt:3176-3184`). -/
def S3134NativeTorsionImage : Prop :=
  Subgroup.map Matrix.SpecialLinearGroup.toGL
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
    (T.clauseC).representation.range

/-- Constructed slot (3), proof: the clause (c) containment
`SourceClauseC.image_contains_SL2`. -/
theorem S3134NativeTorsionImage_proved :
    S3134NativeTorsionImage (l := l) T :=
  (T.clauseC).image_contains_SL2

/-! ## (4) cuspParameter: exact smaller Missing -/

/-- Exact smaller Missing of task-16: the only data field of
`S3134NativeContractMissing` that the native record does not determine.  IUT I,
Definition 3.1 tuple entry `epsilon` (`I-T.txt:3123-3126`) and clause (f)
(`:3273-3282`) present `epsilon` as the geometric cusp of `C_K`, which the
native record carries as `T.tuple.source.epsilon : OrbicurveBoundaryCusp cK`;
the contract's `cusp.epsilon : Real` is a numerical encoding of that same cusp,
so the real cusp parameter and its positivity remain an exact source Missing. -/
structure S3134NativeCuspParameterMissing
    (T : SourceNativeInitialThetaData.{0} l) where
  cuspParameter : ℝ
  cusp_positive : 0 < cuspParameter

/-- The geometric cusp of the native datum (paper `epsilon`, Def. 3.1(f)). -/
def S3134NativeGeometricCusp :
    Iut.OrbicurveBoundaryCusp T.tuple.source.cK :=
  T.tuple.source.epsilon

/-- The reduced Missing: only the real cusp parameter remains. -/
abbrev S3134NativeContractMissingReduced
    (T : SourceNativeInitialThetaData.{0} l) : Type :=
  S3134NativeCuspParameterMissing T

/-! ## Construction and bridge with the reduced Missing -/

/-- Construction of `InitialThetaInput` from the native datum plus the reduced
(single-field) Missing data; slots (1)--(3) are the constructed fields above. -/
noncomputable def S3134NativeInitialThetaInputReduced
    (M : S3134NativeContractMissingReduced T) : InitialThetaInput.{0} l where
  arithmetic := T.arithmetic
  selectedPlaces := S3134NativeSelectedPlaces T
  badPlaces := S3134NativeBadPlaces T
  badIncluded := S3134NativeBadIncluded T
  selectedNonempty := S3134NativeSelectedNonempty T
  badFinite := S3134NativeBadFinite T
  stableReduction := S3134NativeStableReduction T
  stableReduction_proved := S3134NativeStableReduction_proved T
  torsionImage := S3134NativeTorsionImage (l := l) T
  torsionImage_proved := S3134NativeTorsionImage_proved (l := l) T
  cuspParameter := M.cuspParameter
  cusp_positive := M.cusp_positive

/-- Reduced same-C bridge: the canonical native input built with only the cusp
Missing equals the contract input of `J`. -/
def S3134SameCContractBridgeReduced : Prop :=
  ∃ M : S3134NativeContractMissingReduced T,
    S3134NativeInitialThetaInputReduced T M = J.initialThetaInput

/-- Reduced bridge implies the task-12 bridge (fill the constructed slots). -/
theorem S3134SameCContractBridge_ofReduced
    (H : S3134SameCContractBridgeReduced (J := J) (T := T)) :
    S3134SameCContractBridge (J := J) (T := T) := by
  obtain ⟨M, hM⟩ := H
  refine ⟨{ badFinite := S3134NativeBadFinite T
            stableReduction := S3134NativeStableReduction T
            stableReduction_proved := S3134NativeStableReduction_proved T
            torsionImage := S3134NativeTorsionImage (l := l) (T := T)
            torsionImage_proved := S3134NativeTorsionImage_proved (l := l) T
            cuspParameter := M.cuspParameter
            cusp_positive := M.cusp_positive }, ?_⟩
  rw [← hM]
  rfl

/-- Field-level status of the shrink: under the reduced bridge the three
constructed slots are identified with the contract's data, and only the cusp
parameter remains a data identification. -/
theorem S3134NativeContractShrink_status
    (M : S3134NativeContractMissingReduced T)
    (hM : S3134NativeInitialThetaInputReduced T M = J.initialThetaInput) :
    HEq (S3134NativeBadFinite T) J.initialThetaInput.badFinite ∧
      HEq (S3134NativeStableReduction T) J.initialThetaInput.stableReduction ∧
      S3134NativeTorsionImage (l := l) T =
        J.initialThetaInput.torsionImage ∧
      M.cuspParameter = J.initialThetaInput.cuspParameter := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hM]; exact HEq.refl _
  · rw [← hM]; exact HEq.refl _
  · rw [← hM]; rfl
  · rw [← hM]; rfl

/-! ## Re-export of the 3.11.5 => 3.12 mainline consumer with reduced Missing -/

/-- Same-C readout identification with the reduced bridge (three slots closed). -/
structure S3134SameCReadoutIdentificationReduced : Prop where
  bridge : S3134SameCContractBridgeReduced (J := J) (T := T)
  qc : S3134MainlineQCSameC (J := J) (T := T)

/-- The reduced bridge part. -/
theorem S3134SameCReadoutIdentificationReduced_bridge
    (H : S3134SameCReadoutIdentificationReduced (J := J) (T := T)) :
    S3134SameCContractBridgeReduced (J := J) (T := T) :=
  H.bridge

/-- The q-readout part. -/
theorem S3134SameCReadoutIdentificationReduced_qc
    (H : S3134SameCReadoutIdentificationReduced (J := J) (T := T)) :
    S3134MainlineQCSameC (J := J) (T := T) :=
  H.qc

/-- Mainline consumer with the reduced Missing (single data field): the
mainline actual q-side readout `S3131QC T` is bounded by the assembled
Theta-pilot readout of the 3.11.5 => 3.12 comparison. -/
theorem S3134Step3115_mainlineQC_le_thetaPilot_viaSameCReduced
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    (H : S3134SameCReadoutIdentificationReduced (J := J) (T := T)) :
    S3131QC T ≤ S3134Step3115ThetaPilotReadout (I := I) D :=
  S3134Step3115_mainlineQC_le_thetaPilot (I := I) (J := J) (T := T) D G
    (S3134SameCReadoutIdentificationReduced_qc (J := J) (T := T) H)

#check S3134NativeBadPlaces_eq_bad
#check S3134NativeBadFinite
#check S3134NativeStableReduction
#check S3134NativeStableReduction_proved
#check S3134NativeTorsionImage
#check S3134NativeTorsionImage_proved
#check S3134NativeCuspParameterMissing
#check S3134NativeGeometricCusp
#check S3134NativeContractMissingReduced
#check S3134NativeInitialThetaInputReduced
#check S3134SameCContractBridgeReduced
#check S3134SameCContractBridge_ofReduced
#check S3134NativeContractShrink_status
#check S3134Step3115_mainlineQC_le_thetaPilot_viaSameCReduced

end LeanFormal.IUT.XiFPaper.S3134NativeContractShrinkActual
