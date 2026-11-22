import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import tmp.sheaf.xif.paper.S3134Step3115To312Actual

/-!
# S3134: the same-C bridge between native Theta data and the OriginalInput contract

IUT I, Definition 3.1 (corpus `Inter-universal Teichmuller Theory I.txt:3122`)
presents the initial Theta-data as the tuple `(Fbar/F, X_F, l, C_K, V,
V^bad_mod, epsilon)` subject to clauses (a)--(f).  IUT III, Corollary 3.12
(`:10325-10360`) and its Step (xi) work over ONE qualified input `C`.  The
tree has two different carriers for that same definition:

* `SourceNativeInitialThetaData l` (`SourceDefinition31Quantifiers.lean:1681`):
  arithmetic data plus the actual foundation objects and the six source
  clauses (the qVFamily / mainline Batch A side).
* `SourceDefinition31Data l` (`SourceDefinition31Boundary.lean:667`), the
  abstract contract, whose `toInitialThetaInput` projection
  (`SourceDefinition31Boundary.lean:831`) is the `OriginalInput` side
  (`SourceOriginalInput.lean:42`, `initialThetaInput` at `:1297`).

This file does the field-by-field analysis required for the same-C bridge
`S3134MainlineQCSameC`:

1. it constructs the *canonical* native fragment that Definition 3.1 determines:
   the selected places `{v : NumberFieldPlace K // v in V}`, the bad places
   `{p : FinitePlace Fmod // p in V^bad_mod}`, their inclusion through the
   native place bijection `V_mod_bijection`, and the nonemptiness of the
   selected places (all proved);
2. it records the exact missing data that Definition 3.1 leaves to the
   contract but that the native record does not determine:
   * `badFinite`: finiteness of the bad support (IUT I Def. 3.1, clause (b);
     the native carrier has `V^bad_mod` only as a set);
   * `stableReduction` with its universal proof (clause (b)/(c) contract
     predicate; the native clauses carry no such predicate on this carrier);
   * `torsionImage` with its proof (the contract uses
     `torsion.imageContainsSL2`; the native side carries the clause objects,
     not this proposition);
   * `cuspParameter` with positivity (the contract's `cusp.epsilon : Real`;
     the native side carries the geometric cusp `epsilon :
     Iut.OrbicurveBoundaryCusp cK`, which is not a real number);
3. it builds `S3134NativeInitialThetaInput` from a native datum plus exactly
   that missing data, and states the same-C bridge `S3134SameCContractBridge`
   as the existence of missing data making this input equal to
   `J.initialThetaInput`;
4. it proves the field-level consequences of the bridge (arithmetic root,
   both place types, bad inclusion, bad finiteness, stable reduction,
   torsion image, cusp parameter), so the bridge is a genuine field-by-field
   identification, not an opaque equivalence;
5. it wires the 3.11.5 => 3.12 comparison of `S3134Step3115To312Actual` to the
   mainline readout `S3131QC` through the named same-C readout structure
   `S3134SameCReadoutIdentification` (bridge + q-readout identification).

Status: the bridge itself is NOT derivable from the tree — this matches the
independent analysis of `SourceDefinition31NativeContractBridgeReduction`
(native -> contract halts at the finite bad support, the Nat labels, the real
q-parameter layer, and every later clause).  It is therefore recorded as an
exact field-level Missing (above), not as an uninterpreted equivalence.  No
sorry/axiom/arbitrary carrier.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
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
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual

namespace LeanFormal.IUT.XiFPaper.S3134SameCBridgeActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
/- The OriginalInput side is taken at the same universe as the native record,
because the bridge compares the two `InitialThetaInput` values. -/
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The canonical native fragment of Definition 3.1 -/

/-- Selected places of the native initial Theta-data: the places of `V` inside
the K-places (IUT I, Definition 3.1, clause (e)). -/
def S3134NativeSelectedPlaces : Type :=
  {v : NumberFieldPlace T.arithmetic.K // v ∈ T.tuple.source.V}

/-- Bad places of the native initial Theta-data: the places of `V^bad_mod`
(IUT I, Definition 3.1, clause (e)). -/
def S3134NativeBadPlaces : Type :=
  {p : NumberField.FinitePlace T.arithmetic.Fmod //
    p ∈ T.tuple.source.V_mod_bad}

/-- The native bad-place inclusion is the actual place bijection
`V_mod_bijection` composed with the finite-place embedding. -/
def S3134NativeBadIncluded : S3134NativeBadPlaces T → S3134NativeSelectedPlaces T :=
  fun b => T.tuple.source.V_mod_bijection (NumberFieldPlace.finite b.1)

/-- The selected places of the native datum are nonempty: this is Definition
3.1's nonemptiness of the selected-place set transported along the actual
bijection. -/
theorem S3134NativeSelectedNonempty : Nonempty (S3134NativeSelectedPlaces T) := by
  rcases T.tuple.source.V_mod_bad_nonempty with ⟨p, _hp⟩
  exact ⟨T.tuple.source.V_mod_bijection (NumberFieldPlace.finite p)⟩

/-- The native bad-place inclusion is injective (the finite-place embedding is
injective and `V_mod_bijection` is an equivalence). -/
theorem S3134NativeBadIncluded_injective :
    Function.Injective (S3134NativeBadIncluded T) := by
  intro a b h
  have h₁ : NumberFieldPlace.finite a.1 =
      NumberFieldPlace.finite b.1 :=
    T.tuple.source.V_mod_bijection.injective h
  have h₂ : a.1 = b.1 := by
    injection h₁
  exact Subtype.ext h₂

/-! ## 2. The exact missing data of the native record -/

/-- Exact field-level missing data: the fields of `InitialThetaInput` that the
native Definition 3.1 datum does not determine on this carrier, with their
paper locations.  Every field is a named datum, not a default value. -/
structure S3134NativeContractMissing
    (T : SourceNativeInitialThetaData.{0} l) where
  /-- IUT I, Def. 3.1, clause (b): finiteness of the bad support.  The native
  carrier has `V^bad_mod` only as a set. -/
  badFinite : Fintype (S3134NativeBadPlaces T)
  /-- IUT I, Def. 3.1, clauses (b)/(c): the stable-reduction predicate on the
  bad places (the contract carries it; the native clauses do not). -/
  stableReduction : S3134NativeBadPlaces T → Prop
  stableReduction_proved : ∀ b, stableReduction b
  /-- IUT I, Def. 3.1, clause (d): the `imageContainsSL2` torsion proposition
  used by the contract. -/
  torsionImage : Prop
  torsionImage_proved : torsionImage
  /-- IUT I, Def. 3.1, clause (f): the real cusp parameter.  The native side
  carries the geometric boundary cusp `OrbicurveBoundaryCusp`, not a real
  number. -/
  cuspParameter : ℝ
  cusp_positive : 0 < cuspParameter

/-- The canonical native-to-`InitialThetaInput` construction, field by field,
given exactly the missing data above.  Every supplied field is either a
canonical projection of the native Definition 3.1 datum or the named missing
datum. -/
noncomputable def S3134NativeInitialThetaInput
    (M : S3134NativeContractMissing T) : InitialThetaInput.{0} l where
  arithmetic := T.arithmetic
  selectedPlaces := S3134NativeSelectedPlaces T
  badPlaces := S3134NativeBadPlaces T
  badIncluded := S3134NativeBadIncluded T
  selectedNonempty := S3134NativeSelectedNonempty T
  badFinite := M.badFinite
  stableReduction := M.stableReduction
  stableReduction_proved := M.stableReduction_proved
  torsionImage := M.torsionImage
  torsionImage_proved := M.torsionImage_proved
  cuspParameter := M.cuspParameter
  cusp_positive := M.cusp_positive

/-! ## 3. The same-C bridge and its field-level consequences -/

/-- The same-C bridge between the native initial Theta-data `T` and the
`OriginalInput` `J`: there is exact missing data making the canonical native
input equal to the contract input of `J`.  This is the named source
identification of the single qualified input `C` of IUT III, Corollary 3.12;
it is not derivable from the two records. -/
def S3134SameCContractBridge : Prop :=
  ∃ M : S3134NativeContractMissing T,
    S3134NativeInitialThetaInput T M = J.initialThetaInput

/-- Field-level consequence: the arithmetic root of Definition 3.1 is shared. -/
theorem S3134SameCContractBridge_arithmetic
    (H : S3134SameCContractBridge (J := J) (T := T)) :
    T.arithmetic = J.initialThetaInput.arithmetic := by
  obtain ⟨M, hM⟩ := H
  rw [← hM]
  rfl

/-- Field-level consequence: the selected-place types are identified. -/
theorem S3134SameCContractBridge_selectedPlaces
    (H : S3134SameCContractBridge (J := J) (T := T)) :
    S3134NativeSelectedPlaces T = J.initialThetaInput.selectedPlaces := by
  obtain ⟨M, hM⟩ := H
  rw [← hM]
  rfl

/-- Field-level consequence: the bad-place types are identified. -/
theorem S3134SameCContractBridge_badPlaces
    (H : S3134SameCContractBridge (J := J) (T := T)) :
    S3134NativeBadPlaces T = J.initialThetaInput.badPlaces := by
  obtain ⟨M, hM⟩ := H
  rw [← hM]
  rfl

/-- Field-level consequence: the bad-place inclusion is the native one. -/
theorem S3134SameCContractBridge_badIncluded
    (M : S3134NativeContractMissing T)
    (hM : S3134NativeInitialThetaInput T M = J.initialThetaInput) :
    HEq (S3134NativeBadIncluded T) J.initialThetaInput.badIncluded := by
  rw [← hM]
  exact HEq.refl _

/-- Field-level consequence: the bad support is finite. -/
theorem S3134SameCContractBridge_badFinite
    (M : S3134NativeContractMissing T)
    (hM : S3134NativeInitialThetaInput T M = J.initialThetaInput) :
    HEq M.badFinite J.initialThetaInput.badFinite := by
  rw [← hM]
  exact HEq.refl _

/-- Field-level consequence: the stable-reduction predicate is the native one. -/
theorem S3134SameCContractBridge_stableReduction
    (M : S3134NativeContractMissing T)
    (hM : S3134NativeInitialThetaInput T M = J.initialThetaInput) :
    HEq M.stableReduction J.initialThetaInput.stableReduction := by
  rw [← hM]
  exact HEq.refl _

/-- Field-level consequence: the torsion image proposition is shared. -/
theorem S3134SameCContractBridge_torsionImage
    (M : S3134NativeContractMissing T)
    (hM : S3134NativeInitialThetaInput T M = J.initialThetaInput) :
    M.torsionImage = J.initialThetaInput.torsionImage := by
  rw [← hM]
  rfl

/-- Field-level consequence: the real cusp parameter is the supplied one. -/
theorem S3134SameCContractBridge_cuspParameter
    (M : S3134NativeContractMissing T)
    (hM : S3134NativeInitialThetaInput T M = J.initialThetaInput) :
    M.cuspParameter = J.initialThetaInput.cuspParameter := by
  rw [← hM]
  rfl

/-! ## 4. Wiring the 3.11.5 => 3.12 comparison to the mainline readout -/

/-- The named same-C readout identification: the field-level contract bridge
plus the mainline q-side readout identification `S3131QC T = -|log(q)|`. -/
structure S3134SameCReadoutIdentification : Prop where
  bridge : S3134SameCContractBridge (J := J) (T := T)
  qc : S3134MainlineQCSameC (J := J) (T := T)

/-- The same-C bridge part of the readout identification. -/
theorem S3134SameCReadoutIdentification_bridge
    (H : S3134SameCReadoutIdentification (J := J) (T := T)) :
    S3134SameCContractBridge (J := J) (T := T) :=
  H.bridge

/-- The q-readout part of the same-C readout identification. -/
theorem S3134SameCReadoutIdentification_qc
    (H : S3134SameCReadoutIdentification (J := J) (T := T)) :
    S3134MainlineQCSameC (J := J) (T := T) :=
  H.qc

/-- **Wiring theorem**: through the named same-C readout identification, the
mainline actual q-side readout `S3131QC T` is bounded by the assembled
Theta-pilot readout of the 3.11.5 => 3.12 comparison. -/
theorem S3134Step3115_mainlineQC_le_thetaPilot_viaSameC
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    (H : S3134SameCReadoutIdentification (J := J) (T := T)) :
    S3131QC T ≤ S3134Step3115ThetaPilotReadout (I := I) D :=
  S3134Step3115_mainlineQC_le_thetaPilot (I := I) (J := J) (T := T) D G
    (S3134SameCReadoutIdentification_qc (J := J) (T := T) H)

#check S3134NativeSelectedPlaces
#check S3134NativeBadPlaces
#check S3134NativeBadIncluded_injective
#check S3134NativeContractMissing
#check S3134NativeInitialThetaInput
#check S3134SameCContractBridge
#check S3134SameCContractBridge_arithmetic
#check S3134SameCContractBridge_selectedPlaces
#check S3134SameCContractBridge_badPlaces
#check S3134SameCContractBridge_badIncluded
#check S3134SameCContractBridge_badFinite
#check S3134SameCContractBridge_stableReduction
#check S3134SameCContractBridge_torsionImage
#check S3134SameCContractBridge_cuspParameter
#check S3134SameCReadoutIdentification
#check S3134Step3115_mainlineQC_le_thetaPilot_viaSameC

end LeanFormal.IUT.XiFPaper.S3134SameCBridgeActual
-- S3134 same-C bridge: rebuild marker after quarantine fingerprint collision
