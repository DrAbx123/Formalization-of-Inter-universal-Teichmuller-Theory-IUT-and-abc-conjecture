import tmp.sheaf.xif.paper.S3134CuspParameterActual

/-!
# S3134 task-21: constructing the real cusp parameter from actual Tate q magnitudes

Task-19 left the same-C bridge with one data slot: a real cusp parameter
`S3134NativeCuspParameterMissing` (`cuspParameter : Real`, `0 < cuspParameter`).
This file constructs that real number from actual clause-(b) Tate q-parameter
data and thereby eliminates the data slot.

**Component, not paper object.**  The paper object is the geometric cusp
`epsilon` of `C_K` (`S3134CuspGeometricObject` in `S3134CuspParameterActual`);
the real number constructed here is the numeric encoding of its clause (f)
Tate-cusp localizations.  It is a prerequisite component of the same-C bridge,
with named consumers `S3134SameCContractBridgeEpsilonResidual` and
`S3134Step3115_mainlineQC_le_thetaPilot_viaEpsilon`.

The construction:

* the geometric cusp is the paper's `epsilon` (IUT I, Definition 3.1 tuple
  I-T.txt:3123-3126 and clause (f) :3273-3282);
* for every bad place `v in V^bad`, clause (b) gives an actual Tate
  q-parameter candidate (Definition 3.1(b), I-T.txt:3141-3147 and :3131-3133);
  its real q magnitude `0 < residueChar^(-order) < 1` was constructed in
  `S3134CuspParameterActual` (`S3134CuspBadPlaceQMagnitude_pos_lt_one`);
* the real cusp parameter is the *minimal* local magnitude over the whole bad
  support, i.e. the normalization
  `epsilon = min { |q_v| : v in V^bad }` in (0,1).  It is v-independent by
  construction (it uses the whole bad support, not a chosen place) and
  satisfies the v-consistency `epsilon <= |q_v|` for every bad place `v`;
* `S3134CuspParameterConstructed` fills `S3134NativeCuspParameterMissing`.

Consequence: the same-C bridge no longer needs a data existential.  Its
remaining content is the record-level identification
`S3134SameCContractBridgeEpsilonResidual`; its cusp component is exactly the
numeric identification `epsilon = J.cuspParameter` (the contract's opaque
`cusp.epsilon : Real`; the contract's `epsilon_compatibility : Prop` is a
separate opaque field of `SourceCuspClause` not even carried by
`InitialThetaInput`).  So the bridge does NOT close fully; it reduces to this
single named residual, which is a source identification, not a missing object.

No sorry/axiom/arbitrary Real (epsilon is built from actual residue
characteristics and Tate q-orders); no toy carrier.  WRITE-ONLY: no lake/lean.
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
open Classical
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134SameCBridgeActual
open LeanFormal.IUT.XiFPaper.S3134NativeContractShrinkActual
open LeanFormal.IUT.XiFPaper.S3134CuspParameterActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual

namespace LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The finite bad support and the real cusp parameter -/

/-- The finite bad support of the same-C input, as a Fintype on the native bad
places. -/
noncomputable instance S3134CuspBadFinite :
    Fintype (S3134NativeBadPlaces T) :=
  S3134NativeBadFinite T

/-- The bad support is nonempty (Definition 3.1(b)). -/
theorem S3134CuspBadNonempty : Nonempty (S3134NativeBadPlaces T) := by
  obtain ⟨p, hp⟩ := T.tuple.source.V_mod_bad_nonempty
  exact ⟨⟨p, hp⟩⟩

/-- The values of the actual clause-(b) Tate q magnitudes over the bad support. -/
noncomputable abbrev S3134CuspQMagnitudeValues : Finset ℝ :=
  (Finset.univ : Finset (S3134NativeBadPlaces T)).image
    (fun b => S3134CuspBadPlaceQMagnitude T b)

/-- The value set is nonempty. -/
theorem S3134CuspQMagnitudeValues_nonempty :
    (S3134CuspQMagnitudeValues T).Nonempty :=
  Finset.Nonempty.image
    (Finset.univ_nonempty_iff.mpr (S3134CuspBadNonempty T))
    (fun b => S3134CuspBadPlaceQMagnitude T b)

/-- The real cusp parameter: the smallest actual clause-(b) Tate q magnitude
over the bad support, i.e. the normalization
`min { |q_v| : v in V^bad }` in (0,1). -/
noncomputable def S3134CuspEpsilonReal : ℝ :=
  (S3134CuspQMagnitudeValues T).min'
    (S3134CuspQMagnitudeValues_nonempty T)

/-- The constructed real cusp parameter is positive. -/
theorem S3134CuspEpsilonReal_pos : 0 < S3134CuspEpsilonReal T := by
  unfold S3134CuspEpsilonReal
  obtain ⟨b, _hb, hval⟩ :=
    Finset.mem_image.mp
      (Finset.min'_mem (S3134CuspQMagnitudeValues T)
        (S3134CuspQMagnitudeValues_nonempty T))
  rw [← hval]
  exact (S3134CuspBadPlaceQMagnitude_pos_lt_one T b).1

/-- The constructed real cusp parameter is strictly less than one. -/
theorem S3134CuspEpsilonReal_lt_one : S3134CuspEpsilonReal T < 1 := by
  unfold S3134CuspEpsilonReal
  obtain ⟨b, _hb, hval⟩ :=
    Finset.mem_image.mp
      (Finset.min'_mem (S3134CuspQMagnitudeValues T)
        (S3134CuspQMagnitudeValues_nonempty T))
  rw [← hval]
  exact (S3134CuspBadPlaceQMagnitude_pos_lt_one T b).2

/-- v-consistency/normalization: the real cusp parameter is at most every local
Tate q magnitude at v in V^bad. -/
theorem S3134CuspEpsilonReal_le_local (b : S3134NativeBadPlaces T) :
    S3134CuspEpsilonReal T ≤ S3134CuspBadPlaceQMagnitude T b := by
  unfold S3134CuspEpsilonReal
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)

/-! ## 2. Filling the cusp parameter data slot -/

/-- The constructed cusp parameter data fills the task-16 slot: this is an
actual real number built from the actual clause-(b) Tate q magnitudes, not an
assumed data field. -/
noncomputable def S3134CuspParameterConstructed :
    S3134NativeCuspParameterMissing T where
  cuspParameter := S3134CuspEpsilonReal T
  cusp_positive := S3134CuspEpsilonReal_pos T

/-- The canonical native input with the constructed real cusp parameter. -/
noncomputable def S3134NativeInitialThetaInputConstructed
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : InitialThetaInput.{0} l :=
  S3134NativeInitialThetaInputReduced T (S3134CuspParameterConstructed T)

/-! ## 3. Bridge status: one named residual remains -/

/-- The exact residual of the same-C bridge after the cusp data slot has been
constructed: the record-level identification of the canonical native input
(containing the constructed epsilon) with the contract input of `J`.  Its cusp
component is the numeric identification `epsilon = J.cuspParameter`; the
contract's opaque `epsilon_compatibility : Prop` is not part of
`InitialThetaInput`. -/
def S3134SameCContractBridgeEpsilonResidual
    (J : OriginalInput.{0, uv, upi, umon, ui} l V)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  S3134NativeInitialThetaInputConstructed T = J.initialThetaInput

/-- The residual reduces to the numeric cusp identification. -/
theorem S3134SameCContractBridgeEpsilonResidual_cusp
    (h : S3134SameCContractBridgeEpsilonResidual (J := J) (T := T)) :
    S3134CuspEpsilonReal T = J.initialThetaInput.cuspParameter := by
  unfold S3134SameCContractBridgeEpsilonResidual at h
  have hc := congrArg (fun K : InitialThetaInput.{0} l => K.cuspParameter) h
  simpa [S3134NativeInitialThetaInputConstructed,
    S3134NativeInitialThetaInputReduced, S3134CuspParameterConstructed] using hc

/-- The residual implies the task-16 reduced bridge (fill the constructed
slot). -/
theorem S3134SameCContractBridgeReduced_ofEpsilonResidual
    (h : S3134SameCContractBridgeEpsilonResidual (J := J) (T := T)) :
    S3134SameCContractBridgeReduced (J := J) (T := T) := by
  unfold S3134SameCContractBridgeEpsilonResidual at h
  exact ⟨S3134CuspParameterConstructed T, by
    simpa [S3134NativeInitialThetaInputConstructed] using h⟩

/-- The residual implies the task-12 same-C bridge. -/
theorem S3134SameCContractBridge_ofEpsilonResidual
    (h : S3134SameCContractBridgeEpsilonResidual (J := J) (T := T)) :
    S3134SameCContractBridge (J := J) (T := T) :=
  S3134SameCContractBridge_ofReduced (J := J) (T := T)
    (S3134SameCContractBridgeReduced_ofEpsilonResidual (J := J) (T := T) h)

/-- The epsilon residual is exactly the same-C bridge with the constructed
(non-existential) cusp readout: the only remaining content is the named
numeric/record identification. -/
theorem S3134SameCContractBridgeEpsilonResidual_iff_bridgeReduced :
    S3134SameCContractBridgeEpsilonResidual (J := J) (T := T) ↔
      S3134NativeInitialThetaInputReduced T
          (S3134CuspParameterConstructed T) = J.initialThetaInput := by
  constructor
  · intro h
    unfold S3134SameCContractBridgeEpsilonResidual at h
    simpa [S3134NativeInitialThetaInputConstructed] using h
  · intro h
    unfold S3134SameCContractBridgeEpsilonResidual
    simpa [S3134NativeInitialThetaInputConstructed] using h

/-! ## 4. Consumer: the signed 3.11.5 => 3.12 wiring with the constructed epsilon -/

/-- Mainline consumer with the constructed cusp parameter: once the named
epsilon residual holds together with the q-readout identification,
`S3131QC T <= -|log(Theta)|` follows from the actual assembled comparison. -/
theorem S3134Step3115_mainlineQC_le_thetaPilot_viaEpsilon
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    (hres : S3134SameCContractBridgeEpsilonResidual (J := J) (T := T))
    (hqc : S3134MainlineQCSameC (J := J) (T := T)) :
    S3131QC T ≤ S3134Step3115ThetaPilotReadout (I := I) D :=
  S3134Step3115_mainlineQC_le_thetaPilot_viaSameCReduced (I := I) (J := J) (T := T)
    D G
    { bridge := S3134SameCContractBridgeReduced_ofEpsilonResidual (J := J) (T := T) hres
      qc := hqc }

#check S3134CuspBadFinite
#check S3134CuspBadNonempty
#check S3134CuspQMagnitudeValues_nonempty
#check S3134CuspEpsilonReal
#check S3134CuspEpsilonReal_pos
#check S3134CuspEpsilonReal_lt_one
#check S3134CuspEpsilonReal_le_local
#check S3134CuspParameterConstructed
#check S3134NativeInitialThetaInputConstructed
#check S3134SameCContractBridgeEpsilonResidual
#check S3134SameCContractBridgeEpsilonResidual_cusp
#check S3134SameCContractBridgeReduced_ofEpsilonResidual
#check S3134SameCContractBridge_ofEpsilonResidual

end LeanFormal.IUT.XiFPaper.S3134CuspUniformizerActual
