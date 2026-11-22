import tmp.sheaf.xif.paper.S3134NativeContractShrinkActual

/-!
# S3134 task-19: the geometric cusp and the real cusp parameter

IUT I, Definition 3.1: initial Theta-data is the tuple
`(Fbar/F, X_F, l, C_K, V, V^bad_mod, epsilon)` (corpus `I-T.txt:3123-3126`),
and clause (f) (`I-T.txt:3273-3282`) defines `epsilon` as **a cusp of the
hyperbolic orbicurve C_K**, with the extra condition that for `v in V^bad` the
localized cusp `epsilon_v` is the cusp arising from the Tate uniformization.
So the paper's `epsilon` is a *geometric* cusp, not a real number; the total
space of `Iut.OrbicurveBoundaryCusp` is the compactification point with no
real-valued invariant.

The abstract contract `SourceDefinition31Data` nevertheless carries a real
`cusp.epsilon : Real` with `0 < epsilon` and an opaque
`epsilon_compatibility : Prop` (SourceDefinition31Boundary.lean:612-620).
This file:

1. constructs the partial data that the tree does determine:
   * the geometric cusp itself (`S3134NativeGeometricCusp`, from
     `SourceSignQuotientData.epsilon : Iut.OrbicurveBoundaryCusp cK`);
   * for every bad place, an actual place of F above it (Definition 3.1(e)
     section/restriction data, `comap_surjective`) and the actual Tate
     q-parameter candidate of clause (b) at that place
     (`SourceTateComparisonWitness.parameter : FinitePlaceQCandidate`);
   * the positive local q-order and a real q-magnitude in `(0,1)` built from
     the actual residue characteristic and valuation order — the real-valued
     shadow of the clause (f) cusp localization `epsilon_v`;
2. records that the *global real cusp parameter* (the contract's single
   `cusp.epsilon : Real`, positive) has **no real encoding** in the tree:
   `OrbicurveBoundaryCusp` is geometric (compactification/openMap/residueScheme/
   point/isBoundary), no real-valued invariant or cusp uniformizer is
   constructed, and the contract's `epsilon_compatibility` field is opaque.
   The exact Missing therefore remains the single field
   `S3134NativeCuspParameterMissing`;
3. states the final bridge status: `S3134SameCContractBridge` does **not**
   close fully; it remains equivalent to the reduced bridge with exactly this
   one real-cusp slot.  The 3.11.5 => 3.12 mainline consumer is unchanged.

No sorry/axiom/arbitrary carrier/toy; the missing slot is not renamed into
progress.  WRITE-ONLY: no lake/lean.
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
open LeanFormal.IUT.XiFPaper.S3134SameCBridgeActual
open LeanFormal.IUT.XiFPaper.S3134NativeContractShrinkActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual

namespace LeanFormal.IUT.XiFPaper.S3134CuspParameterActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. Partial pieces: the geometric cusp and its bad-place localizations -/

/-- The geometric cusp of the native initial Theta-data: the paper's
`epsilon`, a cusp of `C_K` (IUT I, Definition 3.1(f), `I-T.txt:3273-3282`). -/
def S3134CuspGeometricObject :
    Iut.OrbicurveBoundaryCusp T.tuple.source.cK :=
  T.tuple.source.epsilon

/-- A place of `F` above a bad place of `Fmod` (Definition 3.1(e) section). -/
noncomputable def S3134CuspBadPlaceLift (b : S3134NativeBadPlaces T) :
    NumberField.FinitePlace T.arithmetic.F :=
  Classical.choose (moduliPlace_fiber_nonempty (A := T.arithmetic) b.1)

/-- The lift restricts to the bad place. -/
theorem S3134CuspBadPlaceLift_comap (b : S3134NativeBadPlaces T) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (S3134CuspBadPlaceLift T b) = b.1 :=
  Classical.choose_spec (moduliPlace_fiber_nonempty (A := T.arithmetic) b.1)

/-- The actual Tate q-parameter candidate of clause (b) above a bad place
(`SourceTateComparisonWitness.parameter`, Definition 3.1(b)). -/
noncomputable def S3134CuspBadPlaceQParameter
    (b : S3134NativeBadPlaces T) :
    NumberFieldFinitePlace.FinitePlaceQCandidate (S3134CuspBadPlaceLift T b) :=
  (Classical.choice (T.clauseB.q_comparison (S3134CuspBadPlaceLift T b)
    (by rw [S3134CuspBadPlaceLift_comap T b]; exact b.2))).parameter

/-- The positive local q-order of the clause (b) Tate parameter. -/
noncomputable def S3134CuspBadPlaceQOrder
    (b : S3134NativeBadPlaces T) : Nat :=
  (S3134CuspBadPlaceQParameter T b).order

/-- The local q-order is positive. -/
theorem S3134CuspBadPlaceQOrder_pos (b : S3134NativeBadPlaces T) :
    0 < S3134CuspBadPlaceQOrder T b :=
  NumberFieldFinitePlace.FinitePlaceQCandidate.order_pos
    (S3134CuspBadPlaceQParameter T b)

/-- The real q-magnitude of the clause (b) Tate parameter at a bad place: the
residue characteristic to the negative local q-order.  This is a real-valued
shadow of the clause (f) cusp localization `epsilon_v` (for `v in V^bad` the
cusp is the Tate cusp). -/
noncomputable def S3134CuspBadPlaceQMagnitude
    (b : S3134NativeBadPlaces T) : ℝ :=
  (NumberFieldFinitePlace.residueCharacteristic (S3134CuspBadPlaceLift T b) : ℝ) ^
    (-(S3134CuspBadPlaceQOrder T b : ℤ))

/-- The constructed real q-magnitude lies in `(0,1)`: this is the paper's
`|q| < 1` range for the cusp localization at a bad place, realized as an
actual real number. -/
theorem S3134CuspBadPlaceQMagnitude_pos_lt_one
    (b : S3134NativeBadPlaces T) :
    0 < S3134CuspBadPlaceQMagnitude T b ∧
      S3134CuspBadPlaceQMagnitude T b < 1 := by
  have hprime : Nat.Prime
      (NumberFieldFinitePlace.residueCharacteristic
        (S3134CuspBadPlaceLift T b)) :=
    NumberFieldFinitePlace.residueCharacteristic_prime _
  have hr : (1 : ℝ) <
      (NumberFieldFinitePlace.residueCharacteristic
        (S3134CuspBadPlaceLift T b) : ℝ) := by
    exact_mod_cast hprime.one_lt
  have hn : S3134CuspBadPlaceQOrder T b ≠ 0 :=
    (S3134CuspBadPlaceQOrder_pos T b).ne'
  have hpow : (1 : ℝ) <
      (NumberFieldFinitePlace.residueCharacteristic
        (S3134CuspBadPlaceLift T b) : ℝ) ^
        S3134CuspBadPlaceQOrder T b :=
    one_lt_pow₀ hr hn
  rw [S3134CuspBadPlaceQMagnitude, zpow_neg, zpow_natCast]
  exact ⟨inv_pos.mpr (lt_trans zero_lt_one hpow),
    inv_lt_one_of_one_lt₀ hpow⟩

/-! ## 2. The exact remaining slot: no real encoding of the geometric cusp -/

/-- Exact field-level Missing of task-19.  The paper's `epsilon` is a cusp of
`C_K` (geometric); the tree's carrier `Iut.OrbicurveBoundaryCusp` consists of
compactification/open-immersion/residue-scheme/point/boundary data and carries
no real-valued invariant or cusp uniformizer, and the abstract contract's
`cusp.epsilon : Real` and `epsilon_compatibility : Prop` are fields of
`SourceDefinition31Data` with no theorem relating them to a geometric cusp.
So a real-valued cusp parameter cannot be derived; the slot is exactly this
real number with its positivity. -/
abbrev S3134CuspParameterExactMissing
    (T : SourceNativeInitialThetaData.{0} l) : Type :=
  S3134NativeCuspParameterMissing T

/-- The reduced same-C bridge, equivalently with the single real-cusp slot
spelled out; this is the exact state of `S3134SameCContractBridge`. -/
theorem S3134SameCContractBridge_status :
    S3134SameCContractBridgeReduced (J := J) (T := T) ↔
      ∃ M : S3134CuspParameterExactMissing T,
        S3134NativeInitialThetaInputReduced T M =
          J.initialThetaInput :=
  Iff.rfl

/-- The same-C bridge with the real-cusp data supplied closes the task-12
bridge; without it the bridge is not derivable. -/
theorem S3134SameCContractBridge_ofCuspParameter
    (M : S3134CuspParameterExactMissing T)
    (hM : S3134NativeInitialThetaInputReduced T M =
      J.initialThetaInput) :
    S3134SameCContractBridge (J := J) (T := T) :=
  S3134SameCContractBridge_ofReduced (J := J) (T := T) ⟨M, hM⟩

/-! ## 3. The 3.11.5 => 3.12 mainline consumer (reduced slot) -/

/-- The mainline consumer with the reduced same-C slot (unchanged from
task-16): the mainline actual q-side readout is bounded by the assembled
Theta-pilot readout once the real-cusp slot is supplied. -/
theorem S3134Step3115_mainlineQC_le_thetaPilot_viaCuspSlot
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    (H : S3134SameCReadoutIdentificationReduced (J := J) (T := T)) :
    S3131QC T ≤ S3134Step3115ThetaPilotReadout (I := I) D :=
  S3134Step3115_mainlineQC_le_thetaPilot_viaSameCReduced
    (I := I) (J := J) (T := T) D G H

#check S3134CuspGeometricObject
#check S3134CuspBadPlaceLift
#check S3134CuspBadPlaceLift_comap
#check S3134CuspBadPlaceQParameter
#check S3134CuspBadPlaceQOrder
#check S3134CuspBadPlaceQOrder_pos
#check S3134CuspBadPlaceQMagnitude
#check S3134CuspBadPlaceQMagnitude_pos_lt_one
#check S3134CuspParameterExactMissing
#check S3134SameCContractBridge_status
#check S3134SameCContractBridge_ofCuspParameter
#check S3134Step3115_mainlineQC_le_thetaPilot_viaCuspSlot

end LeanFormal.IUT.XiFPaper.S3134CuspParameterActual
