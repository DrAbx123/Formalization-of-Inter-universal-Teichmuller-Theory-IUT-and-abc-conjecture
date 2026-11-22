import tmp.sheaf.xif.paper.BaseQLogVolumeActual

/-! # Global q-pilot magnitude versus the Gaussian signed average

For an actual native T, the base q family is

  baseQ T b : FinitePlaceQCandidate (nativeBaseSectionPlace T b),

with actual magnitude

  baseQLogMagnitude T b
    = order_b * log (residueNormBase (nativeBaseSectionPlace T b)).

The actual global base-q magnitude is

  nativeBaseQGlobalMagnitude T
    = sum_b baseQLogMagnitude T b.

The Gaussian signed average at q = 1/5 is 2*log 5 (computed in
SignedAverageBoundActual: gaussExponentSum/card = 2 for l = 5).

This file proves:

* positivity/nonnegativity of each local magnitude;
* the exact cardinality/term formula;
* a sufficient lower bound N * log 2 from order >= 1 and residue norm >= 2;
* the exact obstruction for the empty bad set (magnitude 0 < 2 log 5);
* the exact condition under which the comparison holds.

It does NOT assert the comparison unconditionally: the actual orders and residue
norms of the native family can make the total smaller than 2 log 5.  No fake
inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GlobalQPilotComparisonTruthActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Number of actual native bad places. -/
noncomputable def nativeBadPlaceCount [Fintype (Bad (nativePlaceSelection T))] : Nat :=
  Fintype.card (Bad (nativePlaceSelection T))

/-- The actual global base-q magnitude. -/
noncomputable def nativeBaseQGlobalMagnitude
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  baseQTotalLogMagnitude T

/-- Exact pointwise formula for the base q magnitude. -/
theorem nativeBaseQLogMagnitude_eq
    (b : Bad (nativePlaceSelection T)) :
    baseQLogMagnitude T b =
      ((baseQ T b).order : Real) *
        Real.log (residueNormBase (nativeBaseSectionPlace T b)) :=
  baseQLogMagnitude_eq_order_mul_log T b

/-- Each actual base q log-magnitude is positive. -/
theorem nativeBaseQLogMagnitude_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < baseQLogMagnitude T b :=
  baseQLogMagnitude_pos T b

/-- The actual global base-q magnitude is the finite sum of the local magnitudes. -/
theorem nativeBaseQGlobalMagnitude_eq_sum
    [Fintype (Bad (nativePlaceSelection T))] :
    nativeBaseQGlobalMagnitude T =
      ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := rfl

/-- The actual global magnitude is nonnegative. -/
theorem nativeBaseQGlobalMagnitude_nonneg
    [Fintype (Bad (nativePlaceSelection T))] :
    0 ≤ nativeBaseQGlobalMagnitude T := by
  unfold nativeBaseQGlobalMagnitude baseQTotalLogMagnitude
  exact Finset.sum_nonneg (fun b _ => le_of_lt (nativeBaseQLogMagnitude_pos T b))

/-- If V_bad is empty, the global magnitude is exactly zero. -/
theorem nativeBaseQGlobalMagnitude_eq_zero_of_isEmpty
    [Fintype (Bad (nativePlaceSelection T))]
    [IsEmpty (Bad (nativePlaceSelection T))] :
    nativeBaseQGlobalMagnitude T = 0 := by
  unfold nativeBaseQGlobalMagnitude baseQTotalLogMagnitude
  simp

/-- Empty V_bad refutes the comparison with 2 log 5. -/
theorem not_nativeBaseQGlobalMagnitude_ge_two_log5_of_isEmpty
    [Fintype (Bad (nativePlaceSelection T))]
    [IsEmpty (Bad (nativePlaceSelection T))] :
    ¬ (2 * Real.log 5 ≤ nativeBaseQGlobalMagnitude T) := by
  rw [nativeBaseQGlobalMagnitude_eq_zero_of_isEmpty T]
  have hpos : 0 < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  linarith

/-- Sufficient local lower bound: if every base q has order at least one and
every base residue norm is at least 2, then each local magnitude is at least
log 2. -/
theorem nativeBaseQLogMagnitude_ge_log2_of_order_residue
    (b : Bad (nativePlaceSelection T))
    (horder : 1 ≤ (baseQ T b).order)
    (hresidue : 2 ≤ residueNormBase (nativeBaseSectionPlace T b)) :
    Real.log 2 ≤ baseQLogMagnitude T b := by
  rw [nativeBaseQLogMagnitude_eq T b]
  have hres_pos : 0 < residueNormBase (nativeBaseSectionPlace T b) :=
    lt_trans zero_lt_one (residueNormBase_gt_one _)
  have hlog : Real.log 2 ≤
      Real.log (residueNormBase (nativeBaseSectionPlace T b)) :=
    Real.log_le_log (by norm_num) hresidue
  have horder_real : (1 : Real) ≤ ((baseQ T b).order : Real) := by
    exact_mod_cast horder
  have hmul := mul_le_mul horder_real hlog (le_of_lt (Real.log_pos (by norm_num)))
    (by positivity)
  simpa [one_mul] using hmul

/-- Cardinal lower bound: under the local order/residue hypotheses, the global
magnitude is at least card(V_bad) * log 2. -/
theorem nativeBaseQGlobalMagnitude_ge_card_mul_log2
    [Fintype (Bad (nativePlaceSelection T))]
    (horder : ∀ b, 1 ≤ (baseQ T b).order)
    (hresidue : ∀ b, 2 ≤ residueNormBase (nativeBaseSectionPlace T b)) :
    (nativeBadPlaceCount T : Real) * Real.log 2 ≤ nativeBaseQGlobalMagnitude T := by
  unfold nativeBaseQGlobalMagnitude baseQTotalLogMagnitude nativeBadPlaceCount
  have hconst : (Fintype.card (Bad (nativePlaceSelection T)) : Real) * Real.log 2
      = ∑ _ : Bad (nativePlaceSelection T), Real.log 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hconst]
  exact Finset.sum_le_sum (fun b _ =>
    nativeBaseQLogMagnitude_ge_log2_of_order_residue T b (horder b) (hresidue b))

/-- A concrete cardinal sufficient condition: if card(V_bad) >= 5 and every
local term is at least log 2, then the global magnitude is at least 2 log 5,
because 5 log 2 = log 32 > log 25 = 2 log 5. -/
theorem nativeBaseQGlobalMagnitude_ge_two_log5_of_card_ge_five
    [Fintype (Bad (nativePlaceSelection T))]
    (hcard : 5 ≤ nativeBadPlaceCount T)
    (horder : ∀ b, 1 ≤ (baseQ T b).order)
    (hresidue : ∀ b, 2 ≤ residueNormBase (nativeBaseSectionPlace T b)) :
    2 * Real.log 5 ≤ nativeBaseQGlobalMagnitude T := by
  have hlog2_pos : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num)
  have hcard_real : (5 : Real) ≤ (nativeBadPlaceCount T : Real) := by
    exact_mod_cast hcard
  have h5log2 : 5 * Real.log 2 ≤ (nativeBadPlaceCount T : Real) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hcard_real (le_of_lt hlog2_pos)
  have hlog_lt : 2 * Real.log 5 < 5 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num : (0 : Real) < 5) 2,
      ← Real.log_rpow (by norm_num : (0 : Real) < 2) 5]
    exact Real.log_lt_log (by positivity) (by norm_num)
  exact (le_of_lt hlog_lt).trans (h5log2.trans
    (nativeBaseQGlobalMagnitude_ge_card_mul_log2 T horder hresidue))

/-- Exact comparison condition: the actual comparison is precisely the lower
bound on the global base-q magnitude. -/
def NativeGlobalQPilotComparison
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  2 * Real.log 5 ≤ nativeBaseQGlobalMagnitude T

/-- The comparison follows from the cardinal/local sufficient conditions. -/
theorem nativeGlobalQPilotComparison_of_card_ge_five
    [Fintype (Bad (nativePlaceSelection T))]
    (hcard : 5 ≤ nativeBadPlaceCount T)
    (horder : ∀ b, 1 ≤ (baseQ T b).order)
    (hresidue : ∀ b, 2 ≤ residueNormBase (nativeBaseSectionPlace T b)) :
    NativeGlobalQPilotComparison T :=
  nativeBaseQGlobalMagnitude_ge_two_log5_of_card_ge_five T hcard horder hresidue

/-- Exact obstruction: for empty V_bad the comparison is false. -/
def NativeGlobalQPilotComparisonObstruction : Prop :=
  IsEmpty (Bad (nativePlaceSelection T))

end LeanFormal.IUT.XiFPaper.GlobalQPilotComparisonTruthActual

end
