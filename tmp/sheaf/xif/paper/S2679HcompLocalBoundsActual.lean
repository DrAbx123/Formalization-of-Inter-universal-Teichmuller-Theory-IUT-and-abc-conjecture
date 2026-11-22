import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2679HcompLocalBoundsActual

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

/-- Each actual bad base q has order at least 1, from the source
FinitePlaceQCandidate positivity field. -/
theorem hcomp_order_ge_one
    (b : Bad (nativePlaceSelection T)) :
    1 ≤ (baseQ T b).order :=
  Nat.succ_le_of_lt (baseQ_order_pos T b)

/-- Each actual bad base residue norm is at least 2: it is the absolute
norm of a nonzero prime ideal, hence a natural number > 1. -/
theorem hcomp_residueNormBase_ge_two
    (b : Bad (nativePlaceSelection T)) :
    2 ≤ residueNormBase (nativeBaseSectionPlace T b) := by
  have hgt : (1 : Real) < residueNormBase (nativeBaseSectionPlace T b) :=
    residueNormBase_gt_one (nativeBaseSectionPlace T b)
  unfold residueNormBase at hgt ⊢
  have hnat : (1 : Nat) < Ideal.absNorm
      (nativeBaseSectionPlace T b).maximalIdeal.asIdeal := by
    exact_mod_cast hgt
  exact_mod_cast (Nat.succ_le_of_lt hnat)

/-- Local lower bound: |log q_b| >= log 2. -/
theorem hcomp_logMagnitude_ge_log2
    (b : Bad (nativePlaceSelection T)) :
    Real.log 2 ≤ baseQLogMagnitude T b := by
  rw [baseQLogMagnitude_eq_order_mul_log T b]
  have hresidue := hcomp_residueNormBase_ge_two T b
  have hres_pos : 0 < residueNormBase (nativeBaseSectionPlace T b) :=
    lt_trans zero_lt_one (residueNormBase_gt_one _)
  have hlog : Real.log 2 ≤ Real.log (residueNormBase (nativeBaseSectionPlace T b)) :=
    Real.log_le_log (by norm_num) hresidue
  have horder_real : (1 : Real) ≤ ((baseQ T b).order : Real) := by
    exact_mod_cast hcomp_order_ge_one T b
  have hmul := mul_le_mul horder_real hlog (le_of_lt (Real.log_pos (by norm_num)))
    (by positivity)
  simpa [one_mul] using hmul

/-- Global lower bound: total magnitude >= card(V_bad) * log 2. -/
theorem hcomp_global_ge_card_mul_log2
    [Fintype (Bad (nativePlaceSelection T))] :
    (Fintype.card (Bad (nativePlaceSelection T)) : Real) * Real.log 2 ≤ baseQTotalLogMagnitude T := by
  unfold baseQTotalLogMagnitude
  have hconst : (Fintype.card (Bad (nativePlaceSelection T)) : Real) * Real.log 2
      = ∑ _ : Bad (nativePlaceSelection T), Real.log 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hconst]
  exact Finset.sum_le_sum (fun b _ => hcomp_logMagnitude_ge_log2 T b)

/-- Cardinal sufficient condition: card(V_bad) >= 5 gives
2 log 5 <= total base-q magnitude. -/
theorem hcomp_global_ge_two_log5_of_card_ge_five
    [Fintype (Bad (nativePlaceSelection T))]
    (hcard : 5 ≤ Fintype.card (Bad (nativePlaceSelection T))) :
    2 * Real.log 5 ≤ baseQTotalLogMagnitude T := by
  have hlog2_pos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hcard_real : (5 : Real) ≤ (Fintype.card (Bad (nativePlaceSelection T)) : Real) := by
    exact_mod_cast hcard
  have h5log2 : 5 * Real.log 2 ≤ (Fintype.card (Bad (nativePlaceSelection T)) : Real) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hcard_real (le_of_lt hlog2_pos)
  have hlog_lt : 2 * Real.log 5 < 5 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num : (0 : Real) < 5) 2,
      ← Real.log_rpow (by norm_num : (0 : Real) < 2) 5]
    exact Real.log_lt_log (by positivity) (by norm_num)
  exact (le_of_lt hlog_lt).trans (h5log2.trans (hcomp_global_ge_card_mul_log2 T))

#check hcomp_order_ge_one
#check hcomp_residueNormBase_ge_two
#check hcomp_logMagnitude_ge_log2
#check hcomp_global_ge_card_mul_log2
#check hcomp_global_ge_two_log5_of_card_ge_five
#print axioms hcomp_order_ge_one
#print axioms hcomp_residueNormBase_ge_two
#print axioms hcomp_logMagnitude_ge_log2
#print axioms hcomp_global_ge_two_log5_of_card_ge_five

end LeanFormal.IUT.XiFPaper.S2679HcompLocalBoundsActual
end