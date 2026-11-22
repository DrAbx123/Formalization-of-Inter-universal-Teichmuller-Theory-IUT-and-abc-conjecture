import tmp.sheaf.xif.paper.O2QrootGlueActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-!
# Route C0: root-side q-lattice comparison (explicit objects)

From the original q data, take the actual qroot `alpha_b := qrootElem T b` and
the normalized q image `qhat_b := alpha_b^(2l)` (proved equal to the q image).
Then:
* alpha_b is integral (unit ball);
* qhat_b * O_b subset alpha_b * O_b;
* finite product Q_root subset H_root;
* Haar measure comparison;
* explicit remainder ((2l-1) * sum_b d_b * (-log||alpha_b||)) >= 0.

No comparison hypothesis is used.  The lattice sets are set-level unit-ball
images, not a constructed ring-of-integers object (see gap note).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- alpha_b: the actual qroot (2l-th root of q). -/
noncomputable def c0Alpha (b : Bad (nativePlaceSelection T)) : rootNormedExtension T b :=
  qrootElem T b

/-- qhat_b: the normalized q image alpha_b^(2l). -/
noncomputable def c0QHat (b : Bad (nativePlaceSelection T)) : rootNormedExtension T b :=
  (c0Alpha T b) ^ (2 * l.value)

theorem c0QHat_eq_q (b : Bad (nativePlaceSelection T)) :
    c0QHat T b = algebraMap (rootBase T b) (rootNormedExtension T b)
      ((LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual.qVFamily T b).q : rootBase T b) := by
  unfold c0QHat c0Alpha
  exact qrootElem_pow T b

theorem c0Alpha_norm_le_one (b : Bad (nativePlaceSelection T)) :
    ‖c0Alpha T b‖ ≤ 1 := by
  unfold c0Alpha qrootElem qrootUnit
  have h := rootNormedElement_norm_le_one (T := T) (b := b) (rootQUnitNormLeOne (T := T))
  simpa [rootNormedUnit] using h

theorem c0Alpha_ne_zero (b : Bad (nativePlaceSelection T)) : c0Alpha T b ≠ 0 :=
  qrootElem_ne_zero T b

/-- Unit ball O_b (set-level integral lattice). -/
def c0UnitBall (b : Bad (nativePlaceSelection T)) : Set (rootNormedExtension T b) :=
  rootExtensionUnitBall T b

/-- qhat_b * O_b. -/
def c0QLattice (b : Bad (nativePlaceSelection T)) : Set (rootNormedExtension T b) :=
  (fun y => c0QHat T b * y) '' c0UnitBall T b

/-- alpha_b * O_b. -/
def c0HLattice (b : Bad (nativePlaceSelection T)) : Set (rootNormedExtension T b) :=
  (fun y => c0Alpha T b * y) '' c0UnitBall T b

/-- Integrality: alpha_b^(2l-1) is in O_b when alpha_b is. -/
theorem c0Alpha_pow_sub_one_mem (b : Bad (nativePlaceSelection T))
    {x : rootNormedExtension T b} (hx : x ∈ c0UnitBall T b) :
    (c0Alpha T b) ^ (2 * l.value - 1) * x ∈ c0UnitBall T b := by
  unfold c0UnitBall rootExtensionUnitBall at hx ⊢
  rw [Metric.mem_closedBall, dist_eq_norm] at hx ⊢
  simp only [sub_zero] at hx ⊢
  rw [norm_mul]
  have ha : ‖c0Alpha T b‖ ≤ 1 := c0Alpha_norm_le_one T b
  have hpow : ‖c0Alpha T b ^ (2 * l.value - 1)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha
  exact mul_le_one₀ hpow (norm_nonneg _) hx

/-- qhat_b * O_b subset alpha_b * O_b. -/
theorem c0QLattice_subset_alpha (b : Bad (nativePlaceSelection T)) :
    c0QLattice T b ⊆ c0HLattice T b := by
  rintro z ⟨y, hy, rfl⟩
  refine ⟨(c0Alpha T b) ^ (2 * l.value - 1) * y, c0Alpha_pow_sub_one_mem T b hy, ?_⟩
  rw [c0QHat]
  dsimp only
  have hpow : (c0Alpha T b) ^ (2 * l.value) =
      c0Alpha T b * (c0Alpha T b) ^ (2 * l.value - 1) := by
    have hl : 5 ≤ l.value := l.ge_five
    conv_lhs => rw [show 2 * l.value = (2 * l.value - 1) + 1 by omega]
    rw [pow_succ']
  change c0Alpha T b * ((c0Alpha T b) ^ (2 * l.value - 1) * y) =
    (c0Alpha T b) ^ (2 * l.value) * y
  rw [← mul_assoc, ← hpow]

/-- Product Q_root. -/
def c0ProductQ : Set (RootExtensionProductCarrier T) :=
  Set.pi Set.univ (fun b => c0QLattice T b)

/-- Product H_root. -/
def c0ProductH : Set (RootExtensionProductCarrier T) :=
  Set.pi Set.univ (fun b => c0HLattice T b)

theorem c0ProductQ_subset_H : c0ProductQ T ⊆ c0ProductH T := by
  intro x hx b hb
  exact c0QLattice_subset_alpha T b (hx b hb)

theorem c0ProductHaar_mono :
    rootExtensionProductHaar T (c0ProductQ T) ≤
      rootExtensionProductHaar T (c0ProductH T) :=
  measure_mono (c0ProductQ_subset_H T)

/-- Explicit C0 remainder coefficient. -/
noncomputable def c0Remainder : Real :=
  ((2 * (l.value : Real) - 1) *
    ∑ b : Bad (nativePlaceSelection T),
      (Module.finrank ℚ_[(LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b)] (rootNormedExtension T b) : Real) *
        (-Real.log ‖c0Alpha T b‖))

theorem c0Remainder_nonneg : 0 ≤ c0Remainder T := by
  unfold c0Remainder
  have hcoef : 0 ≤ 2 * (l.value : Real) - 1 := by
    have : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
    linarith
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      0 ≤ (Module.finrank ℚ_[(LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b)] (rootNormedExtension T b) : Real) *
        (-Real.log ‖c0Alpha T b‖) := by
    intro b
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · have hnormpos : 0 < ‖c0Alpha T b‖ := norm_pos_iff.mpr (c0Alpha_ne_zero T b)
      have hlog : Real.log ‖c0Alpha T b‖ ≤ 0 :=
        Real.log_nonpos (le_of_lt hnormpos) (c0Alpha_norm_le_one T b)
      linarith
  exact mul_nonneg hcoef (Finset.sum_nonneg (fun b _ => hterm b))

/-- Route C0 constructed bundle. -/
theorem routeC0_constructed :
    (∀ b, c0QHat T b = algebraMap (rootBase T b) (rootNormedExtension T b)
        ((LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual.qVFamily T b).q : rootBase T b)) ∧
      (∀ b, ‖c0Alpha T b‖ ≤ 1) ∧
      (∀ b, c0QLattice T b ⊆ c0HLattice T b) ∧
      c0ProductQ T ⊆ c0ProductH T ∧
      rootExtensionProductHaar T (c0ProductQ T) ≤ rootExtensionProductHaar T (c0ProductH T) ∧
      0 ≤ c0Remainder T := by
  refine ⟨c0QHat_eq_q T, c0Alpha_norm_le_one T, c0QLattice_subset_alpha T,
    c0ProductQ_subset_H T, c0ProductHaar_mono T, c0Remainder_nonneg T⟩

#print axioms routeC0_constructed

end LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
