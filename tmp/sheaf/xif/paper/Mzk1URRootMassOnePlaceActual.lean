/- R1 first piece (kurt): actual normalized log-mass of the q-root lattice in the common finite
extension L_w = rootNormedExtension T b (route section 3.2, simultaneous base change; Lead ruling (A)).

Carrier: the actual root extension L (NontriviallyNormedField, FiniteDimensional over Q_p,
Proper, with rootExtensionHaar an additive Haar measure and the closed unit ball O).
Contents proved here:
* rootUnitBall_smul_of_norm_one: a norm-one field element preserves the closed unit ball;
* log_rootHaar_prime_pow: log mu((p^k) * O) = -k*d*log p + log mu(O), k : Nat, by iterating the
  accepted prime-scaling donor FinitePadicHaarScaling.LeanFormal.IUT.FinitePadicHaarScaling.log_measure_prime_smul_finiteDimensional;
* rootNu: the normalized log-mass nu(S) := (1/d) * (log mu S - log mu O).
The general element r (with r = p^k * u, k : Int) needs the integer-power (zpow) iteration and the
value-group decomposition of the actual root; those are the next R1 statements (listed, not faked).

Default heartbeats; all donors DONE (check oleans present).
-/
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import tmp.sheaf.xif.paper.PaperRootExtensionHaarFactorActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeScalingActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Pointwise
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1URRootMassOnePlaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.FinitePadicHaarScaling

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- A norm-one element of the root extension preserves the closed unit ball. -/
theorem rootUnitBall_smul_of_norm_one (u : (rootNormedExtension T b)ˣ)
    (h : ‖(u : rootNormedExtension T b)‖ = 1) :
    (u : rootNormedExtension T b) • rootExtensionUnitBall T b =
      rootExtensionUnitBall T b := by
  unfold rootExtensionUnitBall
  rw [smul_unitClosedBall, h]

/-- Normalized log-mass of a set: (1/[L:Q_p]) * (log mu S - log mu O). -/
noncomputable def rootNu (S : Set (rootNormedExtension T b)) : ℝ :=
  (1 / (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ)) *
    (Real.log (rootExtensionHaar T b S).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)

/-- Scaling by a natural power of the rational prime preserves positive finite mass. -/
theorem rootPrimePow_measure_pos (k : ℕ) :
    0 < rootExtensionHaar T b
      (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) •
        rootExtensionUnitBall T b) := by
  induction k with
  | zero => simpa using rootExtensionUnitBall_measure_pos T b
  | succ k ih =>
      have hsmul : ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (k + 1)) •
          rootExtensionUnitBall T b =
          (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
            (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) •
              rootExtensionUnitBall T b) := by
        rw [pow_succ']
        rw [smul_smul]
      rw [hsmul]
      rw [rootPrime_smul_measure (T := T) (b := b)]
      exact ENNReal.mul_pos (by positivity) (ne_of_gt ih)

/-- Scaling by a natural power of the rational prime preserves finite mass. -/
theorem rootPrimePow_measure_lt_top (k : ℕ) :
    rootExtensionHaar T b
      (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) •
        rootExtensionUnitBall T b) < ⊤ := by
  induction k with
  | zero => simpa using rootExtensionUnitBall_measure_lt_top T b
  | succ k ih =>
      have hsmul : ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (k + 1)) •
          rootExtensionUnitBall T b =
          (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
            (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) •
              rootExtensionUnitBall T b) := by
        rw [pow_succ']
        rw [smul_smul]
      rw [hsmul]
      rw [rootPrime_smul_measure (T := T) (b := b)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ih

/-- Iterated prime scaling of the log-Haar mass of the unit ball (Nat powers). -/
theorem log_rootHaar_prime_pow (k : ℕ) :
    Real.log (rootExtensionHaar T b
        (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) •
          rootExtensionUnitBall T b)).toReal =
      -(k : ℝ) *
          (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
          Real.log (qVFamTensorP T b : ℝ) +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
  letI hfin : FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensionalQp (T := T) (b := b)
  letI hns : NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionNormedSpaceQp (T := T) (b := b)
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hsmul : ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ (k + 1)) •
          rootExtensionUnitBall T b =
          (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
            (((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k) •
              rootExtensionUnitBall T b) := by
        rw [pow_succ']
        rw [smul_smul]
      have hstep := LeanFormal.IUT.FinitePadicHaarScaling.log_measure_prime_smul_finiteDimensional
        (p := qVFamTensorP T b) (rootExtensionHaar T b) (S :=
          ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) ^ k •
            rootExtensionUnitBall T b))
        (rootPrimePow_measure_pos (T := T) (b := b) k)
        (rootPrimePow_measure_lt_top (T := T) (b := b) k)
      rw [hsmul]
      rw [hstep]
      rw [ih]
      push_cast
      ring

#print axioms rootPrimePow_measure_pos
#print axioms rootPrimePow_measure_lt_top
#print axioms rootUnitBall_smul_of_norm_one
#print axioms log_rootHaar_prime_pow

end LeanFormal.IUT.XiFPaper.Mzk1URRootMassOnePlaceActual
end