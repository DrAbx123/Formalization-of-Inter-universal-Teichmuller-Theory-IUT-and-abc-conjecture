import tmp.sheaf.xif.paper.Mzk1ActualRamifiedDataActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 2000000
open scoped WithZero
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual

namespace LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

/-- The node09 fiber multiplicity: the qV effective multiplicity (order times
local residue degree) of the bad place b(i). -/
noncomputable def fiberMult
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S)) :
    FinitePlaceAtPrime F p → ℝ :=
  fun i => (qVEffectiveMultiplicity X (b i) : ℝ)

/-- Multiplicity decomposition: order(q_v) times the local residue degree. -/
theorem fiberMult_eq_order_mul_localResidueDegree
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (i : FinitePlaceAtPrime F p) :
    fiberMult X b i =
      ((qVFamily X.S (b i)).order : ℝ) *
        (localResidueDegree (k := X.S.arithmetic.Fmod)
          ((nativeBadLift X.S).lift (b i)) : ℝ) := by
  unfold fiberMult qVEffectiveMultiplicity
  push_cast
  rfl

/-- The actual q_v local log magnitude is the fiber multiplicity times the
base residue norm log. -/
theorem fiberMult_log_eq_localLogMagnitude
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (i : FinitePlaceAtPrime F p) :
    fiberMult X b i * Real.log (residueNormBase (b i).1) =
      localLogMagnitude (qVFamily X.S (b i)) :=
  (qVFamily_localLogMagnitude_eq (X := X) (b := b i)).symm

/-- Per-place bridge: the multiplicity-times-base-residue-norm bound implies the
rational-prime log bound, once the two logs are identified. -/
theorem perPlace_of_fiberMult
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) {logIdx diff : FinitePlaceAtPrime F p → ℝ}
    (hlogp : ∀ i : FinitePlaceAtPrime F p,
      Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) =
        Real.log (residueNormBase (b i).1))
    (h : ∀ i : FinitePlaceAtPrime F p,
      fiberMult X b i / (Fdeg * (2 * l)) *
          Real.log (residueNormBase (b i).1) ≤ logIdx i + diff i) :
    ∀ i : FinitePlaceAtPrime F p,
      fiberMult X b i / (Fdeg * (2 * l)) *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) ≤
        logIdx i + diff i := by
  intro i
  rw [hlogp i]
  exact h i

/-- Node09 hq R1: the mult-weighted A-term with the actual qV fiber
multiplicities, fed into the per-place R1 consumer. -/
theorem actual_A_le_Lbar_add_Dbar_of_fiberMult
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ)
    (hlogp : ∀ i : FinitePlaceAtPrime F p,
      Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) =
        Real.log (residueNormBase (b i).1))
    (h : ∀ i : FinitePlaceAtPrime F p,
      fiberMult X b i / (Fdeg * (2 * l)) *
          Real.log (residueNormBase (b i).1) ≤
        actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i)) :
    (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)) ≤
      ∑ i : FinitePlaceAtPrime F p,
        (actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i)) := by
  apply actual_A_le_Lbar_add_Dbar_mult
    (F := F) (p := p) (Fdeg := Fdeg) (l := l)
    (mult := fun i => fiberMult X b i) (logMu := logMu)
  intro i
  rw [hlogp i]
  exact h i

end LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual
