import tmp.sheaf.xif.paper.Mzk1ActualReadingTargetActual
import tmp.sheaf.xif.paper.Mzk1ActualHullTargetMagnitudeActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1ActualReadingTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6HThetaUpperSandwichActual
universe u v
/-- Independent P6 upper bound for H_theta in the paper `M = Q/(2l)` sandwich. -/
noncomputable def p6HThetaUpperSandwich {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (A cl Q : Real) : Prop :=
  actualThetaHullLogRoot (l := l) T ≤
    ((l.value : Real) + 1) / 4 * (A - cl * Q) -
      actualQPilotMagnitudeClassical (l := l) T
/-- P5 lower half: `-M <= H_theta`. -/
theorem p6Sandwich_lower {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [hMeas : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [hBorel : ∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)] :
    -actualQPilotMagnitudeClassical (l := l) T ≤ actualThetaHullLogRoot (l := l) T := by
  simpa [actualQPilotSignedLogClassical] using actualTargetSigned_actual (l := l) T
/-- Combine the independent upper bound with the P5 lower bound and cancel `-M`:
    `c_l*Q <= A`. -/
theorem p6_sandwich_cancel {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [hMeas : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [hBorel : ∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (A cl Q : Real)
    (hU : p6HThetaUpperSandwich (l := l) T A cl Q) :
    cl * Q ≤ A := by
  have hL := p6Sandwich_lower (l := l) T
  unfold p6HThetaUpperSandwich at hU
  have hlpos : (0 : Real) < ((l.value : Real) + 1) / 4 := by
    have : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
    positivity
  have hmain : (0 : Real) ≤ ((l.value : Real) + 1) / 4 * (A - cl * Q) := by
    linarith
  have hdiff : 0 ≤ A - cl * Q := (mul_nonneg_iff_of_pos_left hlpos).mp hmain
  linarith
#print axioms p6_sandwich_cancel
end LeanFormal.IUT.XiFPaper.Mzk1P6HThetaUpperSandwichActual
end