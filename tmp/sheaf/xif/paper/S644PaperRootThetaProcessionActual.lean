import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import tmp.sheaf.xif.paper.S638PaperThetaNormalizationActual
import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual

/-! # S644: paper-root-normalized theta processions

Replaces the old realThetaValue q^(j^2) comparison path by the actual paper
root coefficients:
  paperThetaCoefficient T b j = j^2 * order(q_v)/(2l),
  qVFamPaperThetaValueRoot T b j = hodgeTwoLthRoot^(j^2).
The actual paper signed log magnitude is the paper coefficient times log p.
No inequality is asserted; the comparison is a conditional proposition. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S644PaperRootThetaProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.S638PaperThetaNormalizationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual paper theta log magnitude: paperThetaCoefficient * log p. -/
noncomputable def paperThetaLogMagnitude
    (j : SignedLabel l.value) : Real :=
  paperThetaCoefficient (l := l) T b j *
    Real.log (qVFamTensorP T b : Real)

/-- Signed paper theta value (negative of the log magnitude). -/
noncomputable def paperThetaSignedLogValue
    (j : SignedLabel l.value) : Real :=
  - paperThetaLogMagnitude (l := l) T b j

/-- Actual paper-root-normalized signed procession. -/
noncomputable def paperThetaSignedProcession :
    WeightedValues (SignedLabel l.value) where
  value j := paperThetaSignedLogValue (l := l) T b j
  weight _ := (Fintype.card (SignedLabel l.value) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (mul_inv_cancel₀ hcard).symm

/-- The paper signed procession average. -/
noncomputable def paperThetaSignedAverage : Real :=
  (paperThetaSignedProcession (l := l) T b).average

/-- Paper-root-normalized finite hull. -/
noncomputable def paperThetaSignedFiniteHull :
    FiniteHull (SignedLabel l.value) where
  volume j := paperThetaSignedLogValue (l := l) T b j
  hullVolume := Finset.sum Finset.univ
    (fun j : SignedLabel l.value => |paperThetaSignedLogValue (l := l) T b j|)
  contains j := by
    calc
      paperThetaSignedLogValue (l := l) T b j ≤
          |paperThetaSignedLogValue (l := l) T b j| := le_abs_self _
      _ ≤ Finset.sum Finset.univ
            (fun i : SignedLabel l.value =>
              |paperThetaSignedLogValue (l := l) T b i|) :=
        Finset.single_le_sum
          (fun i _ => abs_nonneg _)
          (Finset.mem_univ j)

/-- Exact comparison proposition for the paper-normalized theta side.  This is
the q-pilot lower bound on the paper root theta average; it is not asserted. -/
def PaperRootThetaComparison (qPilotLogVolume : Real) : Prop :=
  qPilotLogVolume ≤ - paperThetaSignedAverage (l := l) T b

/-- Conditional comparison package. -/
structure PaperRootThetaComparisonData where
  qPilotLogVolume : Real
  comparison : PaperRootThetaComparison (l := l) T b qPilotLogVolume

/-- The paper coefficient is the actual root normalization; the classical
coefficient is 2l times it. -/
theorem paperThetaCoefficient_eq_root_normalization
    (j : SignedLabel l.value) :
    qVFamThetaTensorCoefficient T b j () =
      (2 * l.value : Real) * paperThetaCoefficient (l := l) T b j :=
  classicalThetaCoefficient_is_twoL_times_paper (l := l) T b j

/-- The paper root theta value is the actual root power. -/
theorem paperThetaValueRoot_eq_root_power
    (j : SignedLabel l.value) :
    qVFamPaperThetaValueRoot T b j =
      (hodgeTwoLthRoot (l := l) T b) ^ (gaussExponent j.1).toNat :=
  paperThetaValueRoot_eq_actual_root_power (l := l) T b j

end LeanFormal.IUT.XiFPaper.S644PaperRootThetaProcessionActual

end
