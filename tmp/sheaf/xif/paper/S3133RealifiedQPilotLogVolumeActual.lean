import tmp.sheaf.xif.paper.S3133RealifiedQPilotDivisorActual
import tmp.sheaf.xif.paper.QPilotClassicalLogActual

/-!
# The actual realified q-pilot log-volume on C^boxplus_mod

Source: IUT III, §3, p. 16 (iut3.txt lines 880-893): the log-volume of the
q-pilot object is -|log q| in R, with |log q| > 0.  IUT III, p. 124
(iut3.txt lines 7601-7606): log(q) = ord_v(q_v) log(p_v) in R.

Using the actual q-pilot arithmetic divisor of S3133RealifiedQPilotDivisorActual
in the actual realified global divisor monoid of C^boxplus_mod, this file
constructs its log-volume (minus the realified arithmetic degree) and proves:

* it equals - sum_b mult_b * log(residueNormBase b), the paper's weighted form;
* it equals the actual q-pilot global log-volume qPilotQGlobalLogVolume of the
  same input (presentation-level construction), so the carrier-level divisor and
  the presentation-level log-volume are the same q_v input data;
* it equals - sum_b |log q_v(b)|, i.e. the paper's -|log q|;
* the signed form equals the sum of the actual signed q_v logarithms;
* the per-bad-place contribution is - mult_b * log(residueNormBase b).

No inequality is asserted.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalDivisorOnCarrier
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotClassicalLogActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotDivisorActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual realified q-pilot log-volume: minus the realified arithmetic degree
of the q-pilot divisor. -/
noncomputable def qPilotRealifiedLogVolume
    [Fintype (Bad (nativePlaceSelection X.S))] : Real :=
  -((globalDegree (X := X) (qPilotRealifiedDivisor X)).toAdd)

/-- The actual effective divisor degree of the q_v zero-locus divisor is the
weighted sum of the q_v multiplicities. -/
theorem effectiveDivisorDegree_qVZeroLocusQEffectiveGlobal_eq_sum
    [Fintype (Bad (nativePlaceSelection X.S))] :
    effectiveDivisorDegree X (qVZeroLocusQEffectiveGlobal X) =
      ∑ b : Bad (nativePlaceSelection X.S),
        (qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1) := by
  unfold qVZeroLocusQEffectiveGlobal
  rw [effectiveDivisorDegree_finset_sum X (Finset.univ) (qVZeroLocusQEffectiveDivisor X)]
  exact Finset.sum_congr rfl
    (fun b _ => effectiveDivisorDegree_qVZeroLocusQEffectiveDivisor X b)

/-- The realified q-pilot log-volume in the paper's weighted form. -/
theorem qPilotRealifiedLogVolume_eq
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotRealifiedLogVolume X =
      -∑ b : Bad (nativePlaceSelection X.S),
        (qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1) := by
  unfold qPilotRealifiedLogVolume
  rw [globalDegree_qPilotRealifiedDivisor]
  simp only [toAdd_ofAdd]
  exact congrArg Neg.neg (Finset.sum_congr rfl
    (fun b _ => congrArg _ (globalPrimeWeight_finite_eq X b)))

/-- The realified q-pilot log-volume is exactly the actual q-pilot global
log-volume of the same input. -/
theorem qPilotRealifiedLogVolume_eq_qPilotQGlobalLogVolume
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotRealifiedLogVolume X = qPilotQGlobalLogVolume X := by
  have hdeg := effectiveDivisorDegree_qVZeroLocusQEffectiveGlobal_eq_sum X
  unfold qPilotRealifiedLogVolume qPilotQGlobalLogVolume
  rw [globalDegree_qPilotRealifiedDivisor, hdeg]
  simp only [toAdd_ofAdd]
  exact congrArg Neg.neg (Finset.sum_congr rfl
    (fun b _ => congrArg _ (globalPrimeWeight_finite_eq X b)))

/-- The actual realified q-pilot log-volume is - sum_b |log q_v(b)|: the paper's
-|log q| read off the actual q_v family. -/
theorem qPilotRealifiedLogVolume_eq_neg_sum_localLogMagnitude
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotRealifiedLogVolume X =
      -∑ b : Bad (nativePlaceSelection X.S),
        localLogMagnitude (qVFamily X.S b) := by
  rw [qPilotRealifiedLogVolume_eq_qPilotQGlobalLogVolume X,
    qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude]

/-- The signed form: the realified q-pilot log-volume is the sum of the actual
signed q_v logarithms. -/
theorem qPilotRealifiedLogVolume_eq_sum_localSignedLog
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotRealifiedLogVolume X =
      ∑ b : Bad (nativePlaceSelection X.S),
        localSignedLog (qVFamily X.S b) := by
  rw [qPilotRealifiedLogVolume_eq_neg_sum_localLogMagnitude X,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl
    (fun b _ => (localSignedLog_eq_neg_magnitude (qVFamily X.S b)).symm)

/-- The per-factor log-volume: the contribution of one bad place to the realified
q-pilot log-volume is - mult_b * log(residueNormBase b). -/
theorem realifiedLogVolume_factor_eq
    (b : Bad (nativePlaceSelection X.S)) :
    -((globalDegree (X := X)
        ((qVZeroLocusPrimeDivisor X b) ^ (qVEffectiveMultiplicity X b))).toAdd) =
      -((qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1)) := by
  rw [qPilotRealifiedDivisor_factor X b, globalDegree_primeDivisor_pow,
    globalPrimeWeight_finite_eq]
  simp only [toAdd_ofAdd]

end LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
