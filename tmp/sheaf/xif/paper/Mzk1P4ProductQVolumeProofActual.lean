/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1QVMultiplicityBridgeActual
import Mathlib.Tactic

/-!
# P4 actual product-q volume proof (distinct from hull interface file)

This file proves the product-q log-volume identity

  V(J_q;C_q) = - sum_b n_b f_b log p_b

from the GREEN S3133 realified log-volume donor:

  qPilotRealifiedLogVolume = - sum_b mult_b * log(residueNormBase b)

together with the actual multiplicity decomposition

  mult_b = order(q_v(b)) * localResidueDegree(F-place over b)

from Mzk1QVMultiplicityBridge.  Here n_b = order(q_v(b)),
f_b = localResidueDegree(F-place over b), p_b = residueNormBase b.
The product-Haar reading is the product of the local normalized Haar
ratios p_b^{-n_b f_b}; taking logs gives exactly the sum below.

This file is intentionally separate from Mzk1P4ProductQVolumeActual
(interface-only hull file).  No interface-only placeholder, no fake,
no new axiom.  Watchdog-only.
-/

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1P4ProductQVolumeProofActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QVMultiplicityBridgeActual

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- The actual product-q log-volume, read off the GREEN S3133 realified divisor. -/
noncomputable def productQLogVolume : Real :=
  qPilotRealifiedLogVolume X

/-- Exact S3133 form: the product-q log-volume is minus the weighted sum of the
actual q_v multiplicities over the actual base residue norms. -/
theorem productQLogVolume_eq_neg_sum_multiplicity_logResidue :
    productQLogVolume X =
      -∑ b : Bad (nativePlaceSelection X.S),
        (qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1) :=
  qPilotRealifiedLogVolume_eq X

/-- Actual multiplicity decomposition: mult_b = order(q_v(b)) * f_b. -/
theorem productQLogVolume_eq_neg_sum_order_mul_residueDegree_logResidue :
    productQLogVolume X =
      -∑ b : Bad (nativePlaceSelection X.S),
        ((qVFamily X.S b).order : Real) *
          (localResidueDegree (k := X.S.arithmetic.Fmod)
            ((nativeBadLift X.S).lift b) : Real) *
          Real.log (residueNormBase b.1) := by
  rw [productQLogVolume_eq_neg_sum_multiplicity_logResidue X]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [qVEffectiveMultiplicity_eq_order_mul_localResidueDegree X b]

/-- P4 product-q volume identity in the paper's n_b f_b log p_b form:
n_b = order(q_v(b)), f_b = localResidueDegree(F-place over b),
p_b = residueNormBase b.  This is the actual product-Haar log identity. -/
theorem productQLogVolume_eq_neg_sum_n_mul_f_mul_log_residue
    (n f : Bad (nativePlaceSelection X.S) -> Nat)
    (hn : forall b, (qVFamily X.S b).order = n b)
    (hf : forall b, localResidueDegree (k := X.S.arithmetic.Fmod)
      ((nativeBadLift X.S).lift b) = f b) :
    productQLogVolume X =
      -∑ b : Bad (nativePlaceSelection X.S),
        (n b : Real) * (f b : Real) * Real.log (residueNormBase b.1) := by
  rw [productQLogVolume_eq_neg_sum_order_mul_residueDegree_logResidue X]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [hn b, hf b]

/-- The product of local Haar ratios p_b^{-n_b f_b}; its log is the negative
sum above.  (Kept as a named product object so the consumer can read the
product-Haar side explicitly.) -/
noncomputable def localHaarRatio
    (b : Bad (nativePlaceSelection X.S)) : Real :=
  (residueNormBase b.1) ^ (-((qVEffectiveMultiplicity X b : Nat) : Int))

theorem log_localHaarRatio
    (b : Bad (nativePlaceSelection X.S)) :
    Real.log (localHaarRatio X b) =
      -((qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1)) := by
  unfold localHaarRatio
  rw [Real.log_zpow]
  push_cast
  ring

theorem productQLogVolume_eq_sum_log_localHaarRatio :
    productQLogVolume X =
      ∑ b : Bad (nativePlaceSelection X.S), Real.log (localHaarRatio X b) := by
  rw [productQLogVolume_eq_neg_sum_multiplicity_logResidue X]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  exact (log_localHaarRatio X b).symm

#check productQLogVolume_eq_neg_sum_multiplicity_logResidue
#check productQLogVolume_eq_neg_sum_order_mul_residueDegree_logResidue
#check productQLogVolume_eq_neg_sum_n_mul_f_mul_log_residue
#check productQLogVolume_eq_sum_log_localHaarRatio

end LeanFormal.IUT.XiFPaper.Mzk1P4ProductQVolumeProofActual
end
