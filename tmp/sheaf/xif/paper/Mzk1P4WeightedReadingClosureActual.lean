/- P4 weighted-reading closure: integrate the actual J_q lattice index/log
with the S3133 scalar, the product-q volume proof, LocalHaar/DistribChar finals,
and the weighted-readout proof.  No new hypotheses, no fake. -/
import tmp.sheaf.xif.paper.Mzk1P4JqLatticeActual
import tmp.sheaf.xif.paper.Mzk1P4ProductQVolumeProofActual
import tmp.sheaf.xif.paper.Mzk1P4WeightedReadoutProofActual
import tmp.sheaf.xif.paper.Mzk1P4LocalHaarRatioFinalActual
import tmp.sheaf.xif.paper.Mzk1P4DistribCharUnitFinalActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Mzk1P4JqLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P4ProductQVolumeProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadoutProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P4LocalHaarRatioFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1P4DistribCharUnitFinalActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadingClosureActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- J_q index log is the negative of the weight-1 bad-side readout. -/
theorem log_jqIndex_eq_neg_weightedReadout :
    Real.log (jqIndex (X := X) : Real) =
      -weightedReadout X (fun _ => 1) := by
  rw [log_jqIndex_eq_qPilotRealifiedLogVolume (X := X),
    weightedReadout_one_eq_logVolume (X := X)]

/-- The P4 product-q log-volume is the negative of the actual J_q index log. -/
theorem productQLogVolume_eq_neg_log_jqIndex :
    productQLogVolume X = -Real.log (jqIndex (X := X) : Real) := by
  rw [productQLogVolume, log_jqIndex_eq_qPilotRealifiedLogVolume (X := X)]
  ring

/-- The product-q log-volume is also the sum of the actual local Haar ratio
logs; this is the LocalHaar-side reading. -/
theorem productQLogVolume_eq_sum_log_localHaarRatio_closure :
    productQLogVolume X =
      ∑ b : Bad (nativePlaceSelection X.S), Real.log (localHaarRatio X b) :=
  productQLogVolume_eq_sum_log_localHaarRatio X


/-- Route §9.2 repeated-factor weights: a constant weight c on every bad
factor scales the J_q index log and the bad-side readout with the expected
sign.  This is the only weight form required by the P4 route (general
place-dependent w_b is not needed). -/
theorem log_jqIndex_mul_eq_neg_weightedReadout_repeated (c : Real) :
    c * Real.log (jqIndex (X := X) : Real) =
      -weightedReadout X (fun _ => c) := by
  rw [log_jqIndex_eq_qPilotRealifiedLogVolume (X := X),
    weightedReadout_repeated_factor_eq_logVolume (X := X)]
  ring

/-- Integrated P4 weighted-reading closure: the actual J_q index log, the
S3133 scalar, the product-q log-volume, and the weight-1 bad readout all agree
with the expected signs. -/
theorem p4_weightedReading_closed :
    Real.log (jqIndex (X := X) : Real) =
        -weightedReadout X (fun _ => 1) ∧
      productQLogVolume X = -Real.log (jqIndex (X := X) : Real) ∧
      productQLogVolume X =
        ∑ b : Bad (nativePlaceSelection X.S), Real.log (localHaarRatio X b) :=
  ⟨log_jqIndex_eq_neg_weightedReadout X,
    productQLogVolume_eq_neg_log_jqIndex X,
    productQLogVolume_eq_sum_log_localHaarRatio_closure X⟩

#print axioms log_jqIndex_eq_neg_weightedReadout
#print axioms productQLogVolume_eq_neg_log_jqIndex
#print axioms productQLogVolume_eq_sum_log_localHaarRatio_closure
#print axioms p4_weightedReading_closed
#print axioms log_jqIndex_mul_eq_neg_weightedReadout_repeated

end LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadingClosureActual
end
