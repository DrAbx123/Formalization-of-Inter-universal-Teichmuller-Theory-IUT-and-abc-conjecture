import tmp.sheaf.xif.paper.S3135ValueGroupIdentificationActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import tmp.sheaf.xif.paper.S3135LogShellValueGroupActual

/-!
# task-52 batch: F4 height clause from the value-monoid identification + scaling zero

**COMPONENT, not a paper object.**  Consumer: final assembly gate.

Combines the two F4 residuals: the single source-monoid identification
`S3135ValueMonoidIdentification` (task-39) and the paper scaling-zero datum
`S3135ScalingLogDegreeZero` yield the **actual F4 height comparison clause** at the
constructed value-realized point on the actual carrier:
`FrontierHeightComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
 (fun _ _ a b c => abcSourcePoint I v R a b c)`.
This removes the F4 chain from the residual list whenever the identification and the
scaling normalization are supplied (IUT II Example 1.8(ix); [AbsTopIII] Prop 5.8(ii);
IUT III Remark 3.9.4; Remark 3.9.5(i)).
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupIdentificationActual
open LeanFormal.IUT.XiFPaper.S3135ResidualNarrowingActual
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3135F4FromIdentActual

/-- **F4 height clause from the identification + scaling zero.** -/
theorem s3135_actualF4_of_identification
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l')
    (D : I.SourceUnitRegionHaarData v R n)
    (vp : GlobalPrimeIndex (X := X))
    (hweight : globalPrimeWeight (X := X) vp ≠ 0)
    (hid : S3135ValueMonoidIdentification X I v R vp hweight)
    (hzero : S3135ScalingLogDegreeZero I v R n D) :
    FrontierHeightComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) := by
  have hpt : S3135PointLogShellFaithfulness I v R :=
    s3135_pointFaithfulness_of_identification X I v R vp hweight hid
  have hnorm : ∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps :=
    s3135_normalization_of_scalingLogDegreeZero I v R n D hzero
  exact s3135_actualF4_of_pointFaithfulness I v R n D hpt hnorm

#check s3135_actualF4_of_identification

end LeanFormal.IUT.XiFPaper.S3135F4FromIdentActual
end
