import tmp.sheaf.xif.paper.S3135LogShellValueGroupActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import tmp.sheaf.xif.paper.S3135ActualF4LogShellDegreeActual
open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
namespace LeanFormal.IUT.XiFPaper.S3135ModelF4aBatchActual

/-- **F4.a model obligation in one equation**: if the model realization's log-degree
reads `toAdd` on the generator action, the realization is degree-faithful. -/
theorem s3135_valueGroupFaithfulness_of_realizationLogDegree
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v)
    (hlog : ∀ r : Multiplicative ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction r) = Multiplicative.toAdd r) :
    S3135ValueGroupDegreeFaithfulness I v R :=
  fun x => hlog (Multiplicative.ofAdd x)

/-- F4 card (1) reduced form from the single realization log-degree equation. -/
theorem s3135_pointFaithfulness_of_realizationLogDegree
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v)
    (hlog : ∀ r : Multiplicative ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction r) = Multiplicative.toAdd r) :
    S3135PointLogShellFaithfulness I v R :=
  s3135_pointFaithfulness_of_valueGroupFaithfulness I v R
    (s3135_valueGroupFaithfulness_of_realizationLogDegree I v R hlog)

/-- The actual F4 height clause from the single log-degree equation plus the
scaling-zero card. -/
theorem s3135_actualF4_of_realizationLogDegree
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hlog : ∀ r : Multiplicative ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction r) = Multiplicative.toAdd r)
    (hzero : S3135ScalingLogDegreeZero I v R n D) :
    FrontierHeightComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) := by
  have hpt := s3135_pointFaithfulness_of_realizationLogDegree I v R hlog
  have hnorm : ∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps :=
    s3135_normalization_of_scalingLogDegreeZero I v R n D hzero
  exact s3135_actualF4_of_pointFaithfulness I v R n D hpt hnorm

#check s3135_valueGroupFaithfulness_of_realizationLogDegree
#check s3135_pointFaithfulness_of_realizationLogDegree
#check s3135_actualF4_of_realizationLogDegree
end LeanFormal.IUT.XiFPaper.S3135ModelF4aBatchActual