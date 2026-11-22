import tmp.sheaf.xif.paper.S3135F4ActualHullResidualActual
import tmp.sheaf.xif.paper.S3135ActualF4LogShellDegreeActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual

noncomputable section

open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual

namespace LeanFormal.IUT.XiFPaper.S3135ProcessionDatumActual

/-- **Corpus sub-lemma datum (B), III Remark 3.9.5(i)**: the procession scaling
`lambda` (the `lambda` of the holomorphic hull `H = lambda·O`) is a nonzero unit, hence
has log-degree ZERO in particular NONNEGATIVE.  The frozen `SourceUnitRegionHaarData`
records only the nonpositive direction (`scaling_logDegree_nonpos`); this datum is the
missing elementary half, supplied by the corpus' hull decomposition with nonzero unit
components.  Formalizing the component-level unit statement requires the hull
decomposition API (III Rem 3.9.5(i)) which the frozen structure does not record, so it
is kept as this explicit datum (class B: elementary formalization / contract data). -/
structure S3135ProcessionScalingUnitDatum
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) : Prop where
  /-- Nonnegativity of the scaling log-degree (nonzero unit: log = 0). -/
  scaling_logDegree_nonneg : 0 ≤ I.sourceLocalLogDegree v D.scaling

/-- The corpus datum plus the record's nonpositive direction yields the F4 (b)
scaling card (equality by antisymmetry): no new paper input, only the elementary
unit-log-zero observation recorded as data. -/
theorem s3135_procession_scaling_unit_degree_zero
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hd : S3135ProcessionScalingUnitDatum I v R n D) :
    S3135ScalingLogDegreeZero I v R n D :=
  le_antisymm D.scaling_logDegree_nonpos hd.scaling_logDegree_nonneg

#check S3135ProcessionScalingUnitDatum
#check s3135_procession_scaling_unit_degree_zero
end LeanFormal.IUT.XiFPaper.S3135ProcessionDatumActual
end
