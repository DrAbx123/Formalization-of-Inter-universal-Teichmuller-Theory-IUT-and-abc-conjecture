import tmp.sheaf.xif.paper.S2614CompactnessScalingActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import tmp.sheaf.xif.paper.S3135LogShellValueGroupActual
import tmp.sheaf.xif.paper.S3135FinalResidualActual

noncomputable section
open scoped BigOperators ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2614CompactnessScalingActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135FinalResidualActual

namespace LeanFormal.IUT.XiFPaper.Node09S3135F4InvestigationActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The scaling log-degree card is discharged for the normalized compactness
Haar data: its scaling is literally 1, so its log-degree is 0. -/
theorem s3135_scalingLogDegreeZero_compactness
    (C : I.SourceOneCircUCompactness v R n) :
    S3135ScalingLogDegreeZero I v R n (I.sourceOModuleCompactness_haarData v R n C) := by
  unfold S3135ScalingLogDegreeZero
  exact S2614_compactnessScalingLogDegreeZero I v R n C

/-- Exact status record of the F4 cards and Card P. -/
def Node09S3135F4Status : List String :=
  [ "S3135ScalingLogDegreeZero: for the canonical normalized compactness Haar data sourceOModuleCompactness_haarData, scaling = 1 and logDegree = 0 is PROVED (S2614_compactnessScalingLogDegreeZero, re-exported as s3135_scalingLogDegreeZero_compactness). For an arbitrary paper-side D the carrier gives only <= 0; the missing datum is equality to 0, equivalently the normalized-scaling family S3135ScalingNormalization for every eps > 0 (existing iff reduction)",
    "S3135PointLogShellFaithfulness: exact missing card, not proved. Full value-group faithfulness S3135ValueGroupDegreeFaithfulness implies it (s3135_pointFaithfulness_of_valueGroupFaithfulness); only the cyclic log-q faithfulness is proved. S3135FinalResidualActual records that the only constructed value-layer model has its faithfulness refuted, so the card cannot be assumed for an arbitrary realization",
    "Card P: exactly Node09 hpoint (Node09S3135ResidualMapActual.s3135_pointWeightCard_iff_node09HpointFamily); under the two F4 cards it is equivalent to ABCHeightWeightAdditiveBoundV2 (S3135FinalResidualActual.s3135_pointWeightCard_iff_additiveBound), hence ABC-strength. No donor exists",
    "Card U: unconditional (Node09S3135CardUActual / S3135FinalResidualActual.s3135_actualUnitHullCard); F5 reduces to Card P plus actual hsplit/hptfin",
    "F4 cards plus Card P yield ABCConjecture conditionally (S3135FinalResidualActual.s3135_abcConjecture_of_minimalResiduals); no inhabitant and no fake" ]

end LeanFormal.IUT.XiFPaper.Node09S3135F4InvestigationActual
