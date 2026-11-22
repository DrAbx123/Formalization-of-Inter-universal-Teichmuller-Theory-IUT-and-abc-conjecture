import tmp.sheaf.xif.paper.S3135F5ActualReductionActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import tmp.sheaf.xif.paper.S3135LogShellValueGroupActual

noncomputable section
open scoped BigOperators ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual

namespace LeanFormal.IUT.XiFPaper.Node09S3135CardUActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : ℕ → ℕ → ℕ → I.ThetaPilotPoint v)

/-- Card U is unconditional: the unit-region degree bound is absorbed by any
nonnegative constant, so no hull comparison is needed at all.  This corrects the
earlier reading of card U as a paper-level residual. -/
theorem s3135_actualUnitHullCard_holds :
    S3135ActualUnitHullCard I v R n D := by
  refine ⟨max D.degreeBound 0, le_max_right _ _, ?_⟩
  calc ENNReal.ofReal D.degreeBound
      ≤ ENNReal.ofReal (max D.degreeBound 0) :=
        ENNReal.ofReal_le_ofReal (le_max_left _ _)
    _ ≤ I.sourceHullVolume v R n + ENNReal.ofReal (max D.degreeBound 0) :=
        le_add_left le_rfl

/-- F5 at the actual carrier from the point-weight card alone. -/
theorem s3135_actualFrontierRegionClause_of_pointWeightCard
    (hP : S3135ActualPointWeightCard I v R n D p) :
    FrontierRegionComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ a b c => p a b c) :=
  s3135_actualFrontierRegionClause_of_cards I v R n D p
    (s3135_actualUnitHullCard_holds I v R n D) hP

/-- Exact status of the S3135 F4 cards. -/
def Node09S3135CardStatus : List String :=
  [ "Card U (S3135ActualUnitHullCard): DISCHARGED unconditionally here; choose D0 = max D.degreeBound 0; ofReal degreeBound <= ofReal D0 <= hull + ofReal D0. No hull finiteness needed",
    "F5 at the actual carrier therefore reduces to Card P (S3135ActualPointWeightCard) alone plus the unconditional hsplit/hptfin; Card P is exactly the frozen hpoint input",
    "S3135ScalingLogDegreeZero: carrier gives only sourceLocalLogDegree v D.scaling <= 0; the missing datum is equality to 0, equivalently the normalized-scaling family S3135ScalingNormalization for every eps > 0 (s3135_normalization_family_iff_scalingLogDegreeZero, existing)",
    "S3135PointLogShellFaithfulness: exact missing card; full value-group faithfulness S3135ValueGroupDegreeFaithfulness implies it (s3135_pointFaithfulness_of_valueGroupFaithfulness), but only the cyclic log-q faithfulness (logDegreeAt_posRealAction_nsmul_log_q) is proved",
    "no fake; Card P and the two F4 cards remain the exact paper-level inputs" ]

end LeanFormal.IUT.XiFPaper.Node09S3135CardUActual
