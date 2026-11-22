import tmp.sheaf.xif.paper.S3135FinalAssemblyGateV2Actual
import tmp.sheaf.xif.paper.S3135ValueGroupDegreeUnconditionalActual

/-!
# FINAL ASSEMBLY GATE v3 (task-47)

**COMPONENT / gate, not a paper object.**  v3 uses the unconditional value-group action
(`S3135ValueGroupDegreeUnconditionalActual`, no weight hypothesis) and keeps the one
final conditional theorem of gate v2:

`s3135_finalAssemblyGateV3`: [S3135PointLogShellFaithfulness +
S3135ScalingLogDegreeZero + S3135ActualPointWeightCard (card P)] => ABCConjecture;
tightness `s3135_finalAssemblyGateV3_tight` (card P <=> ABCConjecture under the two
F4 cards).  Imports re-verified green (EXIT=0 + source paths present):
S3135FinalAssemblyGateV2Actual, S3135ValueGroupDegreeUnconditionalActual,
and transitively S3135FinalAssemblyGateActual, S3135TightnessActual,
S3135ValueGroupIdentificationActual, S3135F5ActualReductionActual,
S3135EndToEndV2Actual, mainline S3131CanonicalRootedQCActual, shehdd
S3134FourthTriangleCompositionStatusActual / S3134MainlineRootedHFaActual, hull
S3132QThetaConsumerWiringActual.

Residual delta vs gate v2: NONE in the conditional residual set; only the value-group
action provenance strengthened (now unconditional actual; qpilot
S3133GlobalPrimeWeightActual).  Updated residual list: (a) S3135ValueMonoidIdentification
(owner abc); (b) S3135AdditiveHaarModulusLaw + paper lambda log-degree 0 (owner abc);
(c) hull Theta-half C3-packet uniform comparison + normalization (owner hull);
(d) card P = ABC-strength.
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
open LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual
open LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual
open LeanFormal.IUT.XiFPaper.S3135TightnessActual
open LeanFormal.IUT.XiFPaper.S3135FinalResidualActual
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV2Actual

namespace LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual

/-- Final assembly gate v3 (same residual set; unconditional value-group action). -/
theorem s3135_finalAssemblyGateV3
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀)
    (hP : S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀)) :
    ABCConjecture :=
  s3135_finalAssemblyGateV2 I₀ v₀ R₀ n₀ D₀ hpt hzero hP

/-- Tightness of gate v3. -/
theorem s3135_finalAssemblyGateV3_tight
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀) :
    S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀) ↔
      ABCConjecture :=
  s3135_finalAssemblyGateV2_tight I₀ v₀ R₀ n₀ D₀ hpt hzero

/-- Gate v3 residual ledger (delta vs v2: none in the conditional set). -/
def s3135FinalAssemblyGateV3Report : Audit.Obligation :=
  { id := "IUT-IV.abc-final-assembly-gate-v3"
    source :=
      "IUT II section 1; IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] " ++
        "Proposition 5.8(ii); IUT III Remark 3.9.4; IUT III Proposition 3.9(i) " ++
        "p.115; IUT III Remark 3.9.5(i) pp.158-159; IUT III Cor 3.12 " ++
        ":10324-10353; IUT IV Theorem 1.10 :1255-1385; IUT IV section 1 " ++
        "Proposition 1.4 iut4.txt:671-760; IUT IV section 2 :2329-2340; [GenEll] " ++
        "Definition 1.5; IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "GATE v3: s3135_finalAssemblyGateV3 and tightness " ++
        "s3135_finalAssemblyGateV3_tight; value-group action provenance upgraded to " ++
        "unconditional actual (S3135ValueGroupDegreeUnconditionalActual, qpilot " ++
        "S3133GlobalPrimeWeightActual).  Residual delta: none.  Residuals: (a) " ++
        "S3135ValueMonoidIdentification (abc); (b) S3135AdditiveHaarModulusLaw + " ++
        "paper lambda log-degree 0 (abc); (c) hull Theta-half C3-packet uniform " ++
        "comparison + normalization (hull); (d) card P = ABC-strength.  Handoffs: " ++
        "mainline S3131CanonicalRootedQCActual (Q_C numeric via S778 gap only); " ++
        "shehdd S3134FourthTriangleCompositionStatusActual/S3134MainlineRootedHFaActual; " ++
        "hull S3132QThetaConsumerWiringActual/S3132Task30ThetaHalfActual."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135ValueMonoidIdentification (F4 (a))",
        "S3135AdditiveHaarModulusLaw + paper lambda log-degree 0 (F4 (b))",
        "Theta-half C3-packet uniform comparison + normalization (hull)",
        "ABCHeightWeightAdditiveBoundV2 (F5 card P, ABC-strength)" ] }

#check s3135_finalAssemblyGateV3
#check s3135_finalAssemblyGateV3_tight
#check s3135FinalAssemblyGateV3Report

end LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual
end
