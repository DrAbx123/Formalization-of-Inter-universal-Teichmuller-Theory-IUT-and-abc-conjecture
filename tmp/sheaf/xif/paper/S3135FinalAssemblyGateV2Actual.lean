import tmp.sheaf.xif.paper.S3135FinalAssemblyGateActual
import tmp.sheaf.xif.paper.S3135ValueGroupDegreeUnconditionalActual
import tmp.sheaf.xif.paper.S3133GlobalPrimeWeightActual

/-!
# FINAL ASSEMBLY GATE v2 (task-44): unconditional value-group action, updated residual ledger

**COMPONENT / gate, not a paper object.**  This updates the task-42 final assembly
gate after task-44:

* the actual Real-indexed degree-faithful monoid action on the actual realified
  divisor group is now **unconditional** (no nonzero-weight hypothesis):
  `S3135ValueGroupDegreeUnconditionalActual.normalizedRealifiedPrimePowerHom_degree`,
  using qpilot's citable `S3133GlobalPrimeWeightActual.globalPrimeWeight_ne_zero`;
* the gate's one final conditional theorem is unchanged:
  `s3135_finalAssemblyGate`: [S3135PointLogShellFaithfulness +
  S3135ScalingLogDegreeZero + S3135ActualPointWeightCard (card P)] =>
  `ABCConjecture`, with tightness `s3135_finalAssemblyGate_tight`
  (card P <=> ABCConjecture under the two F4 cards);
* all gate imports verified currently green (EXIT=0) and present: abc
  S3135TightnessActual / S3135ValueGroupIdentificationActual /
  S3135F5ActualReductionActual / S3135EndToEndV2Actual / S3135FinalAssemblyGateActual;
  mainline S3131CanonicalRootedQCActual; shehdd
  S3134FourthTriangleCompositionStatusActual / S3134MainlineRootedHFaActual; hull
  S3132QThetaConsumerWiringActual (the separate S3132Task30ThetaHalfActual is being
  recompiled by hull and is a handoff, not a gate input).

## Updated minimal residual set

(a) `S3135PointLogShellFaithfulness`: now reduced to the SINGLE structure
    `S3135ValueMonoidIdentification` (degree-commuting psi from the actual realified
    divisor group to the source value monoid, agreeing with `R.posRealAction`); the
    value-group action itself is ACTUAL and unconditional.  Owner: abc (next:
    qpilot/mainline confirm or construct the source-monoid identification).  Refs:
    IUT II section 1; IUT II Ex 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] Prop 5.8(ii);
    IUT III Rem 3.9.4.
(b) `S3135ScalingLogDegreeZero`: additive-Haar modulus law
    `mu(c*S) = ofReal ||c|| * mu(S)` on the actual `concreteLogShellField` (hull's
    sourceHullHaar, addHaar on integralLogShell, unit-reference mass 1) via Mathlib
    `Measure.addHaarScalarFactor` / Haar uniqueness, plus the paper lambda in the
    source scaling units with log-degree 0 and procession normalization.
    Owner: abc (Lead-assigned; hull declined duplication).  Refs: IUT III Prop
    3.9(i) p.115; Rem 3.9.5(i) pp.158-159; Cor 3.12:10324-10353.
(c) Theta-half C3-packet uniform comparison + normalization.  Owner: hull (handoff
    S3132Task30ThetaHalfActual / S3132QThetaConsumerWiringActual); independent of the
    F4/F5 => ABC implication of the gate.
(d) `ABCHeightWeightAdditiveBoundV2` = F5 card P: exactly ABC-strength by tightness
    (IUT IV Theorem A / [GenEll]; IV section 2:2329-2340; Def 1.5; IV:2367-2375).
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

namespace LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV2Actual

/-- **Final assembly gate v2** (same residual set; value-group action now
unconditional on the realified side). -/
theorem s3135_finalAssemblyGateV2
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀)
    (hP : S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀)) :
    ABCConjecture :=
  s3135_finalAssemblyGate I₀ v₀ R₀ n₀ D₀ hpt hzero hP

/-- Tightness of the v2 gate (unchanged). -/
theorem s3135_finalAssemblyGateV2_tight
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀) :
    S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀) ↔
      ABCConjecture :=
  s3135_finalAssemblyGate_tight I₀ v₀ R₀ n₀ D₀ hpt hzero

/-- Updated residual ledger for the v2 gate. -/
def s3135FinalAssemblyGateV2Report : Audit.Obligation :=
  { id := "IUT-IV.abc-final-assembly-gate-v2"
    source :=
      "IUT II section 1; IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] " ++
        "Proposition 5.8(ii); IUT III Remark 3.9.4; IUT III Proposition 3.9(i) " ++
        "p.115; IUT III Remark 3.9.5(i) pp.158-159; IUT III Cor 3.12 " ++
        ":10324-10353; IUT IV Theorem 1.10 :1255-1385; IUT IV section 1 " ++
        "Proposition 1.4 iut4.txt:671-760; IUT IV section 2 :2329-2340; [GenEll] " ++
        "Definition 1.5; IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "GATE v2: s3135_finalAssemblyGateV2 ([S3135PointLogShellFaithfulness + " ++
        "S3135ScalingLogDegreeZero + card P] => ABCConjecture) and tightness " ++
        "s3135_finalAssemblyGateV2_tight.  Value-group action on the actual " ++
        "realified divisor group is now UNCONDITIONAL " ++
        "(normalizedRealifiedPrimePowerHom_degree, qpilot " ++
        "globalPrimeWeight_ne_zero).  Residuals: (a) S3135ValueMonoidIdentification " ++
        "(owner abc; reduced to one degree-commuting source-monoid hom); " ++
        "(b) additive-Haar modulus + paper lambda log-degree 0/procession " ++
        "normalization (owner abc; exact statement and Mathlib plan recorded); " ++
        "(c) hull Theta-half C3-packet uniform comparison + normalization (owner " ++
        "hull; handoff); (d) ABCHeightWeightAdditiveBoundV2/card P (exactly " ++
        "ABC-strength).  All gate imports verified EXIT=0 and present; handoffs: " ++
        "mainline S3131CanonicalRootedQCActual (numeric Q_C via S778 gap only), " ++
        "shehdd S3134FourthTriangleCompositionStatusActual/S3134MainlineRootedHFaActual, " ++
        "hull S3132QThetaConsumerWiringActual + S3132Task30ThetaHalfActual (recompiling)."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135ValueMonoidIdentification (F4 (a) source-monoid identification)",
        "S3135AdditiveHaarModulusLaw + paper lambda log-degree 0 (F4 (b))",
        "Theta-half C3-packet uniform comparison + normalization (hull)",
        "ABCHeightWeightAdditiveBoundV2 (F5 card P, ABC-strength)" ] }

#check s3135_finalAssemblyGateV2
#check s3135_finalAssemblyGateV2_tight
#check s3135FinalAssemblyGateV2Report

end LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV2Actual
end
