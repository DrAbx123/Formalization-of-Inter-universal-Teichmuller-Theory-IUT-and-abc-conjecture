import tmp.sheaf.xif.paper.S3135TightnessActual
import tmp.sheaf.xif.paper.S3135ValueGroupIdentificationActual
import tmp.sheaf.xif.paper.S3135F5ActualReductionActual
import tmp.sheaf.xif.paper.S3135EndToEndV2Actual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual
import tmp.sheaf.xif.paper.S3134FourthTriangleCompositionStatusActual
import tmp.sheaf.xif.paper.S3134MainlineRootedHFaActual
import tmp.sheaf.xif.paper.S3132QThetaConsumerWiringActual

/-!
# S3135 FINAL ASSEMBLY GATE

**task-42.**  The single end-to-end final assembly gate of the abc stream, consuming
the final versions of:

* abc: `S3135F4ActualHullResidualActual`, `S3135ActualF4LogShellDegreeActual`,
  `S3135ScalingNormalizationActual`, `S3135LogShellValueGroupActual`,
  `S3135F5ActualReductionActual`, `S3135EndToEndV2Actual`, `S3135TightnessActual`,
  `S3135ValueGroupDegreeActualActual`, `S3135ValueGroupIdentificationActual`
  (transitively imported).
* mainline: `S3131CanonicalRootedQCActual` (canonical rooted Q_C/H_C and the
  unconditional signed comparison; consumed in the chain through
  `S3131PaperNormalizedComparisonActual`); the explicit numeric value of Q_C is
  convention/construction only (`S778 PaperQPilotLogFormulaIdentification` gap,
  ledgered by mainline, not claimed here).
* shehdd: `S3134FourthTriangleCompositionStatusActual`,
  `S3134MainlineRootedHFaActual` (signed 3.11.5=>3.12 leg + reduced same-C
  consumer; consumed through `S3134NativeContractShrinkActual`).
* hull: `S3132QThetaConsumerWiringActual` (C3/Theta-hull consumer wiring);
  `S3132Task30ThetaHalfActual` is being recompiled by hull (olean stale) and is a
  handoff point, not an input of this gate file.

## The one final conditional theorem

`s3135_finalAssemblyGate`: from the **minimal residual set**

1. `S3135PointLogShellFaithfulness` (F4 (a); reduced by task-39 to the single
   identified structure `S3135ValueMonoidIdentification` — a degree-commuting monoid
   hom from the actual realified divisor group to the source value monoid agreeing
   with `R.posRealAction`; actual realified Real-indexed degree action already
   constructed in `S3135ValueGroupDegreeActualActual`);
2. `S3135ScalingLogDegreeZero` (F4 (b); paper lambda log-degree 0 + procession
   normalization — the additive-Haar modulus law is owner: abc per Lead, hull
   declined ownership; exact statement `mu(c*S) = ||c||*mu(S)` on the actual
   `concreteLogShellField` with `sourceHullHaar`, unit-reference mass 1);
3. `S3135ActualPointWeightCard` at the constructed point (F5 card P / (d);
   **exactly ABC-strength** by `s3135_pointWeightCard_iff_abcConjecture`),

one gets `ABCConjecture`, through `ABCFrontier` and the production
`abcConjecture_of_frontier`.  All other chain components are proved/consumed:
F5 card U unconditional, hsplit/hptfin, mainline's paper-normalized
`Q_C <= H_C` (unconditional actual), shehdd's reduced same-C consumer, the actual
Frey/height machinery and IV Theorem 1.10 real-variable bookkeeping.

The residual (c) named by the Lead (Theta-half C3-packet uniform comparison +
normalization) is the hull-stream handoff `S3132Task30ThetaHalfActual` /
`S3132QThetaConsumerWiringActual`; it is not needed for the F4/F5 => ABC
implication of this gate (the Cor 3.12 side enters through mainline's already
unconditional comparison), and is recorded as an independent handoff item.
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
open LeanFormal.IUT.XiFPaper.S3135ResidualNarrowingActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeActualActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupIdentificationActual

namespace LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual

/-- **The final assembly gate theorem**: minimal residual set => `ABCConjecture`. -/
theorem s3135_finalAssemblyGate
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀)
    (hP : S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀)) :
    ABCConjecture :=
  s3135_abcConjecture_of_threeResiduals I₀ v₀ R₀ n₀ D₀ hpt hzero hP

/-- Tightness of the gate: the F5 residual (card P) is equivalent to
`ABCConjecture` under the two F4 cards, so the residual set cannot be weakened in
the F5 slot. -/
theorem s3135_finalAssemblyGate_tight
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀) :
    S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀) ↔
      ABCConjecture :=
  s3135_pointWeightCard_iff_abcConjecture I₀ v₀ R₀ n₀ D₀ hpt hzero

/-- **Residual ledger of the final gate**, each residual with owner, construction
plan and page references. -/
def s3135FinalAssemblyGateReport : Audit.Obligation :=
  { id := "IUT-IV.abc-final-assembly-gate"
    source :=
      "IUT II section 1; IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] " ++
        "Proposition 5.8(ii); IUT III Remark 3.9.4; IUT III Proposition 3.9(i) " ++
        "p.115; IUT III Remark 3.9.5(i) pp.158-159; IUT III Cor 3.12 " ++
        ":10324-10353; IUT IV Theorem 1.10 :1255-1385; IUT IV section 1 " ++
        "Proposition 1.4 iut4.txt:671-760; IUT IV section 2 :2329-2340; [GenEll] " ++
        "Definition 1.5; IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "FINAL GATE RESIDUALS (each with owner / plan / source): " ++
        "(a) S3135PointLogShellFaithfulness -- owner abc; plan: the single " ++
        "identification S3135ValueMonoidIdentification (degree-commuting monoid hom " ++
        "GlobalDivisorMonoid -> source value monoid, agreeing with R.posRealAction); " ++
        "the actual Real-indexed degree-faithful realified action is already " ++
        "constructed (S3135ValueGroupDegreeActualActual); sources IUT II section 1, " ++
        "IUT II Ex 1.8(ix), [AbsTopIII] Prop 5.8(ii), Rem 3.9.4. " ++
        "(b) S3135ScalingLogDegreeZero -- owner abc (Lead assigned the Haar modulus " ++
        "to abc; hull confirmed it will not duplicate); plan: additive-Haar modulus " ++
        "law mu(c*S) = ||c||*mu(S) on the actual concreteLogShellField via Mathlib " ++
        "Measure.addHaarScalarFactor / Haar uniqueness with hull's sourceHullHaar " ++
        "and unit-reference mass 1, plus the paper lambda in the source scaling " ++
        "units with log-degree 0 and procession normalization; sources III Prop " ++
        "3.9(i) p.115, Rem 3.9.5(i) pp.158-159, Cor 3.12. " ++
        "(c) Theta-half C3-packet uniform comparison + normalization -- owner hull " ++
        "(handoff S3132Task30ThetaHalfActual / S3132QThetaConsumerWiringActual); " ++
        "independent of the F4/F5 => ABC implication of this gate. " ++
        "(d) ABCHeightWeightAdditiveBoundV2 = F5 card P -- owner project/Lead; " ++
        "exactly ABC-strength by tightness (IV Theorem A / [GenEll]); card U, " ++
        "hsplit/hptfin, mainline unconditional paper-normalized Q_C<=H_C, shehdd " ++
        "reduced same-C consumer and the actual Frey/height machinery are all " ++
        "proved/consumed.  Cross-stream handoffs: mainline " ++
        "S3131CanonicalRootedQCActual (Q_C numeric value only via " ++
        "S778 PaperQPilotLogFormulaIdentification gap, not claimed); shehdd " ++
        "S3134FourthTriangleCompositionStatusActual / S3134MainlineRootedHFaActual; " ++
        "hull S3132QThetaConsumerWiringActual / S3132Task30ThetaHalfActual."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135ValueMonoidIdentification (F4 (a) identification)",
        "S3135AdditiveHaarModulusLaw + paper lambda log-degree 0 (F4 (b))",
        "Theta-half C3-packet uniform comparison + normalization (hull, F5/Cor 3.12)",
        "ABCHeightWeightAdditiveBoundV2 (F5 card P, ABC-strength)" ] }

#check s3135_finalAssemblyGate
#check s3135_finalAssemblyGate_tight
#check S3135ValueMonoidIdentification
#check S3135ValueGroupDegreeSection
#check s3135_realifiedDegreeSection
#check S3135ScaledHaarNormalizedEquality
#check s3135FinalAssemblyGateReport

end LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateActual
end
