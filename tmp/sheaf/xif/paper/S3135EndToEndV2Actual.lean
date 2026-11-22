import tmp.sheaf.xif.paper.S3135F5ActualReductionActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import tmp.sheaf.xif.paper.S3135LogShellFaithfulnessExpansionActual
import tmp.sheaf.xif.paper.S3131PaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.S3134NativeContractShrinkActual

/-!
# End-to-end v2: mainline's paper-faithful signed comparison + shehdd's reduced same-C leg

**task-22 (3).**  Updates the task-17 end-to-end hypothesis list:

* the Corollary 3.12 leg is now **mainline's actual paper-normalized comparison**
  `S3131PaperRegionalQ <= S3131PaperRegionalHull` (`S3131PaperNormalizedComparisonActual`),
  which is unconditional on actual objects (same paper root normalization on both
  sides: `qPilotPaperRegion` and `paperRootThetaHullNonzero` in the same actual
  arithmetic tensor block, actual normalized Haar log-volume), together with its
  magnitude form `|log Theta| <= |log q|`.  It is consumed below as
  `s3135_mainlinePaperFaithfulSignedLeg`; the earlier conditional
  `IUTIVCor312LowerBound` is no longer needed as an input.
* the same-C coordination leg is shehdd's reduced bridge consumer
  `S3134Step3115_mainlineQC_le_thetaPilot_viaSameCReduced` (single cusp Missing),
  consumed as `s3135_shehddReducedSameCLeg`.
* F4 at the actual value-realized carrier: from the two cards of task-17
  (`S3135PointLogShellFaithfulness` + `S3135ScalingLogDegreeZero`).
* F5 at the same actual carrier: from the two minimal cards of
  `S3135F5ActualReductionActual` (unit-hull normalization + point-volume/weight).
* `ABCFrontier` assembly then gives `ABCConjecture` conditionally on the F4/F5
  cards (`s3135_abcConjecture_of_endToEndInputsV2`).

## Status of the actual faithful value-group action (task-22 (1))

The exact missing datum remains `S3135ValueGroupSplitting` (a degree-faithful
`Multiplicative Real ->* Mon v` action, IUT II Example 1.8(ix), iut2.txt:2402-2409;
[AbsTopIII] Proposition 5.8(ii); Remark 3.9.4).  The tree's only constructed
`SourceImageRealization` is the concrete value-layer model, where the action is
trivial and faithfulness is **refuted** (task-17 B); mainline's actual
`arithmeticTupleNormalizedLogVolume` data supplies the actual log-volume readouts
(consumed in the Cor 3.12 leg) but not an `Real`-indexed value-group action, and the
hull stream's actual `SourceQlLogShellConcrete.sourceQlPrincipalUnitLogImage =
principalUnitLogShell` equalities realize the log-shell additively (principal-unit log
image), not as a copy of `Real` inside the value monoid.  Hence (1) is reported as
**reduced + exact missing**, not proved: no inhabitant of
`S3135ValueGroupSplitting` on the paper carrier is constructed.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual

namespace LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual

/-! ## 1. Updated end-to-end hypothesis list -/

/-- **The updated end-to-end input list.**  F4 cards (point log-shell faithfulness and
zero normalized scaling log-degree) and F5 cards (unit-hull normalization and
point-volume/weight) on the same actual value-realized carrier; the Cor 3.12 and
same-C legs are mainline's/shehdd's *proved* actual consumers (below), not inputs. -/
structure S3135EndToEndInputsV2
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) : Prop where
  /-- Card (1) reduced form: pointwise log-shell value-group faithfulness. -/
  hpt : S3135PointLogShellFaithfulness I v R
  /-- Card (2): zero normalized scaling log-degree. -/
  hzero : S3135ScalingLogDegreeZero I v R n D
  /-- F5 card U: unit-region normalization against the θ-pilot hull bound. -/
  hunit : S3135ActualUnitHullCard I v R n D
  /-- F5 card P: arithmetic-line-bundle point volume against the arithmetic weight,
  at the constructed value-realized point. -/
  hpoint : S3135ActualPointWeightCard I v R n D (abcSourcePoint I v R)

/-- **End-to-end v2: F4 (actual) + F5 (actual) => ABC.** -/
theorem s3135_abcConjecture_of_endToEndInputsV2
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (inp : S3135EndToEndInputsV2 I v R n D) :
    ABCConjecture := by
  have hnorm : ∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps :=
    s3135_normalization_of_scalingLogDegreeZero I v R n D inp.hzero
  have hF4 : FrontierHeightComparisonClause (sourceActualCarrier I v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) :=
    s3135_actualF4_of_pointFaithfulness I v R n D inp.hpt hnorm
  have hF5 : FrontierRegionComparisonClause (sourceActualCarrier I v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) :=
    s3135_actualFrontierRegionClause_of_cards I v R n D (abcSourcePoint I v R)
      inp.hunit inp.hpoint
  exact abcConjecture_of_frontier
    ⟨I.ThetaPilotPoint v, sourceActualCarrier I v R n D,
      (fun _ _ a b c => abcSourcePoint I v R a b c), hF4, hF5⟩

/-! ## 2. Consuming mainline's paper-faithful signed comparison -/

section MainlinePaperFaithful

open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual

variable {lM : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} lM)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- **Mainline's actual paper-faithful Cor 3.12 comparison, consumed.**  The
paper-normalized signed comparison `Q_C <= H_C` and its magnitude form
`|log Theta| <= |log q|` (IUT III Corollary 3.12, :10324-10353) hold
unconditionally on the actual objects. -/
theorem s3135_mainlinePaperFaithfulSignedLeg :
    S3131PaperRegionalQ (l := lM) T mu ≤ S3131PaperRegionalHull (l := lM) T mu ∧
      S3131PaperHullMagnitude (l := lM) T mu ≤ S3131PaperQMagnitude (l := lM) T mu :=
  ⟨S3131PaperRegionalQ_le_Hull (l := lM) T mu,
    (S3131PaperRegionalQ_le_Hull_iff_magnitude (l := lM) T mu).mp
      (S3131PaperRegionalQ_le_Hull (l := lM) T mu)⟩

end MainlinePaperFaithful

/-! ## 3. Consuming shehdd's reduced same-C leg -/

section ShehddReduced

open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointTriangleActual
open LeanFormal.IUT.XiFPaper.S3134ThetaHullDetNormalizationActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open LeanFormal.IUT.XiFPaper.S3134NativeContractShrinkActual

universe uL uC uvL uaP upiP umonP uiP

variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable (Ih : Input Label Choice)
variable {lP : PrimeGeFive} {VP : Type uvL}
variable (JP : OriginalInput.{0, uvL, upiP, umonP, uiP} lP VP)
variable (TP : SourceNativeInitialThetaData.{0} lP)
variable [Fintype (Bad (nativePlaceSelection TP))]

/-- **shehdd's reduced same-C leg, consumed.**  From the reduced same-C bridge (one
cusp data field) and the fourth-joint comparison gap, the mainline actual q readout is
bounded by the assembled signed Θ-pilot readout:
`S3131QC T <= -|log Θ|`. -/
theorem s3135_shehddReducedSameCLeg
    (D : S1300HDDHullDetSource Ih)
    (G : S3134QThetaComparisonGap (I := Ih) (J := JP) D)
    (H : S3134SameCReadoutIdentificationReduced (J := JP) (T := TP)) :
    S3131QC TP ≤ S3134Step3115ThetaPilotReadout (I := Ih) D :=
  S3134Step3115_mainlineQC_le_thetaPilot_viaSameCReduced
    (I := Ih) (J := JP) (T := TP) D G H

end ShehddReduced

/-! ## 4. Completeness report v2 -/

/-- Machine-readable completeness record for the task-22 end-to-end v2 hypothesis
list (mainline paper-faithful Cor 3.12 consumer + shehdd reduced same-C consumer). -/
def s3135EndToEndV2Report : Audit.Obligation :=
  { id := "IUT-IV.f4-f5-end-to-end-v2-mainline-signed"
    source :=
      "IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] Prop 5.8(ii); " ++
        "Remark 3.9.4; IUT III Cor 3.12 :10324-10353; IUT IV Theorem 1.10 " ++
        ":1255-1385; IUT IV section 1 Prop 1.4 iut4.txt:671-760; IUT IV section 2 " ++
        ":2329-2340; [GenEll] Definition 1.5; IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "PROVED (consumed, unconditional actual): mainline S3131PaperRegionalQ_le_Hull " ++
        "paper-normalized signed Q_C <= H_C and its magnitude form |log Theta| <= " ++
        "|log q| (S3131PaperNormalizedComparisonActual); shehdd " ++
        "S3134Step3115_mainlineQC_le_thetaPilot_viaSameCReduced (reduced same-C " ++
        "bridge, single cusp Missing); F5 structural inputs hsplit/hptfin " ++
        "(Cor312ComparisonGapSupplyLayer:127/:152); card (2) on the concrete actual " ++
        "model.  PROVED (conditional assembly): F4 actual from the two cards + F5 " ++
        "actual from cards U/P => ABCFrontier => ABCConjecture " ++
        "(s3135_abcConjecture_of_endToEndInputsV2).  REDUCED: F5 at the actual " ++
        "carrier <=> card U (unit degree bound vs hull volume) + card P (point " ++
        "volume vs arithmetic weight); card (1) <=> Nonempty value-group splitting; " ++
        "card (2) family <=> zero scaling log-degree.  REFUTED: full/pointwise " ++
        "value-group faithfulness on the concrete value-layer model.  EXACT MISSING " ++
        "(task-22 (1)): an inhabitant of S3135ValueGroupSplitting on the paper " ++
        "carrier (actual Real-indexed degree-faithful value-group action); the tree's " ++
        "constructed realization is trivial/refuted and mainline's actual Haar " ++
        "log-volume readouts do not supply the action.  Still named: " ++
        "IUTIVSection2UniformDisplayFamily (IV section 2 uniform display), shehdd " ++
        "S3134QThetaComparisonGap, same-C cusp data."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135ValueGroupSplitting inhabitant on the paper carrier (task-22 (1))",
        "S3135ActualUnitHullCard (F5 card U)",
        "S3135ActualPointWeightCard (F5 card P)",
        "IUTIVSection2UniformDisplayFamily (section-2 route)",
        "S3134QThetaComparisonGap (shehdd signed comparison)" ] }

#check S3135EndToEndInputsV2
#check s3135_abcConjecture_of_endToEndInputsV2
#check s3135_mainlinePaperFaithfulSignedLeg
#check s3135_shehddReducedSameCLeg
#check s3135EndToEndV2Report

end LeanFormal.IUT.XiFPaper.S3135EndToEndV2Actual
end
