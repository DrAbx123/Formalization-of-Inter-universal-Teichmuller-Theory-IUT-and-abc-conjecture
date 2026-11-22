import tmp.sheaf.xif.paper.S3135LogShellValueGroupActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import tmp.sheaf.xif.paper.S3135ComparisonAssemblyActual
import tmp.sheaf.xif.paper.S3134Step3115To312Actual

/-!
# End-to-end conditional assembly: F4 (actual) + F5 (section 2) + shehdd's signed comparison => ABC

**task-17 (C).**  This file ties the stream together with every residual explicitly
named (no residual is renamed into a proof):

## Route 1: actual-carrier F4 + F5 at the same actual carrier => ABC

* carrier: the actual value-realized `IQHullLogVolumeInterface`
  `W = I.sourceUnitRegionHaarInterface v R n D` (`IQCarrierHaarData.lean:159-203`);
* point datum: the constructed arithmetic-line-bundle point `abcSourcePoint a b c`
  (constant value-monoid point with total log-degree `ht(x)`);
* F4 (`FrontierHeightComparisonClause`): from the two named cards
  `S3135PointLogShellFaithfulness` (task-11/17 B) and
  `S3135ScalingLogDegreeZero` (task-11 card (2); proved unconditionally on the
  concrete actual model in task-17 A);
* F5 (`FrontierRegionComparisonClause`): the region-volume comparison at the same
  actual carrier, named residual `hF5` below (this is the IUT IV section 2 /
  Corollary 3.12 θ-pilot log-volume comparison at the realized carrier);
* assembly: `ABCFrontier` (`ABCFrontier.lean:187`) and
  `abcConjecture_of_frontier` (`ABCFrontier.lean:213`) give `ABCConjecture`.

## Route 2: IUT IV section 2 display family => length bound => ABC

`IUTIVSection2UniformDisplayFamily` (the section-2 uniform form of the Theorem 1.10
display, IV:1376-1385 with the bounded-discrepancy uniformity, IV:93-112,
:2404-2430) yields `ABCHeightWeightAdditiveBoundV2` through the assembled bridge
consumer (`S3135ComparisonAssemblyActual`), equivalently `ABCConjecture`.

## Cross-stream: shehdd's signed 3.11.5 => 3.12 leg

`S3134Step3115_qPilot_le_thetaPilot` gives the signed comparison
`-|log q| <= -|log Θ|`; `S3134Step3115_magnitudeBound` gives the genuine magnitude
form `H <= |log q|`; `S3134Step3115_CTheta` gives `C_Θ >= -1`.  The signed form is
the one compatible with abc's sign bridges (signed vs nonnegative magnitude; the
mixed form is vacuous).  Consumed below in `s3135_shehddSignedLeg`; residuals
`S3134QThetaComparisonGap` and `S3134MainlineQCSameC` remain named.

## Residual inventory (proved / refuted / reduced)

proved: card (2) equivalence (task-11) and card (2) on the concrete actual model
(task-17 A); F4 conditional on cards; Route 2 conditional assembly.
refuted: full/pointwise value-group faithfulness on the concrete value-layer model
(task-17 B) — card (1) is additional structure, not a consequence of the data.
reduced: card (1) <=> existence of a faithful value-group splitting (task-17 B);
card (2) family <=> zero scaling log-degree (task-11).
named residuals and sources: `S3135PointLogShellFaithfulness` (IUT II Example
1.8(ix) iut2.txt:2402-2409; [AbsTopIII] Prop 5.8(ii); Remark 3.9.4);
`S3135ScalingLogDegreeZero` (IUT III Remark 3.9.5(i); IUT IV section 1 Prop 1.4,
iut4.txt:671-760); `IUTIVSection2UniformDisplayFamily` (IUT IV Theorem 1.10
:1255-1385, section 2 :93-112, :2404-2430); F5-at-actual-carrier (IUT IV section 2
main estimate / IUT III Cor 3.12:10324-10353).
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135ComparisonAssemblyActual

namespace LeanFormal.IUT.XiFPaper.S3135EndToEndAssemblyActual

/-! ## 1. Route 1: actual-carrier assembly -/

/-- **Route 1 (actual carrier): F4 + F5 => ABC.**  At the actual value-realized
carrier, the constructed arithmetic-line-bundle point satisfies F4 from the two named
cards, and the remaining F5 region comparison is the explicit hypothesis `hF5`; the
frontier assembly then yields `ABCConjecture`. -/
theorem s3135_abcConjecture_of_actualCarrierInputs
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hpt : S3135PointLogShellFaithfulness I v R)
    (hzero : S3135ScalingLogDegreeZero I v R n D)
    (hF5 : FrontierRegionComparisonClause (sourceActualCarrier I v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c)) :
    ABCConjecture := by
  have hnorm : ∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps :=
    s3135_normalization_of_scalingLogDegreeZero I v R n D hzero
  have hF4 : FrontierHeightComparisonClause (sourceActualCarrier I v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) :=
    s3135_actualF4_of_pointFaithfulness I v R n D hpt hnorm
  exact abcConjecture_of_frontier
    ⟨I.ThetaPilotPoint v, sourceActualCarrier I v R n D,
      (fun _ _ a b c => abcSourcePoint I v R a b c), hF4, hF5⟩

/-! ## 2. Route 2: section-2 display family => ABC -/

/-- **Route 2: IUT IV section 2 display family => `ABCConjecture`.** -/
theorem s3135_abcConjecture_of_section2DisplayFamily
    (h : IUTIVSection2UniformDisplayFamily) : ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr
    (s3135_ABCHeightWeightAdditiveBoundV2_of_displayFamily h)

/-! ## 3. Cross-stream consumption: shehdd's signed 3.11.5 => 3.12 leg -/

section ShehddSigned

open scoped BigOperators
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3131QCActualReadout
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointTriangleActual
open LeanFormal.IUT.XiFPaper.S3134ThetaHullDetNormalizationActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual

universe uL uC uvL uaP upiP umonP uiP

variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable (Ih : Input Label Choice)
variable {lP : PrimeGeFive} {VP : Type uvL}
variable (JP : OriginalInput.{uaP, uvL, upiP, umonP, uiP} lP VP)
variable (TP : SourceNativeInitialThetaData.{0} lP)
variable [Fintype (Bad (nativePlaceSelection TP))]

/-- **Consumption of shehdd's signed 3.11.5 => 3.12 assembly**: from the fourth-joint
comparison gap, the signed comparison `-|log q| <= -|log Θ|`, its magnitude form
`H <= |log q|`, and the `C_Θ >= -1` consumer all hold.  The signed form is the one
compatible with abc's sign bridges. -/
theorem s3135_shehddSignedLeg
    (D : S1300HDDHullDetSource Ih)
    (G : S3134QThetaComparisonGap (I := Ih) (J := JP) D) :
    S3134Step3115QPilotReadout (J := JP) ≤
        S3134Step3115ThetaPilotReadout (I := Ih) D ∧
      S3134ThetaHullLogVolume (I := Ih) D ≤ |Real.log (S3134QParameter JP)| ∧
      (∀ {cTheta : ℝ}, S3134Step3115ThetaPilotReadout (I := Ih) D ≤
        cTheta * |Real.log (S3134QParameter JP)| → -1 ≤ cTheta) :=
  ⟨S3134Step3115_qPilot_le_thetaPilot (I := Ih) (J := JP) D G,
    S3134Step3115_magnitudeBound (I := Ih) (J := JP) D G,
    fun {cTheta} hc => S3134Step3115_CTheta (I := Ih) (J := JP) D G hc⟩

end ShehddSigned

/-! ## 4. Completeness / residual report -/

/-- Machine-readable completeness record for the task-17 end-to-end assembly. -/
def s3135EndToEndCompletenessReport : Audit.Obligation :=
  { id := "IUT-IV.f4-f5-end-to-end-conditional-assembly"
    source :=
      "IUT II Example 1.8(ix) (log-shell, iut2.txt:2402-2409); [AbsTopIII] " ++
        "Proposition 5.8(ii); Remark 3.9.4; IUT III Cor 3.12 :10324-10353 and " ++
        "Step (xi-f) :10888-10899; IUT IV Theorem 1.10 :1255-1385; IUT IV " ++
        "section 1 Proposition 1.4 (iut4.txt:671-760); IUT IV section 2 " ++
        ":93-112, :2329-2332; [GenEll] Definition 1.5; IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "PROVED: card (2) family <=> logDegree_v(scaling)=0 (S3135ScalingNormalization); " ++
        "card (2) holds unconditionally on the concrete actual value-layer model " ++
        "(S3135ScalingActualModel); F4 at the actual value-realized carrier from " ++
        "(point log-shell faithfulness) + (zero scaling log-degree); Route 2: " ++
        "IUTIVSection2UniformDisplayFamily => ABCHeightWeightAdditiveBoundV2 => " ++
        "ABCConjecture.  REFUTED: full and pointwise value-group faithfulness on the " ++
        "concrete value-layer model (trivial positive-real action), so the card is " ++
        "additional structure, not derivable from the data.  REDUCED: card (1) <=> " ++
        "Nonempty S3135ValueGroupSplitting (faithful value-group action); cyclic " ++
        "Z.log q case proved.  NAMED RESIDUALS: S3135PointLogShellFaithfulness " ++
        "(IUT II Example 1.8(ix)); S3135ScalingLogDegreeZero for the paper carrier " ++
        "(IUT III Remark 3.9.5(i); IUT IV section 1 Prop 1.4); F5 at the actual " ++
        "carrier (IUT IV section 2 main estimate / IUT III Cor 3.12); " ++
        "IUTIVSection2UniformDisplayFamily; shehdd's S3134QThetaComparisonGap and " ++
        "S3134MainlineQCSameC.  No sorry/axiom/arbitrary carrier."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135PointLogShellFaithfulness (paper-carrier faithful log-shell value-group half)",
        "S3135ScalingLogDegreeZero (paper-carrier normalized scaling log-degree)",
        "F5 at the actual carrier (region-volume comparison)",
        "IUTIVSection2UniformDisplayFamily (section-2 uniform display)",
        "S3134QThetaComparisonGap (shehdd signed Cor 3.12 comparison)",
        "S3134MainlineQCSameC (same-C q readout identification)" ] }

#check s3135_abcConjecture_of_actualCarrierInputs
#check s3135_abcConjecture_of_section2DisplayFamily
#check s3135_shehddSignedLeg
#check s3135EndToEndCompletenessReport

end LeanFormal.IUT.XiFPaper.S3135EndToEndAssemblyActual
end
