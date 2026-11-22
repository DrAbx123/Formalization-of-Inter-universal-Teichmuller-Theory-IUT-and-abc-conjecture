import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction

/-!
# Audit record for the abc stream (task-5): F4/F5 source-faithful attack

Registers, in the machine-readable audit vocabulary, exactly what the S3135 files
prove and what remains named.  No new mathematics here; this is the obligation
inventory with source anchors (IUT III Cor 3.12 :10324-10353; IUT IV Theorem 1.10
:1255-1385; IUT IV section 2 :2329-2332, Theorem A :93-112; [GenEll] Definition 1.5
as reviewed in IUT IV :2367-2375; Explicit estimates :123-126 for the initial-data
choice `l ~ (log q)^{1/2}`).
-/

namespace LeanFormal.IUT.Audit

/-- Source-faithful section-2 dictionary at the lambda-line point `x = a/c`:
the paper's `log-cond_D(x) = deg((s_x^* D)_red)` equals the arithmetic weight
`log rad(a*b*c)`, and the paper's `log-diff_X(x)` vanishes for the rational field
`F = Q(x) = Q`.  Status: proved kernel arithmetic, not the literal [GenEll]
definitions; the height/log-volume dictionary is the accepted
`RationalPointDictionary` height. -/
def s3135LambdaLineDictionaryObligation : Obligation :=
  { id := "IUT-IV.section2.lambda-line-log-diff-log-cond-dictionary"
    source :=
      "IUT IV section 2, :2367-2375 (log-diff / log-cond / ht dictionary); " ++
        "Theorem A, IUT IV:93-112; [GenEll] Definition 1.5; notesoniut:196-208"
    status := VerificationStatus.provedKernel
    note :=
      "S3135LambdaLineHeightLogCondActual.lean: constructs ht_{omega(D)}(x) as the " ++
        "canonical log-height (proved = Real.log c on ABC triples), log-cond_D(x) as " ++
        "the normalized degree of the reduced pullback divisor of [0]+[1]+[infty] " ++
        "(proved = arithmeticWeight = log rad(a*b*c)), and log-diff_X(x) as the " ++
        "normalized log-absolute-discriminant of F = Q(x) (proved = 0).  Proved: " ++
        "log-diff + log-cond = arithmeticWeight, and the Theorem A specialization " ++
        "LambdaLineVojtaShape eps C <-> the additive height/weight bound.  NOT the " ++
        "literal [GenEll] definitions on a number field; the field-degree extension " ++
        "case is not constructed."
    dependsOn := [ "ABC.statement" ] }

/-- F4 (`FrontierHeightComparisonClause`) at the source-realized carrier: the
named point datum is the actual height readout, the log-volume is the sup of
normalized log-degrees, so the region volume dominates the height and F4 holds. -/
def s3135F4RealizedCarrierObligation : Obligation :=
  { id := "IUT-III.cor312-F4-realized-height-carrier"
    source := "IUT III Cor 3.12 :10324-10353 (log-volume of hull/region); IUT IV :2367-2375"
    status := VerificationStatus.testCarrier
    note :=
      "S3135F4SourceHeightVolumeActual.lean: s3135_source_F4_heightComparison proves " ++
        "FrontierHeightComparisonClause at the realized carrier (real line of normalized " ++
        "log-volumes with sup-of-degrees log-volume and point datum = Height.logHeight₁ " ++
        "(abcRationalPoint a c)).  The carrier is a realization, not the literal " ++
        "IQ(S±; ...) inductive system; the content is that F4 has no residual arithmetic " ++
        "content once the point datum is the actual height readout.  " ++
        "s3135FrontierSourceComparison_iff_additiveBound identifies the residual F5 at " ++
        "this carrier with ABCHeightWeightAdditiveBoundV2."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ] }

/-- F5 / IUT IV Theorem 1.10 display: the remaining source inputs, named with
page/line anchors. -/
def s3135IUTIVTheorem110InputsObligation : Obligation :=
  { id := "IUT-IV.theorem-1.10.inputs-into-section2-display"
    source :=
      "IUT IV Theorem 1.10 :1255-1385 (theta-pilot log-volume estimate :1363-1376 " ++
        "and Cor 3.12 consequence display :1376-1385); IUT III Cor 3.12 :10324-10353; " ++
        "IUT IV section 2 Theorem A :93-112, :2404-2430"
    status := VerificationStatus.interface
    note :=
      "S3135IUTIVThetaBoundToComparisonActual.lean proves the real-variable " ++
        "bookkeeping: from (i) the Cor 3.12 lower bound -|log Theta| >= -|log q| " ++
        "(the source-realized Batch A comparison Q_C <= H_C, cf. S3130QCLeHCGap), " ++
        "(ii) the theta-pilot hull upper computation of IV:1363-1376, (iii) the " ++
        "initial-data bound log q <= l^2 (Explicit estimates:123-126) and the side " ++
        "conditions l >= 5, d_mod >= 0, e*_mod >= 1, eta_prm >= 0, one gets the " ++
        "display of IV:1376-1385; with the actual Frey model comparison " ++
        "6*ht(x)+log(27/64) <= h(j) one gets the height bound; with the section-2 " ++
        "uniformity passage (named IUTIVSection2Uniformity) one gets " ++
        "ABCHeightWeightAdditiveBoundV2.  NOT proved: the two named Theorem 1.10 " ++
        "inputs and the section-2 uniformity.  The realized log q is the log-height " ++
        "of the actual Frey j-invariant (q = j^{-1} on the bad support); the " ++
        "identification with deg(q^ADiv) of IV:1302-1362 is at dictionary level only."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface",
        "ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison" ]
    sorryItems :=
      [ "IUTIVCor312LowerBound (Cor 3.12 lower bound at realized readouts)",
        "IUTIVThetaHullComputation (IV:1363-1376 hull upper computation)",
        "IUTIVSection2Uniformity (IV section 2 bounded-discrepancy uniformity)" ] }

/-- Sign convention record (Lead cross-stream item): the Cor 3.12 / IUT IV section 2
comparisons are between *signed* log-volumes, while `IQHullLogVolumeInterface.logVolume`
values are nonnegative `ENNReal` magnitudes.  The source-realized Cor 3.12 input
`IUTIVCor312LowerBound` compares the signed q-pilot value `-|log q|` with the signed
theta-pilot value `-|log Theta| = -H_C^mag`; the mixed comparison against the
nonnegative magnitude `H_C^mag` would be vacuous.  The equivalence between the
signed and magnitude forms is `iutivCor312LowerBound_signBridge` and the vacuity of
the mixed form is `qPilotLogVolume_le_of_nonneg_magnitude`
(S3135IUTIVThetaBoundToComparisonActual.lean). -/
def s3135SignConventionObligation : Obligation :=
  { id := "IUT-III.cor312-signed-log-volume-sign-bridge"
    source := "IUT III Cor 3.12 :10340-10353 (signed -|log q|, -|log Theta|); IUT IV :1358-1362"
    status := VerificationStatus.provedKernel
    note :=
      "Signed-vs-magnitude sign bridge for the Cor 3.12 comparison.  Proved: the " ++
        "signed lower bound (-|log q| <= -H_C^mag) is equivalent to the magnitude " ++
        "bound H_C^mag <= |log q| (iutivCor312LowerBound_signBridge), and the mixed " ++
        "comparison -|log q| <= H_C^mag is automatic/vacuous " ++
        "(qPilotLogVolume_le_of_nonneg_magnitude).  Hence no S3135 consumer uses the " ++
        "vacuous mixed form."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ] }

/-- F4 at the actual value-realized carrier: exact residual record (Lead-requested
rework after the diagonal-fixture finding). -/
def s3135F4ActualResidualObligation : Obligation :=
  { id := "IUT-IV.section2.F4-actual-carrier-positive-degree-height-dictionary"
    source :=
      "IUT IV:2367-2375 (ht_{omega(D)} / log-diff / log-cond dictionary); " ++
        "IUT IV section 2 Theorem A :93-112; [GenEll] Definition 1.5, (iii), (iv); " ++
        "IUT III Remark 3.9.5 / Cor 3.12 :10324-10353 (hull and log-volumes)"
    status := VerificationStatus.interface
    note :=
      "S3135F4ActualHullResidualActual.lean: F4 at the ACTUAL value-realized carrier " ++
        "W = I.sourceUnitRegionHaarInterface v R n D (IQCarrierHaarData.lean:159-203, " ++
        "logVolume = sourceSetVolume = sup of actual sourceLocalLogDegree).  Proved: " ++
        "region-volume finiteness from SourceUnitRegionHaarData fields; region volume " ++
        "dominates the singleton point volume of scaling*p; F4 " ++
        "(FrontierHeightComparisonClause) follows from the named residual; the " ++
        "residual is equivalent to the singleton point-volume/height toReal card; the " ++
        "hull-containment route is impossible (unbounded heights vs finite hull, " ++
        "no_heightDictionary_into_finiteHull).  EXACT RESIDUAL (not proved): " ++
        "S3135ActualF4DegreeResidual eps = for all ABC triples, ht(x) <= " ++
        "(1+eps) * sourceLocalLogDegree v (D.scaling * p a b c) -- the POSITIVE " ++
        "direction of the value-monoid point log-degree/height dictionary.  The " ++
        "opposite (upper) direction degree <= ht is the card (d) of " ++
        "Cor312CarrierRealizationSpec.lean:58-85, refuted at (1,2,3) by log 6 > log 3; " ++
        "F4 must therefore use the lower-bound direction, which cannot be supplied " ++
        "by the weight/point-height dictionaries."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems := [ "S3135ActualF4DegreeResidual (positive degree/height dictionary at the actual carrier)" ] }

/-- Comparison assembly: both clauses at the realized arithmetic-line-bundle point,
consumed by the production bridge consumer. -/
def s3135ComparisonAssemblyObligation : Obligation :=
  { id := "IUT-III.cor312-epsilon-comparison-realized-assembly"
    source := "IUT IV Theorem 1.10 :1376-1385; IUT IV section 2 :2329-2332; IUT III Cor 3.12"
    status := VerificationStatus.interface
    note :=
      "S3135ComparisonAssemblyActual.lean: from the named section-2 uniform display " ++
        "family it assembles Cor312EpsilonArithmeticComparisonAdditive at the realized " ++
        "carrier (point datum (1/6) log q + log(64/27)/6, log-volume = sup of normalized " ++
        "degrees) with A = 0: F4 is discharged from the actual Frey model comparison, " ++
        "F5 from the display with the slope absorbed into eps.  The family is consumed " ++
        "by the production consumer abcHeightWeightAdditiveBoundV2_of_" ++
        "epsilonComparisonAdditive, yielding ABCHeightWeightAdditiveBoundV2.  " ++
        "The named input IUTIVSection2UniformDisplayFamily is not proved."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems := [ "IUTIVSection2UniformDisplayFamily (section-2 uniform display input)" ] }

end LeanFormal.IUT.Audit
