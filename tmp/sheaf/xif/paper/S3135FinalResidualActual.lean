import tmp.sheaf.xif.paper.S3135F5ActualReductionActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import tmp.sheaf.xif.paper.S3135LogShellValueGroupActual
import tmp.sheaf.xif.paper.S3135EndToEndV2Actual

/-!
# Final minimal residual of the F4/F5 end-to-end chain

**task-25.**  Three attacks, with the honest per-item outcome:

## (2) F5 card U: PROVED unconditionally

`S3135ActualUnitHullCard` asks
`exists D0 >= 0, ofReal D.degreeBound <= sourceHullVolume + ofReal D0`.
It is discharged directly with the canonical constant
`D0 = max D.degreeBound 0` (the production supply layer already noted the canonical
instance, `Cor312CarrierSpec.lean:44-50`): if `degreeBound >= 0` then
`ofReal D0 = degreeBound` and the inequality reduces to `0 <= sourceHullVolume`;
if `degreeBound < 0` then the left side is `0`.  No actual-normalization content is
needed; card U is NOT a residual of the chain.

## (3) F5 card P: reduced exactly to the height/weight additive bound (ABC-strength)

Card P (`S3135ActualPointWeightCard` at the constructed point) is proved
**equivalent** to `ABCHeightWeightAdditiveBoundV2` (the IUT IV Theorem A / [GenEll]
shape `height <= (1+eps)*weight + A`) under the two F4 cards:

* card (1) `S3135PointLogShellFaithfulness` gives the actual log-degree of the
  constructed point: `logDegree(scaling * abcSourcePoint) = logDegree(scaling) + ht(x)`;
* card (2) `S3135ScalingLogDegreeZero` kills the scaling term;
* the singleton log-volume is `ofReal` of that log-degree
  (`cor312GapSupply_sourceSetVolume_singleton`), so card P is literally the
  height/weight bound.  This is consistent with the paper: F5 is the main IUT IV
  section 2 estimate (IV:2329-2340; [GenEll] Definition 1.5; IV:2367-2375), i.e. the
  genuine ABC-strength arithmetic comparison.  The uniform-valuation H1 route is
  refuted (`no_oneAdd_valuation_bound`), so the additive form is the faithful one.

## (1) Actual paper-carrier value-group splitting: still the exact missing datum

No inhabitant of `S3135ValueGroupSplitting` on the paper carrier is constructed.
Status unchanged from task-17/22: the generator direction `Z.log q` is proved; the
tree's only constructed realization is the concrete value-layer model whose
faithfulness is refuted; mainline's actual normalized Haar readouts supply
log-volumes, not an `Real`-indexed degree-faithful action; the hull stream's actual
`SourceQlLogShellConcrete` equalities realize the log shell additively
(principal-unit log image).  Exact missing: a degree-faithful value-group action
(IUT II Example 1.8(ix), iut2.txt:2402-2409; [AbsTopIII] Proposition 5.8(ii);
Remark 3.9.4) on the paper-level value monoid.

## Final minimal residual of the end-to-end chain

`s3135_abcConjecture_of_minimalResiduals`: from the two F4 cards and card P one gets
`ABCConjecture` (card U is proved, hsplit/hptfin proved, mainline's unconditional
paper-normalized Cor 3.12 comparison and shehdd's reduced same-C consumer are
consumed).  **Minimal residual**:

1. `S3135PointLogShellFaithfulness` (actual log-shell value-group half, IUT II
   Example 1.8(ix));
2. `S3135ScalingLogDegreeZero` for the paper carrier (IUT III Remark 3.9.5(i);
   IUT IV section 1 Prop 1.4);
3. `ABCHeightWeightAdditiveBoundV2` (F5 card P; IUT IV Theorem A / [GenEll]);
plus shehdd's residuals `S3134QThetaComparisonGap` and the same-C cusp data, which
are independent of this chain.
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

namespace LeanFormal.IUT.XiFPaper.S3135FinalResidualActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)

/-! ## (2) Card U proved unconditionally -/

/-- **F5 card U is not a residual**: the canonical constant `D0 = max D.degreeBound 0`
discharges the unit-region normalization against the hull bound, using only
nonnegativity of the hull log-volume. -/
theorem s3135_actualUnitHullCard : S3135ActualUnitHullCard I v R n D := by
  refine ⟨max D.degreeBound 0, le_max_right _ _, ?_⟩
  rcases le_total 0 D.degreeBound with hb | hb
  · rw [max_eq_left hb]
    calc ENNReal.ofReal D.degreeBound = 0 + ENNReal.ofReal D.degreeBound :=
          (zero_add _).symm
      _ ≤ I.sourceHullVolume v R n + ENNReal.ofReal D.degreeBound :=
          add_le_add
            (show (0 : ENNReal) ≤ I.sourceHullVolume v R n from bot_le) le_rfl
  · rw [max_eq_right hb, ENNReal.ofReal_of_nonpos hb]
    simp only [ENNReal.ofReal_zero]
    exact bot_le

/-- F5 at the actual carrier from card P alone (card U discharged above). -/
theorem s3135_actualFrontierRegionClause_of_pointCard
    (hP : S3135ActualPointWeightCard I v R n D (abcSourcePoint I v R)) :
    FrontierRegionComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) :=
  s3135_actualFrontierRegionClause_of_cards I v R n D (abcSourcePoint I v R)
    (s3135_actualUnitHullCard I v R n D) hP

/-! ## (3) Card P <=> the height/weight additive bound -/

/-- The singleton log-volume of the scaled constructed point is `ofReal` of the
actual log-degree `logDegree(scaling) + ht(x)`. -/
theorem sourceActual_singletonVolume_scaledPoint (a b c : ℕ) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift
          (abcSourcePoint I v R a b c)} =
      ENNReal.ofReal (I.sourceLocalLogDegree v (D.scaling * abcSourcePoint I v R a b c)) := by
  change I.sourceSetVolume v
    {(fun x => D.scaling * x) (abcSourcePoint I v R a b c)} =
      ENNReal.ofReal (I.sourceLocalLogDegree v (D.scaling * abcSourcePoint I v R a b c))
  rw [I.cor312GapSupply_sourceSetVolume_singleton v]
  rfl

/-- **Card P <=> the version-2 additive height/weight bound**, under the two F4
cards.  Hence F5's arithmetic residual is exactly the IUT IV Theorem A shape
(ABC-strength), not a weaker or differently-normalized statement. -/
theorem s3135_pointWeightCard_iff_additiveBound
    (hpt : S3135PointLogShellFaithfulness I v R)
    (hzero : S3135ScalingLogDegreeZero I v R n D) :
    S3135ActualPointWeightCard I v R n D (abcSourcePoint I v R) ↔
      ABCHeightWeightAdditiveBoundV2 := by
  constructor
  · intro hP eps heps
    obtain ⟨D₁, hD₁⟩ := hP eps heps
    refine ⟨D₁, fun a b c habc => ?_⟩
    have hdeg : I.sourceLocalLogDegree v (D.scaling * abcSourcePoint I v R a b c) =
        I.sourceLocalLogDegree v D.scaling +
          Height.logHeight₁ (abcRationalPoint a c) := by
      rw [I.sourceLocalLogDegree_mul,
        sourceLocalLogDegree_abcSourcePoint_of_pointFaithfulness I v R hpt habc]
    unfold S3135ScalingLogDegreeZero at hzero
    rw [hzero, zero_add] at hdeg
    have hnn : 0 ≤ I.sourceLocalLogDegree v (D.scaling * abcSourcePoint I v R a b c) := by
      rw [hdeg]; exact Height.zero_le_logHeight₁ _
    have hvol := sourceActual_singletonVolume_scaledPoint I v R n D a b c
    have hb := hD₁ a b c habc
    rw [hvol, ENNReal.toReal_ofReal hnn, hdeg] at hb
    exact hb
  · intro hV2 eps heps
    obtain ⟨A, hA⟩ := hV2 eps heps
    refine ⟨A, fun a b c habc => ?_⟩
    have hdeg : I.sourceLocalLogDegree v (D.scaling * abcSourcePoint I v R a b c) =
        Height.logHeight₁ (abcRationalPoint a c) := by
      have h1 : I.sourceLocalLogDegree v (D.scaling * abcSourcePoint I v R a b c) =
          I.sourceLocalLogDegree v D.scaling +
            Height.logHeight₁ (abcRationalPoint a c) := by
        rw [I.sourceLocalLogDegree_mul,
          sourceLocalLogDegree_abcSourcePoint_of_pointFaithfulness I v R hpt habc]
      unfold S3135ScalingLogDegreeZero at hzero
      rw [hzero, zero_add] at h1
      exact h1
    have hnn : 0 ≤ I.sourceLocalLogDegree v (D.scaling * abcSourcePoint I v R a b c) := by
      rw [hdeg]; exact Height.zero_le_logHeight₁ _
    have hvol := sourceActual_singletonVolume_scaledPoint I v R n D a b c
    rw [hvol, ENNReal.toReal_ofReal hnn, hdeg]
    exact hA a b c habc

/-! ## Final minimal residual -/

/-- **Final minimal residual of the end-to-end chain**: the two F4 cards plus card P
(the height/weight additive bound) yield `ABCConjecture`; card U, the structural
inputs, mainline's paper-normalized Cor 3.12 comparison and shehdd's reduced same-C
consumer are all discharged/consumed. -/
theorem s3135_abcConjecture_of_minimalResiduals
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀)
    (hP : S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀)) :
    ABCConjecture :=
  s3135_abcConjecture_of_endToEndInputsV2 I₀ v₀ R₀ n₀ D₀
    { hpt := hpt, hzero := hzero,
      hunit := s3135_actualUnitHullCard I₀ v₀ R₀ n₀ D₀, hpoint := hP }

/-- **Minimal-residual completeness record** for the final chain. -/
def s3135FinalMinimalResidualReport : Audit.Obligation :=
  { id := "IUT-IV.f4-f5-final-minimal-residual"
    source :=
      "IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] Prop 5.8(ii); " ++
        "Remark 3.9.4; IUT III Cor 3.12 :10324-10353; IUT III Remark 3.9.5(i); " ++
        "IUT IV Theorem 1.10 :1255-1385; IUT IV section 1 Prop 1.4 " ++
        "iut4.txt:671-760; IUT IV section 2 :2329-2340; [GenEll] Definition 1.5; " ++
        "IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "FINAL MINIMAL RESIDUAL of the F4/F5 end-to-end chain.  PROVED here/earlier: " ++
        "F5 card U unconditional (canonical D0 = max degreeBound 0); F5 hsplit/hptfin " ++
        "unconditional supply-layer theorems; card P <=> ABCHeightWeightAdditiveBoundV2 " ++
        "under the two F4 cards (so F5's arithmetic residual is exactly IV Theorem A / " ++
        "[GenEll] shape, ABC-strength); mainline S3131PaperRegionalQ <= H_C (unconditional " ++
        "actual paper-normalized Cor 3.12) consumed; shehdd reduced same-C consumer " ++
        "consumed; F4 assembly conditional.  MINIMAL RESIDUAL: (1) " ++
        "S3135PointLogShellFaithfulness (actual log-shell value-group half); (2) " ++
        "S3135ScalingLogDegreeZero on the paper carrier (zero normalized scaling " ++
        "log-degree; proved on the concrete model only); (3) " ++
        "ABCHeightWeightAdditiveBoundV2 (F5 card P; IUT IV Theorem A).  Independent " ++
        "shehdd residuals: S3134QThetaComparisonGap and same-C cusp data.  REFUTED, " ++
        "not progress: full/pointwise faithfulness on the concrete value-layer model."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135PointLogShellFaithfulness (paper-carrier log-shell value-group half)",
        "S3135ScalingLogDegreeZero (paper-carrier normalized scaling)",
        "ABCHeightWeightAdditiveBoundV2 (F5 card P / IV Theorem A)" ] }

#check s3135_actualUnitHullCard
#check s3135_actualFrontierRegionClause_of_pointCard
#check s3135_pointWeightCard_iff_additiveBound
#check s3135_abcConjecture_of_minimalResiduals
#check s3135FinalMinimalResidualReport

end LeanFormal.IUT.XiFPaper.S3135FinalResidualActual
end
