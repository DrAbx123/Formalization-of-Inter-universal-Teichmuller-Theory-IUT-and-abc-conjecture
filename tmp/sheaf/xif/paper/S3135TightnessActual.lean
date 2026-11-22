import tmp.sheaf.xif.paper.S3135FinalResidualActual

/-!
# Tightness of the final residual chain; task-31 status of the three residuals

**task-31.**  This file records the tightness of the last three residuals and the
structural finding for the actual log-shell value-group action.

## (c) The F5 arithmetic card is exactly ABC-strength (proved, tight)

`s3135_pointWeightCard_iff_abcConjecture`: under the two F4 cards, the F5 card P
(`S3135ActualPointWeightCard` at the constructed point) is **equivalent to
`ABCConjecture`** — composing the already proved
`card P <=> ABCHeightWeightAdditiveBoundV2` with the accepted production
equivalence `abcConjecture_iff_ABCHeightWeightAdditiveBoundV2`
(`ABCHeightArithmeticWeightComparison.lean:167`).  Consequently the end-to-end chain
cannot be closed by any *weaker* residual in the F5 slot: card P is exactly the
numerical bridge, the IUT IV Theorem A / [GenEll] shape (IV:2329-2340;
[GenEll] Definition 1.5; IV:2367-2375).  The converse direction also shows that
`ABCConjecture` supplies card P at *every* actual carrier — i.e. the F5 slot is
ABС-complete.

## (a) Actual log-shell value-group half: structural finding + exact missing

The missing datum is an `Real`-indexed, degree-faithful action
`Multiplicative Real ->* Mon v` on the paper-level value monoid (IUT II
Example 1.8(ix), iut2.txt:2402-2409; [AbsTopIII] Proposition 5.8(ii);
Remark 3.9.4).  Structural finding from the actual log-shell theory: the realized
log-shell data available in the tree (hull stream `SourceQlLogShellConcrete`:
`sourceQlPrincipalUnitLogImage = principalUnitLogShell`) is an image in the
**unit/principal-unit group**, whose values have degree/norm `0`; a degree-faithful
action at `x != 0` must have value degree `x`, so the principal-unit log image
**cannot** supply it — the missing object is a value-GROUP level embedding (a
splitting of the degree map), not a unit-group log image.  This narrows the exact
missing: `S3135ValueGroupSplitting` must be realized on the q-power/value-group
side, not from principal units.  Generator direction `Z.log q` and additive
closure are proved (task-11/17); full `Real`-indexed splitting is not constructed.

## (b) Normalized scaling log-degree: reduced

`S3135ScalingLogDegreeZero` on the paper carrier is the normalized-`lambda·O`
equation (IUT III Remark 3.9.5(i); IUT IV section 1 Proposition 1.4,
iut4.txt:671-760).  It is proved on the concrete actual model (task-17 A) and is
equivalent to the full `eps`-family of scaling-normalization inequalities
(task-11); on the paper carrier it remains the named normalization input.  The
carrier field only gives `logDegree(scaling) <= 0`, so no proof from the current
fields is possible without the normalized-log-volume identification.
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
open LeanFormal.IUT.XiFPaper.S3135FinalResidualActual

namespace LeanFormal.IUT.XiFPaper.S3135TightnessActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)

/-- **F5 card P is exactly ABC-strength** (under the two F4 cards): it is equivalent
to the additive height/weight bound and hence to the ABC conjecture through the
accepted production equivalence.  No weaker F5 residual can close the chain. -/
theorem s3135_pointWeightCard_iff_abcConjecture
    (hpt : S3135PointLogShellFaithfulness I v R)
    (hzero : S3135ScalingLogDegreeZero I v R n D) :
    S3135ActualPointWeightCard I v R n D (abcSourcePoint I v R) ↔ ABCConjecture :=
  (s3135_pointWeightCard_iff_additiveBound I v R n D hpt hzero).trans
    abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.symm

/-- Converse tightness direction: if `ABCConjecture` holds then the F5 card P holds
at every actual carrier (with the two F4 cards); hence no weaker residual exists in
the F5 slot. -/
theorem s3135_pointWeightCard_of_abcConjecture
    (hpt : S3135PointLogShellFaithfulness I v R)
    (hzero : S3135ScalingLogDegreeZero I v R n D)
    (hABC : ABCConjecture) :
    S3135ActualPointWeightCard I v R n D (abcSourcePoint I v R) :=
  (s3135_pointWeightCard_iff_abcConjecture I v R n D hpt hzero).mpr hABC

/-- **Final chain from the three named residuals**: the two F4 cards and the F5
card P (the numerical bridge) yield `ABCConjecture`; all other components (card U,
hsplit/hptfin, mainline's paper-normalized Cor 3.12 comparison, shehdd's reduced
same-C consumer) are proved/consumed. -/
theorem s3135_abcConjecture_of_threeResiduals
    {l₀ : PrimeGeFive} {V₀ : Type} (I₀ : OriginalInput l₀ V₀) (v₀ : V₀)
    (R₀ : I₀.SourceImageRealization v₀) (n₀ : ThetaPilotCarrier l₀)
    (D₀ : I₀.SourceUnitRegionHaarData v₀ R₀ n₀)
    (hpt : S3135PointLogShellFaithfulness I₀ v₀ R₀)
    (hzero : S3135ScalingLogDegreeZero I₀ v₀ R₀ n₀ D₀)
    (hP : S3135ActualPointWeightCard I₀ v₀ R₀ n₀ D₀ (abcSourcePoint I₀ v₀ R₀)) :
    ABCConjecture :=
  s3135_abcConjecture_of_minimalResiduals I₀ v₀ R₀ n₀ D₀ hpt hzero hP

/-- Machine-readable tightness/status record for the last three residuals. -/
def s3135TightnessReport : Audit.Obligation :=
  { id := "IUT-IV.f4-f5-tightness-final-residuals"
    source :=
      "IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] Prop 5.8(ii); " ++
        "Remark 3.9.4; IUT III Cor 3.12 :10324-10353; IUT III Remark 3.9.5(i); " ++
        "IUT IV Theorem 1.10 :1255-1385; IUT IV section 1 Prop 1.4 " ++
        "iut4.txt:671-760; IUT IV section 2 :2329-2340; [GenEll] Definition 1.5; " ++
        "IUT IV:2367-2375"
    status := Audit.VerificationStatus.interface
    note :=
      "TIGHTNESS: F5 card P <=> ABCConjecture (under the two F4 cards), so the F5 " ++
        "slot is exactly ABC-strength and cannot be weakened; ABCConjecture implies " ++
        "card P at every actual carrier.  (a) S3135PointLogShellFaithfulness: exact " ++
        "missing narrowed to a VALUE-GROUP level degree splitting; the available " ++
        "hull-stream principal-unit log image has degree 0 and cannot supply it; " ++
        "Z.log q generator + additive closure proved.  (b) " ++
        "S3135ScalingLogDegreeZero: normalized-lambda*O equation (III Rem 3.9.5(i); " ++
        "IV section 1 Prop 1.4); proved on the concrete model, named for the paper " ++
        "carrier (carrier fields only give <= 0).  (c) card P: exactly the IV " ++
        "Theorem A / [GenEll] numerical bridge; no weaker residual.  FINAL MINIMAL " ++
        "RESIDUAL: (a) value-group degree splitting; (b) zero normalized scaling " ++
        "log-degree for the paper carrier; (c) ABCHeightWeightAdditiveBoundV2.  All " ++
        "other chain components proved/consumed."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135PointLogShellFaithfulness (value-group level degree splitting)",
        "S3135ScalingLogDegreeZero (paper-carrier normalized scaling)",
        "ABCHeightWeightAdditiveBoundV2 (F5 card P / IV Theorem A)" ] }

#check s3135_pointWeightCard_iff_abcConjecture
#check s3135_pointWeightCard_of_abcConjecture
#check s3135_abcConjecture_of_threeResiduals
#check s3135TightnessReport

end LeanFormal.IUT.XiFPaper.S3135TightnessActual
end
