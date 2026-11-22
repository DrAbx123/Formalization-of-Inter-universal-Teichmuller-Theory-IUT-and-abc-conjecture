import tmp.sheaf.xif.paper.S3135TightnessActual

/-!
# task-33: narrowing of the value-group degree splitting and the lambda-scaling normalization

This file reduces the two remaining F4/F5 residuals to smaller, paper-labelled
objects, with the missing data isolated exactly.

## (a) Value-group degree splitting: reduced to a section + agreement

The exact residual `S3135PointLogShellFaithfulness` asks that the actual source
realization `R.posRealAction : Multiplicative Real ->* Mon v` be degree-faithful
(IUT II Example 1.8(ix), iut2.txt:2402-2409; [AbsTopIII] Proposition 5.8(ii);
Remark 3.9.4).  It is proved here to be **equivalent** to the conjunction of

* a degree **section** `phi : Multiplicative Real ->* Mon v` of the actual degree
  homomorphism (`S3135ValueGroupDegreeSection`: a value-group copy of `Real` inside
  the actual value monoid), and
* **agreement of the actual source realization with that section**
  (`S3135SourceRealizationAgreesWithSection`: the actual q-pilot/theta image is the
  value-group element of the section).

So the missing object is not "faithfulness of the given action" as a black box: it is
split into (i) the actual value-group embedding of `Real` in the value monoid, and
(ii) the identification of the source realization with it (Remark 3.9.4).  Hull
confirmed (message 2026-11-10) that their additive unit/principal-unit log-shell has
degree/norm `0`, hence cannot supply (i) for `x != 0`; candidate actual objects for
(i) are the valuation/degree-lattice side: `IntegralLogShellIndexArithmetic`
(integral log-shell lattice/index arithmetic) and the q-pilot q-parameter objects
(`S3134QParameter` family, constraint of IUT I Definition 3.1(iv) and IUT II
Remark 3.9.4).

## (b) lambda-scaling normalization: named actual Haar equality

The second residual `S3135ScalingLogDegreeZero` is the `lambda·O` normalization of
IUT III Remark 3.9.5(i) / IUT IV section 1 Proposition 1.4 (iut4.txt:671-760).  The
required actual statement is recorded as
`S3135ScaledHaarNormalizedEquality`: the actual normalized log-volume of the scaled
unit region equals that of the unit region (procession-normalized Haar
translation/disintegration, IUT III Proposition 3.9(i)).  Hull confirmed (message
2026-11-10) that this normalized equality is not derivable from the current actual
Haar data (which supplies `addHaar` on the actual integral log-shell, unit-reference
mass `1`, hull finiteness and real log-volume readouts, but no lambda-scaling
disintegration); it is an additional normalized-Haar theorem with the stated page
reference.  The value-carrier field only gives `logDegree(scaling) <= 0`, so the
zero equation cannot be derived from the fields alone.
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
open LeanFormal.IUT.XiFPaper.S3135TightnessActual

namespace LeanFormal.IUT.XiFPaper.S3135ResidualNarrowingActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)

/-- **Sub-card (a1): the actual value monoid admits a degree section** — a monoid
homomorphism from the positive reals whose degree is the identity, i.e. a value-group
copy of `Real` inside the actual value monoid (IUT II Example 1.8(ix);
[AbsTopIII] Proposition 5.8(ii); Remark 3.9.4).  The missing actual object is this
embedding on the valuation/degree side. -/
def S3135ValueGroupDegreeSection : Prop :=
  ∃ phi : Multiplicative ℝ →* I.ValueMonoidAt 0 0 v,
    ∀ x : ℝ, I.logDegreeAt 0 0 v (phi (Multiplicative.ofAdd x)) = x

/-- **Card (1) is exactly: a degree section plus agreement of the actual
realization with it.**  (Sub-card (a2), agreement of the actual source realization
with a degree section, is the second conjunct below: the actual q-pilot/theta value
is the value-group element of the section, Remark 3.9.4.)  Forward: the given realization itself is the section.
Backward: the agreement transports faithfulness to the actual realization. -/
theorem s3135_pointFaithfulness_iff_section_and_agreement :
    S3135ValueGroupDegreeFaithfulness I v R ↔
      ∃ phi : Multiplicative ℝ →* I.ValueMonoidAt 0 0 v,
        (∀ x : ℝ, I.logDegreeAt 0 0 v (phi (Multiplicative.ofAdd x)) = x) ∧
          (∀ x : ℝ, R.posRealAction (Multiplicative.ofAdd x) =
            phi (Multiplicative.ofAdd x)) := by
  constructor
  · intro h
    exact ⟨R.posRealAction, h, fun _ => rfl⟩
  · rintro ⟨phi, hphi, hagree⟩ x
    rw [hagree x]
    exact hphi x

/-- (a1) is necessary for card (1): the actual realization exhibits the degree
section. -/
theorem s3135_valueGroupDegreeSection_of_faithfulness
    (h : S3135ValueGroupDegreeFaithfulness I v R) :
    S3135ValueGroupDegreeSection (I := I) (v := v) :=
  ⟨R.posRealAction, h⟩

/-- **Residual (b) as a named actual Haar normalization equality**: the normalized
log-volume of the scaled unit region equals that of the unit region — the
procession-normalized `lambda·O` Haar normalization (IUT III Proposition 3.9(i);
Remark 3.9.5(i); IUT IV section 1 Proposition 1.4, iut4.txt:671-760). -/
def S3135ScaledHaarNormalizedEquality : Prop :=
  I.sourceSetVolume v (scaledRegionImage D.scaling D.unitRegion) =
    I.sourceSetVolume v D.unitRegion

/-- The residual (b) itself, restated as the scalar degree equation. -/
theorem s3135_scalingLogDegreeZero_iff_degree_eq_zero :
    S3135ScalingLogDegreeZero I v R n D ↔ I.sourceLocalLogDegree v D.scaling = 0 :=
  Iff.rfl

/-- **task-33 residual report.**  (a) is reduced to the pair
`S3135ValueGroupDegreeSection` + `S3135SourceRealizationAgreesWithSection`;
(b) is reduced to the named actual normalized-Haar equality
`S3135ScaledHaarNormalizedEquality` (plus the scalar degree equation, which is
equivalent to the residual by definition). -/
def s3135ResidualNarrowingReport : Audit.Obligation :=
  { id := "IUT-IV.f4-f5-residual-narrowing-valuegroup-haar"
    source :=
      "IUT II Example 1.8(ix) iut2.txt:2402-2409; [AbsTopIII] Proposition 5.8(ii); " ++
        "Remark 3.9.4; IUT III Proposition 3.9(i); IUT III Remark 3.9.5(i); " ++
        "IUT IV section 1 Proposition 1.4 (iut4.txt:671-760)"
    status := Audit.VerificationStatus.interface
    note :=
      "REDUCED: (a) S3135PointLogShellFaithfulness <=> existence of a value-group " ++
        "degree section phi (Real-copy in the actual value monoid, degree = id) plus " ++
        "agreement of the actual source realization with phi " ++
        "(s3135_pointFaithfulness_iff_section_and_agreement).  Hull confirmed the " ++
        "additive principal-unit log-shell has degree 0 and cannot supply the " ++
        "section for x != 0; candidates for the actual section are the " ++
        "valuation/degree-lattice objects (IntegralLogShellIndexArithmetic, q-pilot " ++
        "q-parameter S3134QParameter family).  (b) " ++
        "S3135ScalingLogDegreeZero is the scalar normalization equation, reduced to " ++
        "the named actual normalized-Haar equality " ++
        "S3135ScaledHaarNormalizedEquality (lambda*O normalization, III Prop 3.9(i)); " ++
        "hull confirmed it is not derivable from current Haar data.  (c) unchanged: " ++
        "F5 card P <=> ABCConjecture (tight, task-31)."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface", "ABC.proof-target" ]
    sorryItems :=
      [ "S3135ValueGroupDegreeSection (actual value-group degree section)",
        "S3135SourceRealizationAgreesWithSection (source realization = section)",
        "S3135ScaledHaarNormalizedEquality (lambda*O normalized Haar equality)",
        "ABCHeightWeightAdditiveBoundV2 (F5 card P, ABC-strength)" ] }

#check s3135_pointFaithfulness_iff_section_and_agreement
#check s3135_valueGroupDegreeSection_of_faithfulness
#check S3135ScaledHaarNormalizedEquality
#check s3135ResidualNarrowingReport

end LeanFormal.IUT.XiFPaper.S3135ResidualNarrowingActual
end
