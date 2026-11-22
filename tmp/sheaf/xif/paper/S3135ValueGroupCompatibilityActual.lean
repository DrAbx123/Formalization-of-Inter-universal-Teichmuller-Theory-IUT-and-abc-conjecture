import tmp.sheaf.xif.paper.S3135ValueGroupDegreeUnconditionalActual
import tmp.sheaf.xif.paper.S3135LogShellValueGroupActual
import tmp.sheaf.xif.paper.S3135ScalingNormalizationActual
import tmp.sheaf.xif.paper.S3135ResidualNarrowingActual

/-!
# task-72: F4.a reduced to ONE compatibility lemma (mainline route recorded)

**Reduction file, not a paper object.**  Mainline's route note (FINAL-STATUS A10):
define the identification on the normalized generator by definitional agreement, so the
only remaining content is the degree-commutation compatibility between the actual
source realization and the actual realified degree:

`S3135ValueGroupDegreeCompatibility X I v R vp` :
`forall r : Multiplicative R, ofAdd (logDegreeAt (R.posRealAction r)) =
 globalDegree (normalizedRealifiedPrimePowerHom vp r)`

This file proves that this single Prop **closes F4.a**:
* `s3135_valueGroupFaithfulness_of_compatibility`: the actual source realization is
  degree-faithful (the section field with definitional agreement);
* `s3135_pointFaithfulness_of_compatibility`: the F4 card-(1) reduced form
  `S3135PointLogShellFaithfulness`;
* `s3135_actualF4_of_compatibility`: the actual F4 height clause at the constructed
  point, given the scaling-zero card.

So `S3135ValueMonoidIdentification` assembles from TWO ingredients: this
compatibility lemma (degree side; IUT II section 1; IUT III Remark 3.9.4; [AbsTopIII]
Proposition 5.8(ii)) and the definitional generator agreement (no proof content).
The genuine remaining paper input is exactly the compatibility.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3135ValueGroupCompatibilityActual

/-- **F4.a's single compatibility lemma**: the actual source realization's log-degree
equals the actual realified degree on the normalized generator ray. -/
def S3135ValueGroupDegreeCompatibility
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v)
    (vp : GlobalPrimeIndex (X := X)) : Prop :=
  ∀ r : Multiplicative ℝ,
    Multiplicative.ofAdd (I.logDegreeAt 0 0 v (R.posRealAction r)) =
      globalDegree (X := X) (normalizedRealifiedPrimePowerHom (X := X) vp r)

/-- The compatibility lemma is exactly the degree-faithfulness of the actual source
realization (the generator-agreement field is definitional). -/
theorem s3135_valueGroupFaithfulness_of_compatibility
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (vp : GlobalPrimeIndex (X := X))
    (h : S3135ValueGroupDegreeCompatibility X I v R vp) :
    S3135ValueGroupDegreeFaithfulness I v R := by
  intro x
  have hh := h (Multiplicative.ofAdd x)
  rw [normalizedRealifiedPrimePowerHom_degree (X := X) vp] at hh
  exact congrArg Multiplicative.toAdd hh

/-- F4 card-(1) reduced form from the compatibility lemma. -/
theorem s3135_pointFaithfulness_of_compatibility
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (vp : GlobalPrimeIndex (X := X))
    (h : S3135ValueGroupDegreeCompatibility X I v R vp) :
    S3135PointLogShellFaithfulness I v R :=
  s3135_pointFaithfulness_of_valueGroupFaithfulness I v R
    (s3135_valueGroupFaithfulness_of_compatibility X I v R vp h)

/-- The actual F4 height clause at the constructed point from the compatibility lemma
plus the scaling-zero card. -/
theorem s3135_actualF4_of_compatibility
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l')
    (D : I.SourceUnitRegionHaarData v R n)
    (vp : GlobalPrimeIndex (X := X))
    (h : S3135ValueGroupDegreeCompatibility X I v R vp)
    (hzero : S3135ScalingLogDegreeZero I v R n D) :
    FrontierHeightComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) := by
  have hpt := s3135_pointFaithfulness_of_compatibility X I v R vp h
  have hnorm : ∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps :=
    s3135_normalization_of_scalingLogDegreeZero I v R n D hzero
  exact s3135_actualF4_of_pointFaithfulness I v R n D hpt hnorm

#check S3135ValueGroupDegreeCompatibility
#check s3135_valueGroupFaithfulness_of_compatibility
#check s3135_pointFaithfulness_of_compatibility
#check s3135_actualF4_of_compatibility

end LeanFormal.IUT.XiFPaper.S3135ValueGroupCompatibilityActual
end
