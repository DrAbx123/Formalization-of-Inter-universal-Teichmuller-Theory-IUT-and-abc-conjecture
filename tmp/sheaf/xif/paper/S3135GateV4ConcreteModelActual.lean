import tmp.sheaf.xif.paper.S3135ScalingActualModelActual
import tmp.sheaf.xif.paper.S3135FinalAssemblyGateV3Actual
import tmp.sheaf.xif.paper.S3135PaperLambdaConcreteActual

/-!
# GATE v4 (I): CONCRETE NORMALIZED MODEL instance

**Model-instance gate, explicitly labelled; NOT the general acceptance theorem.**
Gate v3 (`S3135FinalAssemblyGateV3Actual`) remains the general conditional theorem;
this file adds the concrete normalized model instance only.

## Shape (I)

Carrier restricted to the tree's concrete normalized model
(`sourceHaarActualOriginalInput (S)`, image realization
`sourceHaarActualImageRealization`, point `()`, arbitrary theta-pilot carrier `n`,
arbitrary Haar datum `D`).  On this carrier:

* `hzero` is **DISCHARGED** by the citable
  `sourceHaarActual_scalingLogDegree_zero` (task-17: for every `D` on the concrete
  model the normalized scaling log-degree is zero);
* `hb : S3135CompletionBaseFieldUnitScalar (1 : concreteLogShellField)` is the
  concrete-model paper input (proved: `s3135_concrete_scaling_unitScalar`), and it
  **yields** the set-level preservation of the integral log-shell by the concrete
  scaling (used in the conclusion);
* `hpt` (F4.a) and `hP` (F4.c.cardP) remain hypotheses.

## INPUT FLAG (honest)

The concrete model sets `scaling := 1`
(`SourceUnitRegionHaarDataActual.lean:421`), i.e. the concrete-model instance
realizes the TRIVIAL scaling.  It therefore certifies the machinery and the
paper-input shape, but it is a SPECIAL case: it does not realize a nontrivial
procession scaling such as `(2l)^{-1}` or log-shell-scale powers.  In particular
`(logShellScale p)^{-1}` has norm `p` and is NOT of the form `algebraMap z` with
`z` a `Z_p`-unit, so a nontrivial paper scaling with `|lambda| = 1` would need its
actual unit scalar recorded.  The general gate keeps F4 (b) as the flagged paper
input; this instance is not evidence for the general paper claim.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
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
open LeanFormal.IUT.XiFPaper.S3135FinalAssemblyGateV3Actual
open LeanFormal.IUT.XiFPaper.S3135PaperLambdaWiringActual
open LeanFormal.IUT.XiFPaper.S3135PaperLambdaConcreteActual
open LeanFormal.IUT.XiFPaper.S3135ScalingActualModelActual

namespace LeanFormal.IUT.XiFPaper.S3135GateV4ConcreteModelActual

universe ua

/-- **GATE v4 (I), concrete normalized model instance.**  `hzero` discharged by
`sourceHaarActual_scalingLogDegree_zero`; `hb` is the concrete paper input and
yields the integral-log-shell preservation; F4.a and F4.c.cardP remain hypotheses. -/
theorem s3135_finalAssemblyGateV4_concreteModel
    {l : PrimeGeFive} (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l)
    (D : (sourceHaarActualOriginalInput (l := l) S).SourceUnitRegionHaarData ()
      (sourceHaarActualImageRealization (l := l) S) n)
    (hpt : S3135PointLogShellFaithfulness
      (sourceHaarActualOriginalInput (l := l) S) ()
      (sourceHaarActualImageRealization (l := l) S))
    (hb : S3135CompletionBaseFieldUnitScalar (1 : concreteLogShellField))
    (hP : S3135ActualPointWeightCard
      (sourceHaarActualOriginalInput (l := l) S) ()
      (sourceHaarActualImageRealization (l := l) S) n D
      (abcSourcePoint (sourceHaarActualOriginalInput (l := l) S) ()
        (sourceHaarActualImageRealization (l := l) S))) :
    ABCConjecture ∧
      (fun x : concreteLogShellField => (1 : concreteLogShellField) * x) ''
          ((integralLogShell (K := concreteLogShellField)
            (p := concreteRationalPrime)) : Set concreteLogShellField) =
        ((integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime)) : Set concreteLogShellField) := by
  refine ⟨?_, ?_⟩
  · exact s3135_finalAssemblyGateV3
      (sourceHaarActualOriginalInput (l := l) S) () 
      (sourceHaarActualImageRealization (l := l) S) n D hpt
      (sourceHaarActual_scalingLogDegree_zero (l := l) S n D) hP
  · exact s3135_integralLogShell_image_of_baseFieldUnitScalar (1 : concreteLogShellField) hb

#check s3135_finalAssemblyGateV4_concreteModel

end LeanFormal.IUT.XiFPaper.S3135GateV4ConcreteModelActual
end
