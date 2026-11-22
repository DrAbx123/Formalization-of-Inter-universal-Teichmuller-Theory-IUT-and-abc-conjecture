import tmp.sheaf.xif.paper.S3132ThetaHalfFinalCompositionActual
import tmp.sheaf.xif.paper.S3132ConcreteC3PlaceTieActual
import tmp.sheaf.xif.paper.S3132CompletionMapSurjectiveActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3132UniformFactorComparisonComponentActual
open LeanFormal.IUT.XiFPaper.S3132UniformFiberMissingActual
open LeanFormal.IUT.XiFPaper.S3132Task30ThetaHalfActual
open LeanFormal.IUT.XiFPaper.S3132ThetaHalfFinalCompositionActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteC3PlaceTieActual
open LeanFormal.IUT.XiFPaper.S3132CompletionMapSurjectiveActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaHalfConcreteFinalActual

universe u v uv upi umon ui

/-!
# Theta-half final composition for the concrete Example 3.6 model

**Component, not a paper object.**  Owner: hull.  Consumers: mainline
FINAL-STATUS/ledger; lattice index.

Concrete-model final composition.  The residual inputs are exactly:

1. `hTie : MissingConcreteC3PlaceTie I2 C3` — the data-only model tie
   (`I2.initial.arithmetic.Fmod = packetNumberField`, `C3.p = 5`,
   `HEq (c3LogShellPlace C3 i) packetFinitePlace`); everything on the concrete
   packet side is proved: comap/prime, e = f = 1, local finrank one, completionMap
   injective AND surjective (S3132CompletionMapSurjectiveActual), and
   `concreteGaussianFiberRingEquiv_unconditional : Completion (comap packetFinitePlace) ≃+*
   packetFiniteCompletion`;
2. `M` — the packaged uniform comparison (from the index equivalence and the
   concrete fiber data), or `e/Mf` in the split form;
3. `N : MissingThetaLogNormalization` — the normalization identification
   (task-38/41/61 residuals: V-form/canonical + exact factor).

This file states the citable conditional final theorem; the only data residual is
the model tie, and the remaining mathematical identifications are the named
normalization ones.  Pages: III Prop 3.2(ii) 97-99; 3.7(ii),(v) 108-112; 3.9(i)
p.115; Cor 3.12 corpus:10324-10353.
-/

/-- **Concrete-model Theta-half final theorem** (uniform form). -/
theorem thetaHalfFinalConcrete_of_modelTie
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (hTie : MissingConcreteC3PlaceTie I2 C3)
    (M : MissingC3PacketUniformComparison ID C3 D)
    (N : MissingThetaLogNormalization ID C3 D) :
    MissingFourthTriangleThetaHalfReadout (I := ID) (I0 := I2) C3 D :=
  thetaHalfFinal_of_uniformComparison_and_normalization ID C3 D M N

/-- **Concrete-model Theta-half final theorem** (index + fiber form). -/
theorem thetaHalfFinalConcrete_of_modelTie_index_fiber
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (hTie : MissingConcreteC3PlaceTie I2 C3)
    (e : Fin D.rank ≃ C3.tensorIndex)
    (Mf : MissingOneColumnC3FiberComparison ID C3 D e)
    (N : MissingThetaLogNormalization ID C3 D) :
    MissingFourthTriangleThetaHalfReadout (I := ID) (I0 := I2) C3 D :=
  thetaHalfFinal_of_index_and_fiber_and_normalization ID C3 D e Mf N

#check thetaHalfFinalConcrete_of_modelTie
#check thetaHalfFinalConcrete_of_modelTie_index_fiber

end LeanFormal.IUT.XiFPaper.S3132ThetaHalfConcreteFinalActual

end
