import tmp.sheaf.xif.paper.S3132UniformFactorComparisonComponentActual
import tmp.sheaf.xif.paper.S3132UniformFiberMissingActual
import tmp.sheaf.xif.paper.S3132Task30ThetaHalfActual

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

namespace LeanFormal.IUT.XiFPaper.S3132ThetaHalfFinalCompositionActual

universe u v uv upi umon ui

/-!
# Theta-half final composition theorem (task-30/38/62/65 chain)

**Component, not a paper object.**  Owner: hull.  Consumers: mainline
FINAL-STATUS/ledger; lattice index; shehdd gate (no gate change needed).

Citable final composition for the fourth-triangle Theta half:

    [index equivalence  e : Fin D.rank ~ C3.tensorIndex]
  + [fiber comparison     MissingOneColumnC3FiberComparison ID C3 D e]
  + [normalization        MissingThetaLogNormalization ID C3 D]
  ==> MissingFourthTriangleThetaHalfReadout (I := ID) (I0 := I2) C3 D,

equivalently consuming the packaged uniform comparison
`MissingC3PacketUniformComparison`.  This composes the proved reductions
(task-38 transport/normalization reduction, task-62/65 fiber assembly, task-30
Theta-half record) into one citable theorem with the remaining inputs explicit.
The concrete packet side of the fiber comparison is fully proved
(S3132FiberExternalCompletionBridgeActual, S3132CompletionMapSurjectiveActual);
the abstract C3 tie is the data residual `MissingConcreteC3PlaceTie`
(S3132ConcreteC3PlaceTieActual).  Pages: III Prop 3.2(ii) 97-99; 3.7(ii),(v)
108-112; 3.9(i) p.115; Cor 3.12 corpus:10324-10353.
-/

/-- **Theta-half final composition (uniform form).** -/
theorem thetaHalfFinal_of_uniformComparison_and_normalization
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (M : MissingC3PacketUniformComparison ID C3 D)
    (N : MissingThetaLogNormalization ID C3 D) :
    MissingFourthTriangleThetaHalfReadout (I := ID) (I0 := I2) C3 D :=
  missingThetaHalf_of_transport_and_normalization ID C3 D M N

/-- **Theta-half final composition (index + fiber form).** -/
theorem thetaHalfFinal_of_index_and_fiber_and_normalization
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex)
    (Mf : MissingOneColumnC3FiberComparison ID C3 D e)
    (N : MissingThetaLogNormalization ID C3 D) :
    MissingFourthTriangleThetaHalfReadout (I := ID) (I0 := I2) C3 D :=
  missingThetaHalf_of_transport_and_normalization ID C3 D
    (missingC3PacketUniformComparison_of_index_and_fiber ID C3 D e Mf) N

#check thetaHalfFinal_of_uniformComparison_and_normalization
#check thetaHalfFinal_of_index_and_fiber_and_normalization

end LeanFormal.IUT.XiFPaper.S3132ThetaHalfFinalCompositionActual

end
