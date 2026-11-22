import tmp.sheaf.xif.paper.Node09ResidualInputsActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.Node09ResidualInputsActual
open LeanFormal.IUT.XiFPaper.Node09Paper312WeightActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual

namespace LeanFormal.IUT.XiFPaper.Node09FinalConditionalActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
variable [Fintype (FinitePlaceAtPrime F p)]

/-- Final conditional paper-3.12 endpoint: the residual inputs are explicit
fields of Node09Paper312Inputs, with no hidden axioms. -/
theorem final_paper312_conditional
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ) (sFactor : ℝ)
    (I : Node09Paper312Inputs X b Fdeg l logMu sFactor) :
    ExplicitPaper312Inequality sFactor
      ((1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        qVWeight X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)))
      (∑ i : FinitePlaceAtPrime F p, actualLogIdx i)
      (∑ i : FinitePlaceAtPrime F p,
        (logMu i - (1 / (2 * l)) * actualLogIdx i)) :=
  paper312_of_inputs X b Fdeg l logMu sFactor I

/-- Exact residual inputs and the consumer-side missing bridge. -/
def Node09FinalResidualMissing : List String :=
  [ "paper312 endpoint: final_paper312_conditional (conditional, inputs explicit)",
    "horder: (qVFamily X.S (b i)).order = 1 for every bad place (clause-B witness has no order spec)",
    "hcoef: CoeffComparison (actualFn i) Fdeg l (chosenA i) for every place (genuine 3.12 arithmetic; Mzk1PerPlaceInequalityActual records a counterexample, so not derivable unconditionally)",
    "hmu0: 0 <= logMu i; hl: 1 <= 2*l; hc: 1 <= chosenC i",
    "hlocal: localResidueDegree over Fmod equals actualFn; math actual for upper places (Node09HlocalUpperActual), Fmod=Q place equality/k transport explicit",
    "hbase: PadicValuedCoherence (p := pBase X) (K := NativeBaseCompletionRaw X); Qp normalization transport missing",
    "hlogp transport: rational-place residueNormBase donor actual (Node09AbsNormRatActual), Fmod=Q place/prime transport explicit (Node09HlogpTransportActual)",
    "IV/ABC consumer bridge: the external consumer is LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface (Cor312EpsilonArithmeticComparison), which needs the two named gap fields height_le_normalizedRegionVolume and regionVolume_le_normalizedWeight; there is no direct map from our ExplicitPaper312Inequality to that hull/epsilon interface yet" ]

end LeanFormal.IUT.XiFPaper.Node09FinalConditionalActual
