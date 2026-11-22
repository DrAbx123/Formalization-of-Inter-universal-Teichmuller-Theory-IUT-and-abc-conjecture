import tmp.sheaf.xif.paper.Node09HmultReductionActual
import tmp.sheaf.xif.paper.Node09WeightHA0Actual
import tmp.sheaf.xif.paper.Node09HlogpTransportActual

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
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Node09HmultReductionActual
open LeanFormal.IUT.XiFPaper.Node09Paper312WeightActual
open LeanFormal.IUT.XiFPaper.Node09WeightHA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual

namespace LeanFormal.IUT.XiFPaper.Node09ResidualInputsActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
variable [Fintype (FinitePlaceAtPrime F p)]

/-- The explicit residual inputs for the conditional paper-3.12 conclusion:
horder, hlocal, hcoef, hmu0, hl, hc, plus the positivity/sign inputs. -/
structure Node09Paper312Inputs
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ) (sFactor : ℝ) : Prop where
  hFdeg : 0 < Fdeg
  hl_pos : 0 < l
  hs0 : 0 ≤ sFactor - 1
  hs1 : sFactor - 1 ≤ 1
  hlogp_nonneg : ∀ i : FinitePlaceAtPrime F p,
    0 ≤ Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)
  horder : ∀ i : FinitePlaceAtPrime F p, (qVFamily X.S (b i)).order = 1
  hlocal : ∀ i : FinitePlaceAtPrime F p,
    (localResidueDegree (k := X.S.arithmetic.Fmod)
      ((nativeBadLift X.S).lift (b i)) : ℝ) = (actualFn i : ℝ)
  hcoef : ∀ i : FinitePlaceAtPrime F p,
    CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ))
  hmu0 : ∀ i : FinitePlaceAtPrime F p, 0 ≤ logMu i
  hl : 1 ≤ 2 * l
  hc : ∀ i : FinitePlaceAtPrime F p, 1 ≤ chosenC i

/-- Conditional paper 3.12 conclusion from the exact residual inputs. -/
theorem paper312_of_inputs
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ) (sFactor : ℝ)
    (I : Node09Paper312Inputs X b Fdeg l logMu sFactor) :
    ExplicitPaper312Inequality sFactor
      ((1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        qVWeight X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)))
      (∑ i : FinitePlaceAtPrime F p, actualLogIdx i)
      (∑ i : FinitePlaceAtPrime F p,
        (logMu i - (1 / (2 * l)) * actualLogIdx i)) := by
  have hper := hper_of_horder (X := X) b
    (fun i => qVWeight X b i) Fdeg l logMu
    I.hcoef I.hmu0 I.hl I.hc
    (fun _ => rfl) I.horder I.hlocal
  exact paper312_of_qVWeight (X := X) b (fun _ => Fdeg) l
    (fun i => Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ))
    actualLogIdx (fun i => logMu i - (1 / (2 * l)) * actualLogIdx i)
    sFactor I.hs0 I.hs1
    (hA0_of_qVWeight (X := X) b (fun _ => Fdeg) l
      (fun i => Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ))
      (fun _ => I.hFdeg) I.hl_pos I.hlogp_nonneg)
    hper

/-- Exact residual inputs not included in the paper312 conditional theorem. -/
def Node09ResidualMissing : List String :=
  [ "hbase: PadicValuedCoherence (p := pBase X) (K := NativeBaseCompletionRaw X) (Qp normalization transport)",
    "hlogp transport: rational-place residueNormBase donor actual; Fmod=Q place/prime transport explicit (Node09HlogpTransportActual)",
    "horder/hcoef/hmu0/hl/hc/hlocal are explicit fields of Node09Paper312Inputs, not derived" ]

end LeanFormal.IUT.XiFPaper.Node09ResidualInputsActual
