import tmp.sheaf.xif.paper.Node09HperInputActual
import tmp.sheaf.xif.paper.Node09HresidueDegreeActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import tmp.sheaf.n8.closure.NativeBadLiftActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
open LeanFormal.IUT.XiFPaper.Node09HperInputActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual

namespace LeanFormal.IUT.XiFPaper.Node09HmultReductionActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

/-- hmult reduces to the qV order-1 input and the relative-residue-degree/actualFn
identification at the corresponding place. -/
theorem hmult_of_horder
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (mult : FinitePlaceAtPrime F p → ℝ)
    (i : FinitePlaceAtPrime F p)
    (hmult : mult i = (qVEffectiveMultiplicity X (b i) : ℝ))
    (horder : (qVFamily X.S (b i)).order = 1)
    (hlocal : (localResidueDegree (k := X.S.arithmetic.Fmod)
      ((nativeBadLift X.S).lift (b i)) : ℝ) = (actualFn i : ℝ)) :
    mult i = (actualFn i : ℝ) := by
  rw [hmult]
  unfold qVEffectiveMultiplicity
  rw [horder, Nat.one_mul]
  exact hlocal

/-- hper reduces to horder + hlocal + the per-place arithmetic inputs. -/
theorem hper_of_horder
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (mult : FinitePlaceAtPrime F p → ℝ)
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ)))
    (hmu0 : ∀ i : FinitePlaceAtPrime F p, 0 ≤ logMu i)
    (hl : 1 ≤ 2 * l)
    (hc : ∀ i : FinitePlaceAtPrime F p, 1 ≤ chosenC i)
    (hmult : ∀ i : FinitePlaceAtPrime F p,
      mult i = (qVEffectiveMultiplicity X (b i) : ℝ))
    (horder : ∀ i : FinitePlaceAtPrime F p, (qVFamily X.S (b i)).order = 1)
    (hlocal : ∀ i : FinitePlaceAtPrime F p,
      (localResidueDegree (k := X.S.arithmetic.Fmod)
        ((nativeBadLift X.S).lift (b i)) : ℝ) = (actualFn i : ℝ)) :
    ∀ i : FinitePlaceAtPrime F p,
      mult i / (Fdeg * (2 * l)) *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) ≤
        actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i) :=
  hper_of_mult_eq_actualFn (F := F) (p := p) Fdeg l logMu mult
    hcoef hmu0 hl hc
    (fun i => hmult_of_horder X b mult i (hmult i) (horder i) (hlocal i))

/-- Exact remaining missing for the hmult/hper reduction. -/
def Node09HmultRemainingMissing : List String :=
  [ "horder: (qVFamily X.S (b i)).order = 1 (clause-B witness has no order spec)",
    "hmult: mult i = qVEffectiveMultiplicity X (b i) (definitional choice of mult)",
    "hlocal: (localResidueDegree (k := Fmod) ((nativeBadLift X.S).lift (b i)) : R) = (actualFn i : R) (Fmod=Q transport; base-rational-place case DONE as localResidueDegree_rat_eq_actualFn)",
    "hcoef: CoeffComparison (actualFn i) Fdeg l (chosenA i) for every place",
    "hmu0: 0 <= logMu i for every place",
    "hl: 1 <= 2*l; hc: 1 <= chosenC i for every place" ]

end LeanFormal.IUT.XiFPaper.Node09HmultReductionActual
