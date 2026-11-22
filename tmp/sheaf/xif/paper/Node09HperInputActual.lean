import tmp.sheaf.xif.paper.Mzk1ActualRamifiedDataActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual

namespace LeanFormal.IUT.XiFPaper.Node09HperInputActual

variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

/-- hper for a multiplicity, reduced to the actual residue-degree per-place bound
and the identification with actualFn. -/
theorem hper_of_mult_eq_actualFn
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ)))
    (hmu0 : ∀ i : FinitePlaceAtPrime F p, 0 ≤ logMu i)
    (hl : 1 ≤ 2 * l)
    (hc : ∀ i : FinitePlaceAtPrime F p, 1 ≤ chosenC i)
    (hmult : ∀ i : FinitePlaceAtPrime F p, mult i = (actualFn i : ℝ)) :
    ∀ i : FinitePlaceAtPrime F p,
      mult i / (Fdeg * (2 * l)) *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) ≤
        actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i) := by
  intro i
  rw [hmult i]
  exact actualDataCore_perPlace_bounds Fdeg l logMu mult hcoef hmu0 hl hc i

/-- Exact remaining missing for the paper-3.12 per-place input (hper). -/
def Node09HperRemainingMissing : List String :=
  [ "hmult: mult i = actualFn i (qV order = 1 and localResidueDegree = actualFn; otherwise the mult-weighted per-place bound must be supplied separately)",
    "hcoef: CoeffComparison (actualFn i) Fdeg l (chosenA i) for every place (genuine arithmetic content, assumed explicitly in Mzk1PerPlaceInequalityActual)",
    "hmu0: 0 <= logMu i for every place",
    "hl: 1 <= 2*l",
    "hc: 1 <= chosenC i for every place" ]

end LeanFormal.IUT.XiFPaper.Node09HperInputActual
