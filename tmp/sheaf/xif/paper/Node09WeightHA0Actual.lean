import tmp.sheaf.xif.paper.Node09Paper312WeightActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Node09Paper312WeightActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual

namespace LeanFormal.IUT.XiFPaper.Node09WeightHA0Actual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
variable [Fintype (FinitePlaceAtPrime F p)]

/-- Nonnegativity of the actual qV-weighted A-term. -/
theorem hA0_of_qVWeight
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg : FinitePlaceAtPrime F p → ℝ) (l : ℝ)
    (logp : FinitePlaceAtPrime F p → ℝ)
    (hFdeg : ∀ i, 0 < Fdeg i) (hl : 0 < l)
    (hlogp_nonneg : ∀ i, 0 ≤ logp i) :
    0 ≤ (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
      qVWeight X b i / Fdeg i * logp i) := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg ?_)
  intro i _
  have hw : 0 ≤ qVWeight X b i := by
    unfold qVWeight
    exact_mod_cast Nat.zero_le (qVEffectiveMultiplicity X (b i))
  exact mul_nonneg (div_nonneg hw (hFdeg i).le) (hlogp_nonneg i)

/-- The actual qV-weighted 3.12 assembly: hA0 is instantiated; hper remains the
exact per-place arithmetic input. -/
theorem paper312_of_qVWeight_actual
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg : FinitePlaceAtPrime F p → ℝ) (l : ℝ)
    (logp logIdx diff : FinitePlaceAtPrime F p → ℝ)
    (sFactor : ℝ) (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hFdeg : ∀ i, 0 < Fdeg i) (hl : 0 < l)
    (hlogp_nonneg : ∀ i, 0 ≤ logp i)
    (hper : ∀ i : FinitePlaceAtPrime F p,
      qVWeight X b i / (Fdeg i * (2 * l)) * logp i ≤ logIdx i + diff i) :
    ExplicitPaper312Inequality sFactor
      ((1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        qVWeight X b i / Fdeg i * logp i))
      (∑ i : FinitePlaceAtPrime F p, logIdx i)
      (∑ i : FinitePlaceAtPrime F p, diff i) :=
  paper312_of_qVWeight (X := X) b Fdeg l logp logIdx diff sFactor hs0 hs1
    (hA0_of_qVWeight (X := X) b Fdeg l logp hFdeg hl hlogp_nonneg) hper

end LeanFormal.IUT.XiFPaper.Node09WeightHA0Actual
