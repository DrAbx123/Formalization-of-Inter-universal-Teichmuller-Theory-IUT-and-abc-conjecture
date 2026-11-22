import tmp.sheaf.xif.paper.Node09HqAssemblyLinkActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.Node09HqAssemblyLinkActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual

namespace LeanFormal.IUT.XiFPaper.Node09ActualHypothesesActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

/-- Nonnegativity of the fiber A-term: actual qV multiplicities and prime logs
are nonnegative, and the normalization factors are positive. -/
theorem hA0_of_fiberMult
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (hFdeg : 0 < Fdeg) (hl : 0 < l)
    (hlogp_nonneg : ∀ i : FinitePlaceAtPrime F p,
      0 ≤ Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)) :
    0 ≤ (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
      fiberMult X b i / Fdeg *
        Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)) := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg ?_)
  intro i _
  have hfib : 0 ≤ fiberMult X b i := by
    unfold fiberMult
    exact_mod_cast Nat.zero_le (qVEffectiveMultiplicity X (b i))
  exact mul_nonneg (div_nonneg hfib hFdeg.le) (hlogp_nonneg i)

/-- The sFactor lower bound used by the 3.12 assembly. -/
theorem hs0_of_le (sFactor : ℝ) (h1 : 1 ≤ sFactor) : 0 ≤ sFactor - 1 := by
  linarith

/-- The sFactor upper bound used by the 3.12 assembly. -/
theorem hs1_of_le (sFactor : ℝ) (h2 : sFactor ≤ 2) : sFactor - 1 ≤ 1 := by
  linarith

/-- 3.12 assembly with the actual fiber multiplicities, given the remaining
base/hlogp/hper inputs (which are recorded as explicit missing). -/
theorem paper312_of_fiberMult_actual
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ)
    (sFactor : ℝ) (h1 : 1 ≤ sFactor) (h2 : sFactor ≤ 2)
    (hFdeg : 0 < Fdeg) (hl : 0 < l)
    (hlogp_nonneg : ∀ i : FinitePlaceAtPrime F p,
      0 ≤ Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ))
    (hlogp : ∀ i : FinitePlaceAtPrime F p,
      Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) =
        Real.log (residueNormBase (b i).1))
    (hper : ∀ i : FinitePlaceAtPrime F p,
      fiberMult X b i / (Fdeg * (2 * l)) *
          Real.log (residueNormBase (b i).1) ≤
        actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i)) :
    ExplicitPaper312Inequality sFactor
      ((1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)))
      (∑ i : FinitePlaceAtPrime F p, actualLogIdx i)
      (∑ i : FinitePlaceAtPrime F p,
        (logMu i - (1 / (2 * l)) * actualLogIdx i)) :=
  Node09HqAssemblyLinkActual.paper312_of_fiberMult_bounds (X := X)
    b Fdeg l logMu sFactor
    (hs0_of_le sFactor h1) (hs1_of_le sFactor h2)
    (hA0_of_fiberMult (X := X) b Fdeg l hFdeg hl hlogp_nonneg)
    hlogp hper

/-- Exact remaining missing inputs for the node09 hq/3.12 actual instantiation. -/
def Node09RemainingMissing : List String :=
  [ "hbase: Nonempty (FinitePlaceQCandidate (nativeBadBasePlace X)) via RelativeNormQProperties (needs actual Qp coherence/tower/finite/cast inhabitants)",
    "hlogp: residueNormBase (b i).1 = rational prime from index/bad-place compatibility (Fmod = Q)",
    "hper: paper 3.12 per-place mult-weighted inequality (not derivable from qVFamily_localLogMagnitude_eq alone)" ]

end LeanFormal.IUT.XiFPaper.Node09ActualHypothesesActual
