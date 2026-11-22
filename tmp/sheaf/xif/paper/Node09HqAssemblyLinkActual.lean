import tmp.sheaf.xif.paper.Node09HqWeightedRegionActual
import tmp.sheaf.xif.paper.Mzk1Paper312AssemblyActual
import tmp.sheaf.xif.paper.Mzk1QVWeightedActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Node09HqWeightedRegionActual
open LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual

namespace LeanFormal.IUT.XiFPaper.Node09HqAssemblyLinkActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

/-- The weighted region component, with the actual log-index/diff reduction. -/
theorem weightedRegion_of_fiberMult
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ)
    (hbase : Nonempty (FinitePlaceQCandidate (nativeBadBasePlace X)))
    (hlogp : ∀ i : FinitePlaceAtPrime F p,
      Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) =
        Real.log (residueNormBase (b i).1))
    (hper : ∀ i : FinitePlaceAtPrime F p,
      fiberMult X b i / (Fdeg * (2 * l)) *
          Real.log (residueNormBase (b i).1) ≤
        actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i)) :
    Node09HqWeightedRegion X b Fdeg l actualLogIdx
      (fun i => logMu i - (1 / (2 * l)) * actualLogIdx i) :=
  ⟨hbase, actual_A_le_Lbar_add_Dbar_of_fiberMult (X := X) b Fdeg l logMu hlogp hper⟩

/-- The 3.12 assembly consumer for the mult-weighted fiber A-term. -/
theorem paper312_of_fiberMult_bounds
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logMu : FinitePlaceAtPrime F p → ℝ)
    (sFactor : ℝ) (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hA0 : 0 ≤ (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
      fiberMult X b i / Fdeg *
        Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)))
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
        (logMu i - (1 / (2 * l)) * actualLogIdx i)) := by
  exact Mzk1Paper312AssemblyActual.paper312_of_correction_bounds
    (fn := fun i => fiberMult X b i)
    (Fdeg := fun _ => Fdeg)
    (logp := fun i => Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ))
    (logIdx := actualLogIdx)
    (diff := fun i => logMu i - (1 / (2 * l)) * actualLogIdx i)
    hs0 hs1 hA0
    (fun i => by
      rw [hlogp i]
      exact hper i)


/-- 3.12 assembly consumer stated with the fiber-weighted `MqFiber`.
Uses Node09 `paper312_of_fiberMult_bounds` plus the pure sum rewrite
`log completionRationalPrime = log residueNormBase` (hlogp). -/
theorem paper312_of_MqFiber_bounds
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : Real) (logMu : FinitePlaceAtPrime F p → Real)
    (sFactor : Real) (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hA0 : 0 ≤ (1 / (2 * l)) * (1 / Fdeg) *
      LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual.MqFiber (p := p) X b)
    (hlogp : ∀ i : FinitePlaceAtPrime F p,
      Real.log (((completionRationalPrime (i.val)).val : Nat) : Real) =
        Real.log (residueNormBase ((b i).1)))
    (hper : ∀ i : FinitePlaceAtPrime F p,
      fiberMult X b i / (Fdeg * (2 * l)) *
          Real.log (residueNormBase ((b i).1)) ≤
        actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i)) :
    ExplicitPaper312Inequality sFactor
      ((1 / (2 * l)) * (1 / Fdeg) *
        LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual.MqFiber (p := p) X b)
      (∑ i : FinitePlaceAtPrime F p, actualLogIdx i)
      (∑ i : FinitePlaceAtPrime F p,
        (logMu i - (1 / (2 * l)) * actualLogIdx i)) := by
  have hsumlog : (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i / Fdeg * Real.log (residueNormBase ((b i).1))) =
      (1 / Fdeg) *
        LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual.MqFiber (p := p) X b := by
    rw [LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual.MqFiber, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsumlogp : (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : Nat) : Real)) =
      (1 / Fdeg) *
        LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual.MqFiber (p := p) X b := by
    rw [← hsumlog]
    apply Finset.sum_congr rfl
    intro i _
    rw [hlogp i]
  have hAeq : (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : Nat) : Real)) =
      (1 / (2 * l)) * (1 / Fdeg) *
        LeanFormal.IUT.XiFPaper.Mzk1QVWeightedActual.MqFiber (p := p) X b := by
    rw [hsumlogp]
    ring
  have hA0' : 0 ≤ (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : Nat) : Real)) := by
    rw [hAeq]
    exact hA0
  have h := paper312_of_fiberMult_bounds (X := X) b Fdeg l logMu sFactor hs0 hs1 hA0' hlogp hper
  rwa [hAeq] at h

end LeanFormal.IUT.XiFPaper.Node09HqAssemblyLinkActual
