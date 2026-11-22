import tmp.sheaf.xif.paper.Mzk1B5FractionalCountNumDenActual
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Tactic

/-! # B5 finsum difference and summability bridges

* FinsumSubBridge: finite-support version of
    (∑ f) - (∑ g) = ∑ (f - g)
* count-weighted log sums have finite support and are Summable.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FinsumSummableActual

open IsDedekindDomain
open scoped BigOperators

variable {α : Type*}

/-- Finite-support Finsum subtraction bridge. -/
theorem finsum_sub_bridge {f g : α → Real}
    (hf : Function.HasFiniteSupport f) (hg : Function.HasFiniteSupport g) :
    (∑ᶠ i, f i) - (∑ᶠ i, g i) = ∑ᶠ i, (f i - g i) := by
  rw [finsum_sub_distrib hf hg]

variable (K : Type) [Field K] [NumberField K]

/-- Integer-ideal count-weighted log function has finite support. -/
theorem ideal_count_weighted_hasFiniteSupport
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0) :
    Function.HasFiniteSupport (fun v :
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Real) *
          Real.log (Ideal.absNorm v.asIdeal : Real)) := by
  classical
  rw [Function.HasFiniteSupport]
  have hev : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int) = 0 :=
    Associates.finite_factors (R := NumberField.RingOfIntegers K) hI
  have hfin : {v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) |
      ¬ ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int) = 0}.Finite := by
    simpa only [Filter.eventually_cofinite] using hev
  refine hfin.subset ?_
  intro v hv
  by_contra hcount
  have hc : ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Int) = 0 := by
    by_contra h
    exact hcount (by simpa using h)
  have hcR : ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Real) = 0 := by
    exact_mod_cast hc
  exact hv (by simp [hcR])

/-- Fractional-ideal count-weighted log function has finite support. -/
theorem fractional_count_weighted_hasFiniteSupport
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :
    Function.HasFiniteSupport (fun v :
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (FractionalIdeal.count K v I : Real) *
          Real.log (Ideal.absNorm v.asIdeal : Real)) := by
  classical
  rw [Function.HasFiniteSupport]
  have hev : ∀ᶠ v in Filter.cofinite, FractionalIdeal.count K v I = 0 :=
    FractionalIdeal.finite_factors (K := K) I
  have hfin : {v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) | ¬ FractionalIdeal.count K v I = 0}.Finite := by
    simpa only [Filter.eventually_cofinite] using hev
  refine hfin.subset ?_
  intro v hv
  by_contra hcount
  have hc : FractionalIdeal.count K v I = 0 := by
    by_contra h
    exact hcount (by simpa using h)
  have hcR : (FractionalIdeal.count K v I : Real) = 0 := by
    exact_mod_cast hc
  exact hv (by simp [hcR])

/-- Summability of the integer count-weighted log sum. -/
theorem ideal_count_weighted_summable
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : Real) *
        Real.log (Ideal.absNorm v.asIdeal : Real)) :=
  summable_of_hasFiniteSupport (ideal_count_weighted_hasFiniteSupport K I hI)

/-- Summability of the fractional count-weighted log sum. -/
theorem fractional_count_weighted_summable
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      (FractionalIdeal.count K v I : Real) *
        Real.log (Ideal.absNorm v.asIdeal : Real)) :=
  summable_of_hasFiniteSupport (fractional_count_weighted_hasFiniteSupport K I)

#check finsum_sub_bridge
#check ideal_count_weighted_hasFiniteSupport
#check fractional_count_weighted_hasFiniteSupport
#check ideal_count_weighted_summable
#check fractional_count_weighted_summable
end LeanFormal.IUT.XiFPaper.Mzk1B5FinsumSummableActual
end
