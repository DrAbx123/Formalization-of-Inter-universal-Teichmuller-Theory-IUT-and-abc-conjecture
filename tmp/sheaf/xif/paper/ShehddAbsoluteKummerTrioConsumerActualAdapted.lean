import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerQuotient
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerContinuity

/-!
# ShehddAbsoluteKummerTrioConsumerActualAdapted — absolute/etale Kummer trio consumer

STEP 0 prior-art (reuse only; A475 search hit IUTII/Kummer tree assets):
* AbsoluteKummerInjection: RootsOfUnityFixed, rootsOfUnity_fixed_of_mem_base,
  chosenRoot_spec, absoluteKummerMap_eq_one_iff;
* AbsoluteKummerQuotient: nthPowerSubgroup, absoluteKummerMapQuotient_injective;
* AbsoluteKummerContinuity: isLocallyConstant_absoluteKummerMap, continuous_absoluteKummerMap.

This file packages the three proved facts (kernel criterion, quotient injectivity, local
constancy) as one consumer interface for the absolute Kummer class.  No new assumptions,
no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddAbsoluteKummerTrioConsumerActualAdapted

open LeanFormal.IUT

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]

/-- **PROVED consumer:** with fixed roots of unity, the absolute Kummer map's kernel is
exactly the n-th powers, the quotient map is injective, and the class is locally constant
in the Galois action. -/
theorem absoluteKummer_trio_summary
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    (∀ a : Kˣ,
        AbsoluteKummerInjection.absoluteKummerMap (K := K) (n := n) hμ a = 1 ↔
          ∃ b : Kˣ, b ^ n = a) ∧
      Function.Injective
        (AbsoluteKummerQuotient.absoluteKummerMapQuotient (K := K) (n := n) hμ) ∧
      (∀ a : Kˣ, IsLocallyConstant
        (fun σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K =>
          AbsoluteKummerInjection.absoluteKummerMap (K := K) (n := n) hμ a σ)) :=
  ⟨fun a => AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff hμ a,
    AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective hμ,
    fun a => AbsoluteKummerContinuity.isLocallyConstant_absoluteKummerMap hμ a⟩

/-- **PROVED consumer:** the n-th power subgroup consists exactly of the n-th powers. -/
theorem nthPowerSubgroup_mem_consumer (a : Kˣ) :
    a ∈ AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n) ↔
      ∃ b : Kˣ, b ^ n = a :=
  AbsoluteKummerQuotient.mem_nthPowerSubgroup a

/-- Row record: reused absolute-Kummer laws vs the consumer interface. -/
def absoluteKummerTrioRows : List (String × String × String) :=
  [ ("kernel criterion (absoluteKummerMap_eq_one_iff)", "REUSED PROVED", "AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff")
  , ("quotient injectivity", "REUSED PROVED", "AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective")
  , ("local constancy / continuity", "REUSED PROVED", "AbsoluteKummerContinuity.isLocallyConstant_absoluteKummerMap / continuous_absoluteKummerMap")
  , ("consumer trio interface", "COMPOSED PROVED", "absoluteKummer_trio_summary, nthPowerSubgroup_mem_consumer")
  , ("root-of-unity fixedness from base-image hypothesis", "REUSED PROVED", "AbsoluteKummerInjection.rootsOfUnity_fixed_of_mem_base (hypothesis form kept)") ]

theorem absoluteKummerTrioRows_length : absoluteKummerTrioRows.length = 5 := rfl

#check absoluteKummer_trio_summary
#check nthPowerSubgroup_mem_consumer
#check absoluteKummerTrioRows_length

end LeanFormal.IUT.XiFPaper.ShehddAbsoluteKummerTrioConsumerActualAdapted
end
