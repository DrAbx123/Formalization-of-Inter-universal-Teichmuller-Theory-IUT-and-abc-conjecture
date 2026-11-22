import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerQuotient

/-!
# ShehddAbsoluteKummerKernelConsumerActual — absolute Kummer kernel = n-th powers consumer

STEP 0 prior-art (reuse only):
* AbsoluteKummerInjection: absoluteKummerMap (Kˣ →* Gal →* rootsOfUnity),
  absoluteKummerMap_eq_one_iff (kernel criterion);
* AbsoluteKummerQuotient: nthPowerSubgroup = (powMonoidHom n).range,
  mem_nthPowerSubgroup, absoluteKummerMapQuotient_injective.

This file identifies the kernel of the absolute Kummer map with the n-th power subgroup
and packages the quotient injectivity as a consumer.  No new assumptions, no
sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddAbsoluteKummerKernelConsumerActual

open LeanFormal.IUT

variable {K : Type*} [Field K] [CharZero K] {n : ℕ} [NeZero n]

/-- **PROVED consumer:** the kernel of the absolute Kummer map is exactly the n-th power
subgroup. -/
theorem absoluteKummerMap_ker_eq_nthPowerSubgroup
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    MonoidHom.ker (AbsoluteKummerInjection.absoluteKummerMap (K := K) (n := n) hμ) =
      AbsoluteKummerQuotient.nthPowerSubgroup (K := K) (n := n) := by
  ext a
  rw [MonoidHom.mem_ker,
    AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff hμ a,
    AbsoluteKummerQuotient.mem_nthPowerSubgroup]

/-- **PROVED consumer:** elementwise kernel characterization and injectivity of the
quotient map. -/
theorem absoluteKummer_kernel_and_quotient_consumer
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    (∀ a : Kˣ,
        a ∈ MonoidHom.ker
          (AbsoluteKummerInjection.absoluteKummerMap (K := K) (n := n) hμ) ↔
          ∃ b : Kˣ, b ^ n = a) ∧
      Function.Injective
        (AbsoluteKummerQuotient.absoluteKummerMapQuotient (K := K) (n := n) hμ) :=
  ⟨fun a => (absoluteKummerMap_ker_eq_nthPowerSubgroup hμ).symm ▸
    (AbsoluteKummerQuotient.mem_nthPowerSubgroup a),
    AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective hμ⟩

/-- Row record: reused absolute Kummer assets vs the consumer interface. -/
def absoluteKummerKernelRows : List (String × String × String) :=
  [ ("kernel criterion", "REUSED PROVED", "AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff")
  , ("n-th power subgroup membership", "REUSED PROVED", "AbsoluteKummerQuotient.mem_nthPowerSubgroup")
  , ("quotient injectivity", "REUSED PROVED", "AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective")
  , ("kernel = n-th powers", "COMPOSED PROVED", "absoluteKummerMap_ker_eq_nthPowerSubgroup")
  , ("kernel + quotient consumer bundle", "COMPOSED PROVED", "absoluteKummer_kernel_and_quotient_consumer") ]

theorem absoluteKummerKernelRows_length : absoluteKummerKernelRows.length = 5 := rfl

#check absoluteKummerMap_ker_eq_nthPowerSubgroup
#check absoluteKummer_kernel_and_quotient_consumer
#check absoluteKummerKernelRows_length

end LeanFormal.IUT.XiFPaper.ShehddAbsoluteKummerKernelConsumerActual
end
