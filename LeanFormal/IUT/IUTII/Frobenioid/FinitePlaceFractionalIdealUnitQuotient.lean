import LeanFormal.IUT.IUTII.Frobenioid.LocalFractionalIdealUnitQuotient
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs

/-!
# The local fractional-ideal dictionary at actual finite places

IUT III Example 3.6 uses the quotient of the multiplicative group of a local
field by its integral units. Here the local field and integer ring are the
actual valuation completion of a Dedekind fraction field and its integer ring.
The PID and fraction-field facts are supplied by existing proved instances.
The map from the global field is its canonical completion map.

This is the nonarchimedean local construction. It does not assert a global
Frobenioid equivalence or reconstruct a Hodge theater from a prime-strip.
-/

noncomputable section

open scoped nonZeroDivisors
open IsDedekindDomain

namespace LeanFormal.IUT.FinitePlaceFractionalIdealUnitQuotient

open LocalFractionalIdealUnitQuotient

variable (R K : Type*) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The local quotient in Example 3.6, interpreted in actual fractional ideals. -/
def completionUnitQuotientEquivFractionalIdeals :
    (v.adicCompletion K)ˣ ⧸
      integralUnitImage (v.adicCompletionIntegers K) (v.adicCompletion K) ≃*
        (FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K))ˣ :=
  localUnitQuotientEquivFractionalIdeals
    (v.adicCompletionIntegers K) (v.adicCompletion K)

/-- The actual global-to-local unit-class homomorphism beta_v of Example 3.6. -/
def completionUnitClass :
    Kˣ →* (v.adicCompletion K)ˣ ⧸
      integralUnitImage (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  (QuotientGroup.mk' _).comp
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom)

@[simp]
theorem completionUnitQuotientEquiv_completionUnitClass (x : Kˣ) :
    completionUnitQuotientEquivFractionalIdeals R K v (completionUnitClass R K v x) =
      toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K)
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) := rfl

/-- The actual local integrality criterion, expressed as membership in O_v. -/
theorem completionPrincipalIdeal_le_iff_integral
    (x y : (v.adicCompletion K)ˣ) :
    (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x :
      FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ≤
      (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) y :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ↔
      (x : v.adicCompletion K) / (y : v.adicCompletion K) ∈
        v.adicCompletionIntegers K := by
  rw [principalIdeal_le_iff_div_mem_integralImage]
  constructor
  · rintro ⟨z, hz⟩
    exact hz ▸ z.property
  · intro hz
    exact ⟨⟨_, hz⟩, rfl⟩

/-- The same criterion reads directly as a bound for the actual completion valuation. -/
theorem completionPrincipalIdeal_le_iff_valuation
    (x y : (v.adicCompletion K)ˣ) :
    (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) x :
      FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ≤
      (toPrincipalIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) y :
        FractionalIdeal (v.adicCompletionIntegers K)⁰ (v.adicCompletion K)) ↔
      Valued.v ((x : v.adicCompletion K) / (y : v.adicCompletion K)) ≤ 1 := by
  rw [completionPrincipalIdeal_le_iff_integral, HeightOneSpectrum.mem_adicCompletionIntegers]

end LeanFormal.IUT.FinitePlaceFractionalIdealUnitQuotient
