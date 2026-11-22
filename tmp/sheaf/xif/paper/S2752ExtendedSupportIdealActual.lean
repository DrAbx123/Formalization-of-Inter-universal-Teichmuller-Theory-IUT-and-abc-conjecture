import tmp.sheaf.xif.paper.S2743SupportIdealAbsNormLowerActual
import tmp.sheaf.xif.paper.S2751ExtendedAbsNormActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2738PrimeOverFamilyActual
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2743SupportIdealAbsNormLowerActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2752ExtendedSupportIdealActual

variable {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]

/-- The extended support ideal `J = qPilotIdeal * supportIdeal(a,c)`. -/
noncomputable def S2752J
    (Q : Ideal (NumberField.RingOfIntegers K)) (x : ℚ) :
    Ideal (NumberField.RingOfIntegers K) :=
  Q * supportIdeal (K := K) x

/-- Subtype/Finset coercion bridge: the product over the support subtype is the
product over the actual prime-support Finset. -/
theorem S2752_prod_supportIndex_eq_finset_prod (x : ℚ) :
    (∏ i : SupportIndex x, (i : Nat)) =
      ∏ p ∈ arithmeticPrimeSupport x, p := by
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach (s := arithmeticPrimeSupport x) (fun p : Nat => p)

/-- The support ideal divides the extended `J`. -/
theorem S2752_supportIdeal_dvd_J
    (Q : Ideal (NumberField.RingOfIntegers K)) (x : ℚ) :
    supportIdeal (K := K) x ∣ S2752J (K := K) Q x := by
  refine ⟨Q, ?_⟩
  rw [S2752J, mul_comm]

/-- absNorm of the extended `J` factors through qPilotIdeal and supportIdeal. -/
theorem S2752J_absNorm
    (Q : Ideal (NumberField.RingOfIntegers K)) (x : ℚ) :
    Ideal.absNorm (S2752J (K := K) Q x) =
      Ideal.absNorm Q * Ideal.absNorm (supportIdeal (K := K) x) :=
  map_mul Ideal.absNorm Q (supportIdeal (K := K) x)

/-- The support-product lower bound transfers to the extended `J`:
`∏ p ≤ absNorm supportIdeal ≤ absNorm J` whenever all factors are nonzero. -/
theorem S2752_prod_support_le_J_absNorm
    (Q : Ideal (NumberField.RingOfIntegers K)) (x : ℚ)
    (hQ : Ideal.absNorm Q ≠ 0) :
    (∏ i : SupportIndex x, i.1) ≤
      Ideal.absNorm (S2752J (K := K) Q x) := by
  calc
    (∏ i : SupportIndex x, i.1) ≤
        Ideal.absNorm (supportIdeal (K := K) x) :=
      S2743_prod_support_le_supportIdeal_absNorm x
    _ ≤ Ideal.absNorm Q * Ideal.absNorm (supportIdeal (K := K) x) := by
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hQ)
    _ = Ideal.absNorm (S2752J (K := K) Q x) :=
      (S2752J_absNorm Q x).symm

#check S2752J
#check S2752_prod_support_le_J_absNorm
#print axioms S2752_prod_support_le_J_absNorm

end LeanFormal.IUT.XiFPaper.S2752ExtendedSupportIdealActual
end
