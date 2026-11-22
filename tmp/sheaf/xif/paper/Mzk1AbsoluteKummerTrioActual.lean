import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerContinuity
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerQuotient

/-!
# Mzk1AbsoluteKummerTrioActual — typed bundle over the absolute Kummer trio (iuti-ii)

STEP 0 prior-art: AbsoluteKummerInjection / AbsoluteKummerContinuity / AbsoluteKummerQuotient
(tree proofs) -> REUSE; this file gives one typed interface bundling the trio's facts
(Kummer class, kernel = n-th powers, locally constant/continuous, quotient injection).

No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerTrioActual

open LeanFormal.IUT

/-- The absolute Kummer class map (tree: AbsoluteKummerInjection). -/
def kummerMapTrio :=
  @AbsoluteKummerInjection.absoluteKummerMap

/-- The kernel of the Kummer class is the subgroup of n-th powers (tree). -/
def kummerKernelTrio :=
  @AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff

/-- Locally constant in the Galois variable (tree). -/
def kummerLocallyConstantTrio :=
  @AbsoluteKummerContinuity.isLocallyConstant_absoluteKummerMap

/-- Continuous in the Galois variable (tree, discrete topology on the closure). -/
def kummerContinuousTrio :=
  @AbsoluteKummerContinuity.continuous_absoluteKummerMap

/-- The quotient Kummer map and its injectivity (tree). -/
def kummerQuotientTrio :=
  @AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective

/-- The subgroup of n-th powers in K^x (tree). -/
def nthPowerSubgroupTrio :=
  @AbsoluteKummerQuotient.nthPowerSubgroup

/-- Typed bundle over the absolute Kummer trio: the class map and the quotient injection. -/
structure AbsoluteKummerTrio (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) where
  kummerMap : Kˣ →* ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
    rootsOfUnity n (AlgebraicClosure K))
  quotientInjective : Function.Injective
    (AbsoluteKummerQuotient.absoluteKummerMapQuotient hμ)

/-- The trio bundle is inhabited by the tree data. -/
def absoluteKummerTrio (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    AbsoluteKummerTrio K n hμ where
  kummerMap := AbsoluteKummerInjection.absoluteKummerMap hμ
  quotientInjective := AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective hμ

/-- The trio bundle is nonempty. -/
theorem absoluteKummerTrio_nonempty (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    Nonempty (AbsoluteKummerTrio K n hμ) :=
  ⟨absoluteKummerTrio K n hμ⟩

/-- Trio rows: (fact, tree declaration, status). -/
def absoluteKummerTrioRows : List (String × String × String) :=
  [ ("absolute Kummer class map", "AbsoluteKummerInjection.absoluteKummerMap", "TREE PROOF"),
    ("kernel = n-th powers", "AbsoluteKummerInjection.absoluteKummerMap_eq_one_iff", "TREE PROOF"),
    ("locally constant in Galois variable", "AbsoluteKummerContinuity.isLocallyConstant_absoluteKummerMap", "TREE PROOF"),
    ("continuous in Galois variable", "AbsoluteKummerContinuity.continuous_absoluteKummerMap", "TREE PROOF"),
    ("quotient K^x/(K^x)^n injection", "AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective", "TREE PROOF"),
    ("n-th power subgroup", "AbsoluteKummerQuotient.nthPowerSubgroup", "TREE DEFINITION") ]

/-- The trio row record has six rows. -/
theorem absoluteKummerTrioRows_length : absoluteKummerTrioRows.length = 6 := rfl

#check kummerMapTrio
#check kummerKernelTrio
#check kummerLocallyConstantTrio
#check kummerContinuousTrio
#check kummerQuotientTrio
#check nthPowerSubgroupTrio
#check AbsoluteKummerTrio
#check absoluteKummerTrio_nonempty
#check absoluteKummerTrioRows_length

end LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerTrioActual
end
