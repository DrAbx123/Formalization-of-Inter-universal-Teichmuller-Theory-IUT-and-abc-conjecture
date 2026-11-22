import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Actual rational-side Gaussian base-q value 1/5 (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: task-51 M2 residual, lattice R1,
mainline M2.

Source: IUT I, Example 3.2, (iv) (q_v parameters); IUT I, Definition 3.1, (b),
(c) (bad-place selection, residue characteristic 5); IUT III, Definition 3.8,
(i), p. 112-113.

This file constructs the ACTUAL rational p-adic base-q value for the Gaussian
model: the scalar 5 in Q_5 has norm exactly 1/5.  The proof uses only
Padic.norm_eq_zpow_neg_valuation and Padic.valuation_p (no sorry-tainted or
uncompiled input).

What remains exact missing for M2: the transport of this actual Q_5 scalar to
the Gaussian Fmod completion, and the clause-B/Tate q identification (D4, IUT I
Definition 3.1(b), Example 3.2(iv)), recorded as S3133GaussianBaseQDescentMissing
in S3133M2BaseQReductionActual and S3133GaussianBaseQTransportMissing
(see ledger 02:18/02:33).  S2684GaussianFiveQCandidateActual is PARKED
(Lead option b) and is not imported here.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S3133GaussianBaseQRationalActual

local instance s3133RationalFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The actual rational p-adic base scalar 5 in Q_5. -/
noncomputable def S3133RationalFiveQ : ℚ_[5] :=
  ((5 : ℚ) : ℚ_[5])

/-- The actual rational base scalar has norm exactly 1/5. -/
theorem S3133RationalFiveQ_norm :
    ‖S3133RationalFiveQ‖ = ((5 : Real)⁻¹) := by
  unfold S3133RationalFiveQ
  rw [Padic.norm_eq_zpow_neg_valuation
    (by norm_num : ((5 : ℚ) : ℚ_[5]) ≠ 0)]
  rw [show (((5 : ℚ) : ℚ_[5])).valuation = 1 from Padic.valuation_p]
  norm_num

/-- The actual rational base scalar is nonzero. -/
theorem S3133RationalFiveQ_ne_zero : S3133RationalFiveQ ≠ 0 := by
  unfold S3133RationalFiveQ
  norm_num

end LeanFormal.IUT.XiFPaper.S3133GaussianBaseQRationalActual
