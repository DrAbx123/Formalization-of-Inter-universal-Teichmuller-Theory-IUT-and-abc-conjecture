import tmp.sheaf.xif.paper.S2450GeneralNormalizationActual
import tmp.sheaf.xif.paper.S2452XiFCoverageActual

/-! # S2460: obstruction for paper-family construction via S2404 readout

If every output readout is the S2404/S2391 source scalar, then the corrected
paper normalization `-C/(4l)` (S2450) cannot be covered exactly or by signed
epsilon when the source scalar is strictly below it.  This proves the old
S2404-readout route cannot produce the paper family; actual P_C/nu_C remain
missing.  No interface is asserted as actual. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S2441C9PaperCarrierActual
open LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

local instance s2460GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2460FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S2460PaperFamilyObstructionActual

/-- Generic exact-coverage obstruction: if all readouts equal `source` and
`Q_C = paper`, then exact coverage is impossible when `source ≠ paper`. -/
theorem s2460_exact_coverage_obstruction
    {A : Type*} {P_C : Set A} {nu_C profile : A → Real}
    {Q_C source paper : Real}
    (hread : ∀ D, D ∈ P_C → nu_C D = profile D)
    (hprof : ∀ D, D ∈ P_C → profile D = source)
    (hQ : Q_C = paper) (hne : source ≠ paper)
    (hcov : ∃ D, D ∈ P_C ∧ nu_C D = Q_C) : False := by
  obtain ⟨D, hD, hnu⟩ := hcov
  exact hne (by rw [← hprof D hD, ← hread D hD, hnu, hQ])

/-- Signed-epsilon coverage is also impossible if every readout equals a
source value strictly below the paper scalar. -/
theorem s2460_signed_coverage_obstruction
    {A : Type*} {P_C : Set A} {nu_C profile : A → Real}
    {Q_C source paper : Real}
    (hread : ∀ D, D ∈ P_C → nu_C D = profile D)
    (hprof : ∀ D, D ∈ P_C → profile D = source)
    (hQ : Q_C = paper) (hlt : source < paper)
    (hcov : ∀ eps > 0, ∃ D, D ∈ P_C ∧ Q_C - eps ≤ nu_C D) : False := by
  have hpos : 0 < (paper - source) / 2 := by linarith
  obtain ⟨D, hD, hle⟩ := hcov ((paper - source) / 2) hpos
  have hnu : nu_C D = source := by
    rw [hread D hD, hprof D hD]
  rw [hQ, hnu] at hle
  linarith

/-- The concrete corrected paper scalar is strictly below the raw source
scalar: `-C < -C/(4l)`. -/
theorem s2460_source_lt_paper (D : S1895PaperInput) :
    sourceQPilotSignedLog (paperInput D).initial <
      paperNormalizedSignedLog D := by
  have hsrc := s2441_concrete_normalization D
  have hpaper := paperNormalizedSignedLog_eq D
  have hlog : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have horder : 0 < (S1487Cand.order : Real) :=
    by exact_mod_cast S1487Cand.order_pos
  have hC : 0 < (S1487Cand.order : Real) * Real.log 5 := mul_pos horder hlog
  have hl : 2 < 2 * (D.l.value : Real) := by
    have hge : (5 : Real) ≤ (D.l.value : Real) := by
      exact_mod_cast D.l.ge_five
    nlinarith
  rw [hsrc, hpaper]
  have hden : 0 < 4 * (D.l.value : Real) := by nlinarith
  have hfrac : ((S1487Cand.order : Real) * Real.log 5) /
      (4 * (D.l.value : Real)) <
        (S1487Cand.order : Real) * Real.log 5 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

#check s2460_exact_coverage_obstruction
#check s2460_signed_coverage_obstruction
#check s2460_source_lt_paper

end LeanFormal.IUT.XiFPaper.S2460PaperFamilyObstructionActual
end
