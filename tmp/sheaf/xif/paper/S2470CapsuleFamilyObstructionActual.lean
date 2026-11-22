import tmp.sheaf.xif.paper.S2451ProcessionAverageActual
import tmp.sheaf.xif.paper.S2460PaperFamilyObstructionActual

/-! # S2470: concrete non-singleton capsule-family obstruction

The actual paper capsule index `S2451PaperCapsuleLabel D` is non-singleton and
carries the actual diagonal q-pilot readout `paperQPilotLogVolume D`.  With the
corrected paper scalar `-C/(4l)` this family cannot have exact or signed-epsilon
coverage.  This is a concrete counterexample to the natural capsule family, not
an interface. -/

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
open LeanFormal.IUT.XiFPaper.S2451ProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S2452XiFCoverageActual
open LeanFormal.IUT.XiFPaper.S2460PaperFamilyObstructionActual

local instance s2470GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2470FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S2470CapsuleFamilyObstructionActual

/-- The actual capsule index is non-singleton for l >= 5. -/
theorem s2470_capsule_card_ge_two (D : S1895PaperInput) :
    2 ≤ Fintype.card (S2451PaperCapsuleLabel D) := by
  rw [S2451PaperCapsuleLabel_card]
  have hge : 5 ≤ D.l.value := D.l.ge_five
  omega

/-- Exact coverage of the corrected paper scalar by the actual diagonal
capsule family is impossible. -/
theorem s2470_capsule_exact_coverage_impossible (D : S1895PaperInput) :
    ¬ S2452ExactCoverage
        (Set.univ : Set (S2451PaperCapsuleLabel D))
        (fun _ => paperQPilotLogVolume D)
        (paperNormalizedSignedLog D) := by
  apply s2460_exact_coverage_obstruction
      (P_C := (Set.univ : Set (S2451PaperCapsuleLabel D)))
      (nu_C := fun _ => paperQPilotLogVolume D)
      (profile := fun _ => sourceQPilotSignedLog (paperInput D).initial)
      (Q_C := paperNormalizedSignedLog D)
      (source := sourceQPilotSignedLog (paperInput D).initial)
      (paper := paperNormalizedSignedLog D)
  · intro x hx
    exact paperQPilotLogVolume_eq_signedLog D
  · intro x hx
    rfl
  · rfl
  · exact ne_of_lt (s2460_source_lt_paper D)

/-- Signed-epsilon coverage is also impossible for the diagonal capsule family. -/
theorem s2470_capsule_signed_coverage_impossible (D : S1895PaperInput) :
    ¬ S2452SignedCoverage
        (Set.univ : Set (S2451PaperCapsuleLabel D))
        (fun _ => paperQPilotLogVolume D)
        (paperNormalizedSignedLog D) := by
  intro hcov
  apply s2460_signed_coverage_obstruction
      (P_C := (Set.univ : Set (S2451PaperCapsuleLabel D)))
      (nu_C := fun _ => paperQPilotLogVolume D)
      (profile := fun _ => sourceQPilotSignedLog (paperInput D).initial)
      (Q_C := paperNormalizedSignedLog D)
      (source := sourceQPilotSignedLog (paperInput D).initial)
      (paper := paperNormalizedSignedLog D)
  · intro x hx
    exact paperQPilotLogVolume_eq_signedLog D
  · intro x hx
    rfl
  · rfl
  · exact s2460_source_lt_paper D
  · exact hcov

#check s2470_capsule_card_ge_two
#check s2470_capsule_exact_coverage_impossible
#check s2470_capsule_signed_coverage_impossible

end LeanFormal.IUT.XiFPaper.S2470CapsuleFamilyObstructionActual
end
