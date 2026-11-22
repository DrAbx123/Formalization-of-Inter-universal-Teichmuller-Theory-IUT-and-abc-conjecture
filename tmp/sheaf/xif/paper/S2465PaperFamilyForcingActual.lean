import tmp.sheaf.xif.paper.S2460PaperFamilyObstructionActual
import tmp.sheaf.xif.paper.S2452XiFCoverageActual

/-! # S2465: paper-family coverage forces a genuine new profile readout

Any S2452 paper family has `readout_eq` (nu_C = profile) and coverage of Q_C.
Exact coverage therefore forces an actual output whose profile value is Q_C;
signed coverage forces profile values arbitrarily above Q_C - eps.  If the only
available readout is the S2404 source scalar, S2460 obstruction applies.  Hence
a genuine new P_C/nu_C is required; this file proves the forcing lemmas, not a
paper-family inhabitant. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper.S2452XiFCoverageActual
open LeanFormal.IUT.XiFPaper.S2460PaperFamilyObstructionActual

universe u v w ux

namespace LeanFormal.IUT.XiFPaper.S2465PaperFamilyForcingActual

theorem s2465_family_exact_coverage_profile
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} {P : PaperSignedHull X Label}
    {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}
    (F : S2452PaperOutputFamily P R)
    (h : S2452ExactCoverage F.P_C F.nu_C F.Q_C) :
    ∃ D : ActualOutput R, D ∈ F.P_C ∧
      R.input.profile.logVolume D.source = F.Q_C := by
  rcases h with ⟨D, hD, hnu⟩
  exact ⟨D, hD, by rw [← F.readout_eq D hD, hnu]⟩

theorem s2465_family_signed_coverage_profile
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} {P : PaperSignedHull X Label}
    {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}
    (F : S2452PaperOutputFamily P R)
    (h : S2452SignedCoverage F.P_C F.nu_C F.Q_C) :
    ∀ eps > 0, ∃ D : ActualOutput R, D ∈ F.P_C ∧
      F.Q_C - eps ≤ R.input.profile.logVolume D.source := by
  intro eps heps
  obtain ⟨D, hD, hle⟩ := h eps heps
  rw [F.readout_eq D hD] at hle
  exact ⟨D, hD, hle⟩

theorem s2465_no_exact_family_of_source_readout
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] [Fintype Label]
    {X : Type ux} {P : PaperSignedHull X Label}
    {R : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice}
    (F : S2452PaperOutputFamily P R)
    {source paper : Real}
    (hsource : ∀ D, D ∈ F.P_C →
      R.input.profile.logVolume D.source = source)
    (hQ : F.Q_C = paper) (hne : source ≠ paper) :
    ¬ S2452ExactCoverage F.P_C F.nu_C F.Q_C := by
  intro hcov
  obtain ⟨D, hD, hprof⟩ := s2465_family_exact_coverage_profile F hcov
  exact hne (by rw [← hsource D hD, hprof, hQ])

#check s2465_family_exact_coverage_profile
#check s2465_family_signed_coverage_profile
#check s2465_no_exact_family_of_source_readout

end LeanFormal.IUT.XiFPaper.S2465PaperFamilyForcingActual
end
