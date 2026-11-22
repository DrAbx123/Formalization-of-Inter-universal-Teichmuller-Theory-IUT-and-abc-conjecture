import tmp.sheaf.xif.paper.S3078dGeneratingPresieve

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3050ConnectedSite
open LeanFormal.IUT.XiFPaper.S3078dGeneratingPresieve
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3078dSupportActual

/-- Every sieve is itself a generating presieve: the openness condition is the
only extra datum. -/
noncomputable def S3078dGeneratingPresieveOfOpen {S : S3050ConnectedScheme}
    {T : Over S} (R : Sieve T)
    (hopen : forall {Y : Over S} (f : Y ⟶ T), R.arrows f ->
      AlgebraicGeometry.IsOpenImmersion
        (Over.Hom.left (Over.Hom.left f).hom)) :
    S3078dGeneratingPresieve R where
  P := R.arrows
  le_R := by rw [Sieve.generate_sieve]
  open_arrow := hopen

/-- Exact openness condition needed for the extraction. -/
def S3078dAllArrowsOpen : Prop :=
  forall (S : S3050ConnectedScheme) (T : Over S) (R : Sieve T),
    R ∈ S3050ConnectedSite.over S T ->
      forall {Y : Over S} (f : Y ⟶ T), R.arrows f ->
        AlgebraicGeometry.IsOpenImmersion
          (Over.Hom.left (Over.Hom.left f).hom)

theorem S3078dExistsGeneratingPresieve_of_open
    (hopen : S3078dAllArrowsOpen) : S3078dExistsGeneratingPresieve := by
  intro S T R hR
  exact ⟨S3078dGeneratingPresieveOfOpen R (hopen S T R hR)⟩

#check S3078dGeneratingPresieveOfOpen
#check S3078dAllArrowsOpen
#check S3078dExistsGeneratingPresieve_of_open
#print axioms S3078dGeneratingPresieveOfOpen
#print axioms S3078dExistsGeneratingPresieve_of_open

end LeanFormal.IUT.XiFPaper.S3078dSupportActual
end