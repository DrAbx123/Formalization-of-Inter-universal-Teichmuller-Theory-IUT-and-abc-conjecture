import tmp.sheaf.xif.paper.S2535LocalizedIntegralClosureActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace LeanFormal.IUT.XiFPaper.S2536LocalizedPowersActual
open LeanFormal.IUT.XiFPaper.S2535LocalizedIntegralClosureActual
theorem isIntegralClosure_localization_powers
    {A C K L R S : Type*}
    [CommRing A] [CommRing C] [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDomain A] [IsDomain C]
    [Algebra A K] [Algebra A L] [Algebra A C] [Algebra C L]
    [FaithfulSMul A C]
    [IsIntegralClosure C A L] [IsFractionRing C L]
    (a : A) (ha : a ∈ nonZeroDivisors A)
    [Algebra A R] [IsLocalization (Submonoid.powers a) R] [Algebra A S]
    [Algebra C S]
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers a)) S]
    [Algebra R S]
    [Algebra R L] [Algebra S L]
    (hACL : IsScalarTower A C L) (hARS : IsScalarTower A R S)
    (hACS : IsScalarTower A C S) (hARL : IsScalarTower A R L)
    (hCSL : IsScalarTower C S L) (hRSL : IsScalarTower R S L)
    :
    IsIntegralClosure S R L := by
  letI := hACL
  letI := hARS
  letI := hACS
  letI := hARL
  letI := hCSL
  letI := hRSL
  exact isIntegralClosure_localization
    (A := A) (C := C) (K := K) (L := L) (R := R) (S := S)
    (M := Submonoid.powers a) (hM := (Submonoid.powers_le).mpr ha)
#print axioms isIntegralClosure_localization_powers
end LeanFormal.IUT.XiFPaper.S2536LocalizedPowersActual
end