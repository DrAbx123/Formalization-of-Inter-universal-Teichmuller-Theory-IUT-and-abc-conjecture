import tmp.sheaf.xif.paper.S2591LocalizedResidueEquivActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual

noncomputable def localizedResidueEquiv
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (M : Submonoid R) [IsLocalization M T]
    (I : Ideal R) (P : Ideal T) [I.IsMaximal] [P.IsPrime]
    (hunder : P.comap (algebraMap R T) = I) :
    (R ⧸ I) ≃+* (T ⧸ P) := by
  haveI hImax : I.IsMaximal := inferInstance
  let phi : (R ⧸ I) →+* (T ⧸ P) :=
    Ideal.quotientMap P (algebraMap R T) (le_of_eq hunder.symm)
  have hinj : Function.Injective phi := by
    exact Ideal.quotientMap_injective' (le_of_eq hunder)
  have hsurj : Function.Surjective phi := by
    have hpmax : (P.under R).IsMaximal := by
      simpa [Ideal.under, hunder] using hImax
    exact IsLocalization.surjective_quotientMap_of_maximal_of_localization
      (M := M) (S := T) (I := P) (J := I) (H := le_of_eq hunder.symm) hpmax
  exact RingEquiv.ofBijective phi ⟨hinj, hsurj⟩

end LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual
end