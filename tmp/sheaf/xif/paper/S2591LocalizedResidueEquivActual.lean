import tmp.sheaf.xif.paper.S2590LocalizedPrimeContractionActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S2591LocalizedResidueEquivActual

open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual

abbrev C : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev S : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S

noncomputable def S2591_localized_residue_equiv
    (D : S2587LocalizedResidueDataS)
    (h613 : algebraMap ℤ S (613 : ℤ) ∈ D.p) :
    (C ⧸ D.p.comap (algebraMap C S)) ≃+* (S ⧸ D.p) := by
  haveI hpmax : D.p.IsPrime := D.p_max.isPrime
  haveI hqmax : (D.p.comap (algebraMap C S)).IsMaximal := S2590_contraction_maximal D h613
  let φ : (C ⧸ D.p.comap (algebraMap C S)) →+* (S ⧸ D.p) :=
    Ideal.quotientMap D.p (algebraMap C S) le_rfl
  have hinj : Function.Injective φ := by
    exact Ideal.quotientMap_injective (I := D.p) (f := algebraMap C S)
  have hsurj : Function.Surjective φ := by
    exact IsLocalization.surjective_quotientMap_of_maximal_of_localization
      (M := Algebra.algebraMapSubmonoid C (Submonoid.powers (LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.c : ℤ)))
      (S := S) (I := D.p) (J := D.p.comap (algebraMap C S)) (H := le_rfl) hqmax
  exact RingEquiv.ofBijective φ ⟨hinj, hsurj⟩

#print axioms S2591_localized_residue_equiv

end LeanFormal.IUT.XiFPaper.S2591LocalizedResidueEquivActual
end
