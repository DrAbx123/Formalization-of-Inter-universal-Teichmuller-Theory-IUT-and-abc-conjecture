import tmp.sheaf.xif.paper.S2590LocalizedPrimeContractionActual
import tmp.sheaf.xif.paper.S2587LocalizedResidueDataActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2591LocalizedResidueIsoActual

open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

variable (D : S2587LocalizedResidueDataS)
  (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p)

include D h613

/-- The contraction of the localized prime to O_F'. -/
noncomputable def S2591q : Ideal C := D.p.comap (algebraMap C S)

lemma S2591q_max : (S2591q D).IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2590LocalizedPrimeContractionActual.S2590_contraction_maximal D h613

lemma S2591q_eq_comap :
    S2591q D = Ideal.comap (algebraMap C S) D.p := rfl

/-- The residue map (O_F'/q) -> (S/p). -/
noncomputable def S2591map : C ⧸ S2591q D →+* S ⧸ D.p :=
  Ideal.quotientMap D.p (algebraMap C S)
    (le_of_eq (S2591q_eq_comap D).symm)

lemma S2591map_surjective : Function.Surjective (S2591map D) := by
  haveI : D.p.IsPrime := D.p_max.isPrime
  have h := IsLocalization.surjective_quotientMap_of_maximal_of_localization
    (M := Algebra.algebraMapSubmonoid C M) (S := S)
    (I := D.p) (J := S2591q D) (H := le_of_eq (S2591q_eq_comap D).symm)
    (S2591q_max D h613)
  simpa [S2591map] using h

lemma S2591map_injective : Function.Injective (S2591map D) := by
  apply Ideal.quotientMap_injective'
  exact le_of_eq (S2591q_eq_comap D)

/-- The localized residue equivalence (O_F'/q) = (S/p). -/
noncomputable def S2591ResidueEquiv : (C ⧸ S2591q D) ≃+* (S ⧸ D.p) :=
  RingEquiv.ofBijective (S2591map D)
    ⟨S2591map_injective D, S2591map_surjective D h613⟩

end LeanFormal.IUT.XiFPaper.S2591LocalizedResidueIsoActual
end