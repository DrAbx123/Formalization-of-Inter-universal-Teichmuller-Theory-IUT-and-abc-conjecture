import tmp.sheaf.xif.paper.S2595LResidueEquivActual
import tmp.sheaf.xif.paper.S2591LocalizedResidueEquivActual
import tmp.sheaf.xif.paper.S2574LocalizedP12Actual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2596FbarCompatibilityActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2591LocalizedResidueEquivActual
open LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

variable (D : S2587LocalizedResidueDataS)
  (h613 : (algebraMap ℤ S) (613 : ℤ) ∈ D.p)

/-- The integer model of psi5 over C = O_F'. -/
noncomputable def fC : C[X] := S2132Psi5Z.map (Int.castRingHom C)

/-- Reduction of fC at q = D.p.comap C S. -/
noncomputable def fbarC : (C ⧸ D.p.comap (algebraMap C S))[X] :=
  fC.map (Ideal.Quotient.mk (D.p.comap (algebraMap C S)))

lemma fC_map_S : fC.map (algebraMap C S) = S2132Psi5Z.map (Int.castRingHom S) := by
  unfold fC
  rw [Polynomial.map_map]
  congr 1
  ext x
  simp [IsScalarTower.algebraMap_apply ℤ C S]

/-- Base residue equivalence from S2591. -/
noncomputable def eBase : (C ⧸ D.p.comap (algebraMap C S)) ≃+* (S ⧸ D.p) :=
  S2591_localized_residue_equiv D h613

lemma eBase_comp_mk :
    (eBase D h613).toRingHom.comp (Ideal.Quotient.mk (D.p.comap (algebraMap C S))) =
      (Ideal.Quotient.mk D.p).comp (algebraMap C S) := by
  ext x
  simp [eBase, S2591_localized_residue_equiv, Ideal.quotientMap_mk]

lemma fbarC_map_eBase :
    (fbarC D).map (eBase D h613).toRingHom =
      (S2132Psi5Z.map (Int.castRingHom S)).map (Ideal.Quotient.mk D.p) := by
  unfold fbarC
  rw [Polynomial.map_map]
  rw [eBase_comp_mk D h613]
  rw [← Polynomial.map_map]
  congr 1
  exact (fC_map_S).trans (by rfl)

lemma fbarC_map_eBase' :
    (fbarC D).map (eBase D h613).toRingHom =
      S2574P.map (Ideal.Quotient.mk D.p) := by
  rw [fbarC_map_eBase]
  rfl

end LeanFormal.IUT.XiFPaper.S2596FbarCompatibilityActual
end