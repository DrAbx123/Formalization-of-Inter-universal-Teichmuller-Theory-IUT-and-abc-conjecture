import tmp.sheaf.xif.paper.S2592GenericLocalizedResidueIsoActual
import tmp.sheaf.xif.paper.S2593ConditionalChainActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2594LP0PActual

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual

abbrev OL : Type := NumberField.RingOfIntegers S2057FiveDivisionField
abbrev T : Type := Localization.Away (algebraMap C OL Cden)

/-- If `P0` avoids `Cden`, its localization `P = P0.map T` is prime and lies over `P0`. -/
noncomputable def S2594P (P0 : Ideal OL) : Ideal T := P0.map (algebraMap OL T)

lemma S2594P_prime (P0 : Ideal OL) [P0.IsPrime]
    (hC0 : algebraMap C OL Cden ∈ P0 → False) : (S2594P P0).IsPrime := by
  apply IsLocalization.isPrime_of_isPrime_disjoint
    (M := Submonoid.powers (algebraMap C OL Cden)) (S := T) P0 ‹P0.IsPrime›
  rw [Set.disjoint_left]
  intro x hx hxP0
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x (algebraMap C OL Cden)).mp hx
  exact hC0 ((‹P0.IsPrime›).mem_of_pow_mem n hxP0)

lemma S2594P_under (P0 : Ideal OL) [P0.IsPrime]
    (hC0 : algebraMap C OL Cden ∈ P0 → False) :
    (S2594P P0).comap (algebraMap OL T) = P0 := by
  apply IsLocalization.under_map_of_isPrime_disjoint
    (M := Submonoid.powers (algebraMap C OL Cden)) (S := T) ‹P0.IsPrime›
  rw [Set.disjoint_left]
  intro x hx hxP0
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x (algebraMap C OL Cden)).mp hx
  exact hC0 ((‹P0.IsPrime›).mem_of_pow_mem n hxP0)

/-- L-side localized residue equivalence, conditional on P0 avoiding Cden. -/
noncomputable def S2594LResidueEquiv (P0 : Ideal OL) [P0.IsMaximal]
    (hC0 : algebraMap C OL Cden ∈ P0 → False) :
    (OL ⧸ P0) ≃+* (T ⧸ S2594P P0) := by
  haveI : (S2594P P0).IsPrime := S2594P_prime P0 hC0
  exact localizedResidueEquiv
    (M := Submonoid.powers (algebraMap C OL Cden)) (T := T) P0 (S2594P P0)
    (S2594P_under P0 hC0)

end LeanFormal.IUT.XiFPaper.S2594LP0PActual
end