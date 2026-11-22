import tmp.sheaf.xif.paper.S2270IntersectionDegreeActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2056Psi5RootsPairsActual
import tmp.sheaf.xif.paper.S1723DegreeBoundActual
import Mathlib.FieldTheory.SplittingField.Construction
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2270IntersectionDegreeActual
open LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
open LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsPairsActual
open LeanFormal.IUT.XiFPaper.S1723DegreeBoundActual
/-- The absolute 5-division field Q(E[5]) = splitting field of psi5 over Q. -/
abbrev s2289QE5 : Type := Polynomial.SplittingField S2057Psi5Q
local instance : NumberField s2289QE5 where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance
local instance : IsSplittingField ℚ s2289QE5 S2057Psi5Q :=
  Polynomial.IsSplittingField.splittingField S2057Psi5Q
local instance : IsGalois ℚ s2289QE5 :=
  IsGalois.of_separable_splitting_field (p := S2057Psi5Q) S2057Psi5Q_separable
/-- psi5 has degree 12. -/
theorem s2289Psi5_natDegree : S2057Psi5Q.natDegree = 12 := by
  simpa [S2057Psi5Q, S2056Psi5] using S2056Psi5_natDegree
/-- The exact degree is the order of the absolute Galois group of Q(E[5]). -/
theorem s2289QE5_finrank_eq_card_aut :
    Module.finrank ℚ s2289QE5 = Nat.card (s2289QE5 ≃ₐ[ℚ] s2289QE5) :=
  (IsGalois.card_aut_eq_finrank ℚ s2289QE5).symm
/-- Actual upper bound: [Q(E[5]) : Q] divides 12!. -/
theorem s2289QE5_finrank_dvd_factorial :
    Module.finrank ℚ s2289QE5 ∣ Nat.factorial 12 := by
  have h := splittingField_finrank_dvd_factorial ℚ S2057Psi5Q
  rwa [s2289Psi5_natDegree] at h
/-- Degree product implies intersection bot for the F'/Q(E[5]) images. -/
theorem s2289IntersectionIsBot_of_degreeProduct
    (h : Module.finrank ℚ ↥(s2253FImage ⊔ s2253LImage) =
      Module.finrank ℚ ↥s2253FImage * Module.finrank ℚ ↥s2253LImage) :
    s2253IntersectionIsBot :=
  s2270IntersectionIsBot_of_degreeProduct h
#print axioms s2289Psi5_natDegree
#print axioms s2289QE5_finrank_eq_card_aut
#print axioms s2289QE5_finrank_dvd_factorial
#print axioms s2289IntersectionIsBot_of_degreeProduct
end LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
end
