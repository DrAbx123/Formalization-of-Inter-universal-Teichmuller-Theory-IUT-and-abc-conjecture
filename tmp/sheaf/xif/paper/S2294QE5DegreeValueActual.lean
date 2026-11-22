import tmp.sheaf.xif.paper.S2289QE5DegreeActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2294QE5DegreeValueActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2270IntersectionDegreeActual
open LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
open LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
open Polynomial NumberField Module
/-- Parameterized exact-degree target for the absolute 5-division field. -/
def s2294QE5DegreeIs (n : Nat) : Prop :=
  Module.finrank ℚ s2289QE5 = n
/-- The degree is positive. -/
theorem s2294QE5_finrank_pos : 0 < Module.finrank ℚ s2289QE5 :=
  Module.finrank_pos
/-- The degree is the order of the absolute Galois group. -/
theorem s2294QE5_finrank_eq_card_aut :
    Module.finrank ℚ s2289QE5 = Nat.card (s2289QE5 ≃ₐ[ℚ] s2289QE5) :=
  s2289QE5_finrank_eq_card_aut
/-- The actual upper bound. -/
theorem s2294QE5_finrank_dvd_factorial :
    Module.finrank ℚ s2289QE5 ∣ Nat.factorial 12 :=
  s2289QE5_finrank_dvd_factorial
/-- A precise degree value gives the intersection-bot conclusion through the
degree product. -/
theorem s2294IntersectionIsBot_of_degreeProduct
    (h : Module.finrank ℚ ↥(s2253FImage ⊔ s2253LImage) =
      Module.finrank ℚ ↥s2253FImage * Module.finrank ℚ ↥s2253LImage) :
    s2253IntersectionIsBot :=
  s2289IntersectionIsBot_of_degreeProduct h
#print axioms s2294QE5_finrank_pos
#print axioms s2294QE5_finrank_eq_card_aut
#print axioms s2294QE5_finrank_dvd_factorial
#print axioms s2294IntersectionIsBot_of_degreeProduct
end LeanFormal.IUT.XiFPaper.S2294QE5DegreeValueActual
end
