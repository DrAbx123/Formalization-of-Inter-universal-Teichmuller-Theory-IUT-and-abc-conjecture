import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip
import tmp.sheaf.xif.paper.Mzk1Ind1AlgebraicUnitQuotientActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1LocalMonActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Ind1AlgebraicUnitQuotientActual

/-- The actual local FPrimeStrip `Mon` is the algebraic-closure unit group. -/
theorem localFPrimeStrip_Mon_eq (v : RationalPrimePlace) [Fact (Nat.Prime v.1)] :
    localFPrimeStrip.Mon v = (AlgebraicClosure ℚ_[v.1])ˣ := by
  letI := Fact.mk v.2
  rfl

#print axioms localFPrimeStrip_Mon_eq
end LeanFormal.IUT.XiFPaper.Mzk1Ind1LocalMonActual