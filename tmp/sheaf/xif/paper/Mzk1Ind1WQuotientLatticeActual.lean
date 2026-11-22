import tmp.sheaf.xif.paper.Mzk1Ind1KernelIntegersActual
import tmp.sheaf.xif.paper.Mzk1Ind1ZpLatticeDivisibleActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1WQuotientLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1KernelIntegersActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ZpLatticeDivisibleActual

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Specialized lattice identification for the actual Gaussian completion at
the rational prime `5`.  `completionWQuotient` has no `p` argument; the
integer prime is fixed to `5`.  No inhabitant is supplied. -/
structure WQuotientLatticeIdentification where
  equiv : completionWQuotient ≃* ZpLattice 5 1

def WQuotientLatticeIdentificationRequired : Prop :=
  Nonempty WQuotientLatticeIdentification


#print axioms WQuotientLatticeIdentificationRequired
end LeanFormal.IUT.XiFPaper.Mzk1Ind1WQuotientLatticeActual