/- U-R packet definitions (small): one actual packet, q-root lattice, theta
source span, reference lattice, q-reading formula. -/
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.Mzk1P6SourceFieldsActual
import tmp.sheaf.xif.paper.Mzk1P6RootParameterWeightActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.URPacketDefs
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual
open LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual

universe u v w
variable {l : PrimeGeFive} (X : N8NativeInput l)

abbrev urP : Nat := p6P X
abbrev urPlaces : Unit → Unit → FinitePlaceAtPrime X.S.arithmetic.F (urP X) := p6Places X
abbrev urTuple : Unit → Unit := p6Tuple X
abbrev urBlock : Type := P6Block X

def urIst : Unit := ()
def urVarpi : CommonPrimeCompletion ((urPlaces X) urIst ((urTuple X) urIst)) := 1
theorem urHvarpi : urVarpi X ≠ 0 := one_ne_zero

def urReferenceLattice : Set (urBlock X) :=
  arithmeticTupleUnitLogLattice (urPlaces X) (urTuple X)

def urQRootLattice (r : urBlock X) : Set (urBlock X) :=
  {x | ∃ n : ℤ, x = n • r}

def urThetaSourceSpan (gens : Finset (urBlock X)) : Set (urBlock X) :=
  {x | ∃ c : urBlock X → ℤ, x = ∑ g ∈ gens, (c g) • g}

theorem urQRootLattice_def (r : urBlock X) {x : urBlock X}
    (hx : x ∈ urQRootLattice X r) : ∃ n : ℤ, x = n • r := hx
theorem urThetaSourceSpan_def (gens : Finset (urBlock X)) {x : urBlock X}
    (hx : x ∈ urThetaSourceSpan X gens) :
    ∃ c : urBlock X → ℤ, x = ∑ g ∈ gens, (c g) • g := hx

theorem ur_qReading_formula {p : Nat} {K : Type*} [NormedField K]
    (D : DistinguishedScalarData p K) :
    ord (K := K) p (theta D.alpha D.j) =
      ((D.j : Real) ^ 2 / (2 * (D.l : Real))) * ord (K := K) p D.q :=
  rootParameterWeight_eq_ord_varpi D

#print axioms ur_qReading_formula
end LeanFormal.IUT.XiFPaper.URPacketDefs
end
