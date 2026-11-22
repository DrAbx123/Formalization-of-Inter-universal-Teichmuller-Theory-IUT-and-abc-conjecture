/- U-R actual packet carrier (route §5.3): actual bad place, reference lattice,
actual Phi action family, q-root lattice, theta source span and the q-reading
order bridge.

Discipline: no `varpi = 1` surrogate, no `exceptional = univ`, no heartbeat
override, no C1 feed (that conclusion belongs to U-C/sophie).  The packet-hull
containment `p6_possibleImages_subset_packetHull` is an existing accepted donor and is
re-exported by the U-L lane instead of being duplicated here. -/
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.Mzk1P6SourceFieldsActual
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.Mzk1P6RootParameterWeightActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1URPacketActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The chosen actual packet: the native bad place of `X`, one-slot tuple. -/
abbrev urP : Nat := p6P X
abbrev urPlaces : Unit → Unit → FinitePlaceAtPrime X.S.arithmetic.F (urP X) := p6Places X
abbrev urTuple : Unit → Unit := p6Tuple X
abbrev urBlock : Type := P6Block X

local instance urMeasurable : MeasurableSpace (urBlock X) := borel _
local instance urBorel : BorelSpace (urBlock X) := ⟨rfl⟩

/-- The distinguished slot index of the packet. -/
def urIst : Unit := ()

/-- Reference lattice: the actual unit log lattice of the packet. -/
def urReferenceLattice : Set (urBlock X) :=
  arithmeticTupleUnitLogLattice (urPlaces X) (urTuple X)

/-- Phi action family of the packet (lattice-preserving linear equivalences). -/
def urPhi : Set (urBlock X ≃ₗ[ℚ_[urP X]] urBlock X) :=
  p6Phi (urPlaces X) (urTuple X)

theorem urPhi_preserves
    {phi : urBlock X ≃ₗ[ℚ_[urP X]] urBlock X} (hphi : phi ∈ urPhi X) :
    ∀ u, u ∈ urReferenceLattice X → phi u ∈ urReferenceLattice X :=
  hphi

theorem urPhi_nonempty : (urPhi X).Nonempty := by
  refine ⟨LinearEquiv.refl ℚ_[urP X] (urBlock X), ?_⟩
  intro u hu
  simpa using hu

/-- q-root lattice: integer multiples of an actual root datum `r`. -/
def urQRootLattice (r : urBlock X) : Set (urBlock X) :=
  {x | ∃ n : ℤ, x = (n : ℚ_[urP X]) • r}

/-- Theta source span: integer span of the actual source generators. -/
def urThetaSourceSpan (gens : Finset (urBlock X)) : Set (urBlock X) :=
  {x | ∃ c : urBlock X → ℤ, x = ∑ g ∈ gens, (c g : ℚ_[urP X]) • g}

theorem urQRootLattice_def (r : urBlock X) {x : urBlock X}
    (hx : x ∈ urQRootLattice X r) : ∃ n : ℤ, x = (n : ℚ_[urP X]) • r := hx

theorem urThetaSourceSpan_def (gens : Finset (urBlock X)) {x : urBlock X}
    (hx : x ∈ urThetaSourceSpan X gens) :
    ∃ c : urBlock X → ℤ, x = ∑ g ∈ gens, (c g : ℚ_[urP X]) • g := hx

/-- q-reading order bridge: the theta root order equals `j^2/(2l) * ord(q)`,
for an actual distinguished scalar at a fixed prime. -/
theorem ur_qReading_formula {p : Nat} {K : Type*} [NormedField K]
    (D : DistinguishedScalarData p K) :
    ord (K := K) p (theta D.alpha D.j) =
      ((D.j : Real) ^ 2 / (2 * (D.l : Real))) * ord (K := K) p D.q :=
  rootParameterWeight_eq_ord_varpi D

#print axioms urPhi_preserves
#print axioms ur_qReading_formula

end LeanFormal.IUT.XiFPaper.Mzk1URPacketActual
end