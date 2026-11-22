/- U-R theta region (red-fix, generic actual-data form).

The former version was red: it imported the non-actual `URPacketDefs`
(`urVarpi := 1`) and the failed `URPhiAction`.  This version states the
containment for the actual packet data of `Mzk1P6PhiActionFamilyActual` with a
genuine nonzero `varpi`, exactly as the donor, and is therefore green.

NOTE (documented limitation, not a surrogate): the X-side instantiation at the
concrete `p6Places X / p6Tuple X / (p6Witness X).equiv` data times out at the
default 200000-heartbeat limit during `whnf` of `p6PacketHull` (the same
statement-level timeout that forced removing the heavy `p6PacketHull` containment
from `Mzk1URPacketActual`); heartbeat overrides are forbidden by discipline, so
the concrete instantiation needs a statement refactor (opaque packet-hull wrapper)
before it can be added. -/
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.URThetaRegion

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- Every actual theta possible image (actual packet data, genuine nonzero
`varpi`) lies in the actual packet hull. -/
theorem ur_thetaRegion_subset_hull
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar))) :
    arithmeticTupleStepVPossibleImages places tuple istar varpi (p6Phi places tuple) ⊆
      p6PacketHull places tuple e istar varpi :=
  p6_possibleImages_subset_packetHull places tuple e istar varpi

#print axioms ur_thetaRegion_subset_hull

end LeanFormal.IUT.XiFPaper.URThetaRegion
end