import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Tactic
/-!
# R2 L_w packet: PacketHullData with a prescribed possible-image family `Phi`

The L_w packet uses `Phi_j := mulLeft ((urRootAlpha T b)^(gaussExponent j))`, `varpi = 1`,
`e = funUnique`.  This file supplies the structure-level constructor and the hull
definition; the actual `mulLeft`/`funUnique` instantiations are supplied by the caller
(the root-extension carrier has no `Field` instance in the current interface).
Only the `Phi`-override and its `hPhi_ne`/`hPhi` obligations are constructed here.
-/
noncomputable section
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
universe u v w
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwPacketActual

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
variable {places : (i : ι) → V i → FinitePlaceAtPrime K p}
variable {tuple : (i : ι) → V i}
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

/-- Replace the possible-image family of a packet by `PhiLw`, keeping all other data. -/
noncomputable def packetHullDataWithPhi
    (D : PacketHullData places tuple (J := J) (E := E))
    (PhiLw : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hne : PhiLw.Nonempty)
    (hinv : ∀ phi, phi ∈ PhiLw → ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple →
      phi u ∈ arithmeticTupleUnitLogLattice places tuple) :
    PacketHullData places tuple (J := J) (E := E) :=
  { D with Phi := PhiLw, hPhi_ne := hne, hPhi := hinv }

/-- The L_w packet hull: hull of the possible images `PhiLw`. -/
noncomputable def packetHullLw
    (D : PacketHullData places tuple (J := J) (E := E))
    (PhiLw : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hne : PhiLw.Nonempty)
    (hinv : ∀ phi, phi ∈ PhiLw → ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple →
      phi u ∈ arithmeticTupleUnitLogLattice places tuple) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  packetHull (packetHullDataWithPhi D PhiLw hne hinv)

theorem packetHullLw_eq
    (D : PacketHullData places tuple (J := J) (E := E))
    (PhiLw : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hne : PhiLw.Nonempty)
    (hinv : ∀ phi, phi ∈ PhiLw → ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple →
      phi u ∈ arithmeticTupleUnitLogLattice places tuple) :
    packetHullLw D PhiLw hne hinv =
      arithmeticTupleHolomorphicHull places tuple D.e
        (arithmeticTupleStepVPossibleImages places tuple D.istar D.varpi PhiLw) := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwPacketActual
end