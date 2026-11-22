/- PIECE 2 (kurt): hull equality for the local root family.

Combines LocalStepV (localRootImages/localRootHull) with PIECE 1's L_w packet constructor to record:
 * localRootImages is literally the union of the root images ⋃_j r^(gauss j) O;
 * the hull equals the image union as soon as the union is closed (needed to pass hull = source image
   set, i.e. packetHull_L = rootNormHull_L in the local carrier);
 * packetHullLw is the holomorphic hull of the StepV possible images (rfl, from PIECE 1).
-/
import tmp.sheaf.xif.paper.Mzk1G1F2R2LocalStepVActual
import tmp.sheaf.xif.paper.Mzk1G1F2R2LwPacketActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Pointwise
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwHullEqActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.LocalStepVActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwPacketActual

variable {L : Type*} [NormedField L]

/-- The local root images are the union of the root-ball multiples (definitional form). -/
theorem localRootImages_eq_iUnion {J : Type*} (r : L) (gauss : J → ℤ) (O : Set L) :
    localRootImages r gauss O = ⋃ j : J, (r ^ (gauss j)) • O := rfl

/-- If the union of root images is closed, the hull equals it exactly: packetHull_L = rootNormHull_L
in the local carrier (no strict enlargement under closure). -/
theorem localRootHull_eq_images_of_isClosed {J : Type*} (r : L) (gauss : J → ℤ) (O : Set L)
    (hclosed : IsClosed (localRootImages r gauss O)) :
    localRootHull r gauss O = localRootImages r gauss O := by
  unfold localRootHull
  exact IsClosed.closure_eq hclosed

/-- Every root image lies in the hull (subset direction used for the log-volume bound). -/
theorem localRootImages_subset_hull' {J : Type*} (r : L) (gauss : J → ℤ) (O : Set L) :
    localRootImages r gauss O ⊆ localRootHull r gauss O :=
  localRootImages_subset_hull r gauss O

section Packet

variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
variable {places : (i : ι) → V i → FinitePlaceAtPrime K p}
variable {tuple : (i : ι) → V i}
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type*} [Finite J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

/-- The L_w packet hull is the holomorphic hull of the StepV possible images (PIECE 1, rfl). -/
theorem packetHullLw_eq_holomorphicHull
    (D : PacketHullData places tuple (J := J) (E := E))
    (PhiLw : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hne : PhiLw.Nonempty)
    (hinv : ∀ phi, phi ∈ PhiLw → ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple →
      phi u ∈ arithmeticTupleUnitLogLattice places tuple) :
    packetHullLw D PhiLw hne hinv =
      arithmeticTupleHolomorphicHull places tuple D.e
        (arithmeticTupleStepVPossibleImages places tuple D.istar D.varpi PhiLw) :=
  packetHullLw_eq D PhiLw hne hinv

end Packet

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LwHullEqActual
end