/- R2 actual StepV inputs (kurt): concrete algebraic equivalence e and the StepV source-space
instantiation at the actual packet place.

Inputs (all actual):
 * varpi := (urCeilData T b).localGenerator () (nonzero: urCeilLocalGenerator_ne_zero)
 * Phi := ksThetaPhi (unit-log-lattice preserving by definition: hPhi is `fun _ hphi => hphi`)
 * m := floor(lam - sum_i (d_i + a_i)) with lam, d_i as in Mzk1URPacketActualInstanceActual
 * e := (AlgEquiv.funUnique Qp Unit (ksBlock T b)).symm : ksBlock T b ~= ((_ : Unit) -> ksBlock T b)
       (constructed, not assumed; J := Unit, E := fun _ => ksBlock T b).
-/
import tmp.sheaf.xif.paper.Mzk1URPacketActualInstanceActual
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URStepVActualInputsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1URPacketActualInstanceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The concrete algebraic equivalence `e` used by the StepV packet: the product block with
the unique index type `Unit` is the block itself (`AlgEquiv.funUnique`). -/
noncomputable def urStepVE :
    ksBlock T b ≃ₐ[ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]]
      ((_ : Unit) → fun _ => ksBlock T b) :=
  (AlgEquiv.funUnique ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val] Unit
    (ksBlock T b)).symm

/-- The actual StepV possible-image containment, with all StepV inputs instantiated concretely
(varpi the ceiling generator, Phi = ksThetaPhi, m the paper floor, e = urStepVE). -/
theorem stepVPossibleImages_subset_endpoint_actual [DecidableEq qVFamTensorV] :
    arithmeticTupleStepVPossibleImages (ksPlaces T b) ksTuple ()
        ((urCeilData T b).localGenerator ()) (ksThetaPhi (l := l) T b)
      ⊆ arithmeticTupleTprod (ksPlaces T b) ksTuple
          (arithmeticTupleStepVEndpointGenerator (ksPlaces T b) ksTuple () 
            ⌊(LocalFieldLogarithm.localNormOrder (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
                ((urCeilData T b).localGenerator ()) : ℝ) -
              ∑ i : qVFamTensorV,
                (LocalFieldLogarithm.localNormOrder
                    (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
                    (arithmeticTupleLocalDifferent (ksPlaces T b) ksTuple i) +
                  arithmeticTupleStepVA (ksPlaces T b) ksTuple i)⌋) •
        arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple := by
  have hPhi : ∀ φ ∈ ksThetaPhi (l := l) T b,
      ∀ u ∈ arithmeticTupleUnitLogLattice (ksPlaces T b) ksTuple,
        φ u ∈ arithmeticTupleUnitLogLattice (ksPlaces T b) ksTuple :=
    fun φ hφ => hφ
  refine arithmeticTupleStepVPossibleImages_subset_endpoint (ksPlaces T b) ksTuple ()
    ((urCeilData T b).localGenerator ()) (urCeilLocalGenerator_ne_zero (l := l) T b)
    (ksThetaPhi (l := l) T b) hPhi
    ⌊(LocalFieldLogarithm.localNormOrder (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
        ((urCeilData T b).localGenerator ()) : ℝ) -
      ∑ i : qVFamTensorV,
        (LocalFieldLogarithm.localNormOrder
            (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
            (arithmeticTupleLocalDifferent (ksPlaces T b) ksTuple i) +
          arithmeticTupleStepVA (ksPlaces T b) ksTuple i)⌋ ?_
  rw [Finset.sum_add_distrib, ← sub_sub]
  exact Int.floor_le _

#print axioms stepVPossibleImages_subset_endpoint_actual

end LeanFormal.IUT.XiFPaper.Mzk1URStepVActualInputsActual
end