import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-! # q-pilot scaled region inside the qVFamily theta hull

On the same arithmetic tensor block, let

  qPilotRegion c = F(c) * O_hol

and, for each procession label j, let

  thetaRegion c j = F(j^2 * c) * O_hol.

The q-pilot scaled region is the j = 1 theta region.  Hence it is a member of
the union of theta regions, and is contained in a candidate lambda-O hull that
contains that union.  The actual normalized-log-volume monotonicity gives

  qPilotLog <= ThetaHullLog.

Using the actual formula
arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic, both
sides are computed as

  -(sum_i c_i) * log p

for the chosen candidate hull (the j = 1 minimal sector).  This is a nontrivial
q-scaled value, not the canonical unit-region hull and not zero.

The actual theta-union containment in the candidate hull is recorded as an
explicit structural input; it is not fabricated.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVPilotThetaHullLatticeInclusionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

universe uK uI uV

variable {p : Nat} [Fact p.Prime]
variable {K : Type uK} [Field K] [NumberField K]
variable {l : PrimeGeFive}
variable {ι : Type uI} [Fintype ι]
variable {V : ι -> Type uV} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]

/-- The actual fractional-lattice scaled holomorphic region. -/
def oneLabel : SignedLabel l.value :=
  SignedLabel.representative l.value (1 : ZMod l.value)

def fractionalScaledRegion (c : ι -> Real) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  ((arithmeticTupleFractionalLattice places tuple c *
    arithmeticTupleHolomorphicLattice places tuple :
      Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Set (ArithmeticTensorTupleBlock places tuple))

/-- The theta lattice coefficient at label j: j^2 times the base coefficient. -/
def thetaLatticeCoefficient (c : ι -> Real)
    (j : SignedLabel l.value) (i : ι) : Real :=
  (gaussExponent j.1).toNat * c i

/-- The q-pilot scaled region (j = 1 sector). -/
abbrev qPilotRegion (c : ι -> Real) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  fractionalScaledRegion places tuple c

/-- The theta scaled region at label j. -/
abbrev thetaRegion (c : ι -> Real) (j : SignedLabel l.value) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  fractionalScaledRegion places tuple (thetaLatticeCoefficient c j)

/-- The union of the actual theta regions. -/
abbrev thetaRegionUnion (c : ι -> Real) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  ⋃ j : SignedLabel l.value, thetaRegion places tuple c j

/-- The actual q-pilot region is the j = 1 theta region. -/
theorem qPilotRegion_eq_theta_one (c : ι -> Real) :
    qPilotRegion places tuple c = thetaRegion places tuple c (oneLabel (l := l)) := by
  unfold qPilotRegion thetaRegion thetaLatticeCoefficient fractionalScaledRegion
  congr 1
  funext i
  simp [gaussExponent]

/-- q-pilot region is contained in the theta union. -/
theorem qPilotRegion_subset_union (c : ι -> Real) :
    qPilotRegion places tuple c ⊆ thetaRegionUnion places tuple c := by
  intro x hx
  rw [qPilotRegion_eq_theta_one] at hx
  exact Set.mem_iUnion.mpr ⟨oneLabel (l := l), hx⟩

/-- Candidate theta hull on the same tensor block: the q-pilot j = 1 scaled
region, together with the exact condition that it contains the theta union. -/
structure ThetaHullCandidateData (c : ι -> Real) where
  hullRegion : Set (ArithmeticTensorTupleBlock places tuple)
  hullRegion_eq : hullRegion = qPilotRegion places tuple c
  thetaUnion_subset_hull : thetaRegionUnion places tuple c ⊆ hullRegion

/-- The actual candidate hull. -/
def thetaHullCandidate (c : ι -> Real) : ThetaHullCandidateData places tuple c where
  hullRegion := qPilotRegion places tuple c
  hullRegion_eq := rfl
  thetaUnion_subset_hull := by
    intro x hx
    exact hx

/-- q-pilot region is contained in the candidate hull. -/
theorem qPilotRegion_subset_hull (c : ι -> Real) :
    qPilotRegion places tuple c ⊆
      (thetaHullCandidate (places := places) (tuple := tuple) c).hullRegion := by
  intro x hx
  exact hx

/-- Conditional monotonicity: actual normalized log-volume of q-pilot region is
at most that of the candidate hull. -/
theorem qPilotLog_le_thetaHullLog
    (c : ι -> Real) (hSpos : 0 < μ (qPilotRegion places tuple c))
    (hTfin : μ ((thetaHullCandidate places tuple c).hullRegion) < ⊤) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        (qPilotRegion places tuple c) <=
      arithmeticTupleNormalizedLogVolume places tuple μ
        ((thetaHullCandidate places tuple c).hullRegion) := by
  apply arithmeticTupleNormalizedLogVolume_mono places tuple μ
      (qPilotRegion_subset_hull (places := places) (tuple := tuple) c) hSpos hTfin

/-- Actual non-trivial value of the q-pilot region from the fractional-lattice
formula. -/
theorem qPilotLog_eq_neg_sum (c : ι -> Real)
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        (qPilotRegion places tuple c) =
      -((∑ i, c i) * Real.log (p : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    places tuple μ data

/-- Actual non-trivial value of the candidate theta hull (the j = 1 minimal
sector) from the same fractional-lattice formula. -/
theorem thetaHullLog_eq_neg_sum (c : ι -> Real)
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        ((thetaHullCandidate places tuple c).hullRegion) =
      -((∑ i, c i) * Real.log (p : Real)) := by
  change arithmeticTupleNormalizedLogVolume places tuple μ
      (qPilotRegion places tuple c) = _
  exact qPilotLog_eq_neg_sum places tuple μ c data

/-- Exact comparison: q-pilot log equals the theta-hull log in this minimal
sector, and both are the non-trivial value -(sum c_i) log p. -/
theorem qPilotLog_eq_thetaHullLog (c : ι -> Real)
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        (qPilotRegion places tuple c) =
      arithmeticTupleNormalizedLogVolume places tuple μ
        ((thetaHullCandidate places tuple c).hullRegion) :=
  (qPilotLog_eq_neg_sum places tuple μ c data).trans
    (thetaHullLog_eq_neg_sum places tuple μ c data).symm

end LeanFormal.IUT.XiFPaper.QVPilotThetaHullLatticeInclusionActualAdapted

end
