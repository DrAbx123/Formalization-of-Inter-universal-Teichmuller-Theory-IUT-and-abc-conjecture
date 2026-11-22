import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels

/-! # qPilot classical region inside the root theta hull

Let c_norm be the normalized-generator qPilot coefficient and c_root the 2l-th
root coefficient, with c_root <= c_norm.  The qPilot classical region

  F(c_norm) * O_hol

is contained in the minimal root theta region F(c_root) * O_hol, hence in the
root theta closure hull.  The actual fractional-lattice formula computes

  mu_log(F(c_norm) * O_hol) = -(sum c_norm) log p,

and normalized-log-volume monotonicity gives

  qPilotSigned <= rootThetaHullLog.

No root hull equality is asserted.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual

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
variable (cNorm cRoot : ι -> Real)
variable (dataNorm : ArithmeticTuplePureFractionalScalingData places tuple cNorm)
variable (hge : ∀ i, cRoot i <= cNorm i)
variable (oneLabel : SignedLabel l.value)
variable (hone : (gaussExponent oneLabel.1).toNat = 1)

/-- The qPilot classical normalized-generator region F(c_norm) * O_hol. -/
def qPilotClassicalRegion : Set (ArithmeticTensorTupleBlock places tuple) :=
  ((arithmeticTupleFractionalLattice places tuple cNorm *
    arithmeticTupleHolomorphicLattice places tuple :
      Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Set (ArithmeticTensorTupleBlock places tuple))

/-- The actual root theta region at a signed label j: F(j^2 c_root) * O_hol. -/
def rootThetaRegion (j : SignedLabel l.value) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  ((arithmeticTupleFractionalLattice places tuple
      (fun i => (gaussExponent j.1).toNat * cRoot i) *
    arithmeticTupleHolomorphicLattice places tuple :
      Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Set (ArithmeticTensorTupleBlock places tuple))

/-- The root theta image union. -/
def rootThetaImageSet : Set (ArithmeticTensorTupleBlock places tuple) :=
  ⋃ j : SignedLabel l.value, rootThetaRegion (l := l) places tuple cRoot j

/-- The actual root theta closure hull. -/
def rootThetaHull : Set (ArithmeticTensorTupleBlock places tuple) :=
  closure (rootThetaImageSet (l := l) places tuple cRoot)

theorem qPilotClassicalRegion_subset_rootHull
    (hge : ∀ i, cRoot i <= cNorm i)
    (oneLabel : SignedLabel l.value)
    (hone : (gaussExponent oneLabel.1).toNat = 1) :
    qPilotClassicalRegion places tuple cNorm ⊆
      rootThetaHull (l := l) places tuple cRoot := by
  intro x hx
  apply subset_closure
  apply Set.mem_iUnion.mpr
  refine ⟨oneLabel, ?_⟩
  -- c_root <= c_norm gives F(c_norm) <= F(c_root)
  have hlat : arithmeticTupleFractionalLattice places tuple cNorm <=
      arithmeticTupleFractionalLattice places tuple
        (fun i => (gaussExponent (oneLabel).1).toNat * cRoot i) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    rw [hone]
    simpa using hge i
  have hmul := mul_le_mul' hlat
    (le_rfl : arithmeticTupleHolomorphicLattice places tuple <=
      arithmeticTupleHolomorphicLattice places tuple)
  exact hmul hx

/-- Actual qPilot classical normalized log. -/
noncomputable def qPilotClassicalLog
    (dataNorm : ArithmeticTuplePureFractionalScalingData places tuple cNorm) : Real :=
  arithmeticTupleNormalizedLogVolume places tuple μ
    (qPilotClassicalRegion places tuple cNorm)

/-- Exact formula for qPilot classical log from the actual scaling data. -/
theorem qPilotClassicalLog_eq :
    qPilotClassicalLog places tuple μ cNorm dataNorm =
      -((∑ i, cNorm i) * Real.log (p : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    places tuple μ dataNorm

/-- Root theta hull normalized log. -/
noncomputable def rootThetaHullLog : Real :=
  arithmeticTupleNormalizedLogVolume places tuple μ
    (rootThetaHull (l := l) places tuple cRoot)

/-- The actual scalar inequality qPilotSigned <= rootThetaHullLog. -/
theorem qPilotClassicalLog_le_rootThetaHullLog
    (hge : ∀ i, cRoot i <= cNorm i)
    (oneLabel : SignedLabel l.value)
    (hone : (gaussExponent oneLabel.1).toNat = 1)
    (hpos : 0 < μ (qPilotClassicalRegion places tuple cNorm))
    (hfin : μ (rootThetaHull (l := l) places tuple cRoot) < ⊤) :
    qPilotClassicalLog places tuple μ cNorm dataNorm <=
      rootThetaHullLog (l := l) places tuple μ cRoot :=
  arithmeticTupleNormalizedLogVolume_mono places tuple μ
    (qPilotClassicalRegion_subset_rootHull (l := l) places tuple cNorm cRoot hge oneLabel hone)
    hpos hfin

end LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual

end
