-- UNNECESSARY per 2026-10-29 direction: target uses rootThetaHull itself;
-- this closure/equality file is not queued and must not be extended.
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

/-! # Root hull over nonzero F_l^x labels and closedness gap

The root theta union in RootHullContainmentInequalityActual used all SignedLabel
labels.  This file restricts to the actual nonzero labels (F_l^x, j != 0), where
j^2 >= 1.  Then every root theta region F(j^2 c_root) O_hol is contained in the
maximal j = 1 region F(c_root) O_hol, so the nonzero root union is contained in
the minimal region.

The minimal region is contained in the closure hull (as the j = 1 member of the
union).  The reverse closure containment is exactly closedness of the minimal
region; it is recorded as an exact gap, not assumed.  Thus equality of the root
hull with F(c_root) O_hol is proved conditional on IsClosed.

No fake equality.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootHullClosednessActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.Foundations.Theta
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
variable (hcRoot : ∀ i, 0 <= cRoot i)
variable (oneLabel : SignedLabel l.value)
variable (hone : (gaussExponent oneLabel.1).toNat = 1)

/-- The nonzero F_l^x label subtype. -/
abbrev NonzeroLabel := {j : SignedLabel l.value // j.1 ≠ 0}

/-- Exponent j^2 is at least one for every nonzero label. -/
theorem one_le_exp_of_ne_zero {j : SignedLabel l.value} (hj : j.1 ≠ 0) :
    1 <= (gaussExponent j.1).toNat := by
  have hpos : 0 < j.1 ^ 2 := sq_pos_of_ne_zero hj
  have hcast : ((j.1 ^ 2).toNat : Int) = j.1 ^ 2 :=
    Int.toNat_of_nonneg hpos.le
  unfold gaussExponent
  omega

/-- The nonzero root theta image union. -/
def rootThetaImageSetNZ : Set (ArithmeticTensorTupleBlock places tuple) :=
  ⋃ j : NonzeroLabel (l := l),
    rootThetaRegion (l := l) places tuple cRoot j.1

/-- The nonzero root closure hull. -/
def rootThetaHullNZ : Set (ArithmeticTensorTupleBlock places tuple) :=
  closure (rootThetaImageSetNZ (l := l) places tuple cRoot)

/-- The minimal j = 1 root region. -/
def rootMinimalRegion : Set (ArithmeticTensorTupleBlock places tuple) :=
  rootThetaRegion (l := l) places tuple cRoot oneLabel

/-- The one label is nonzero because its gauss exponent is one. -/
theorem oneLabel_ne_zero : oneLabel.1 ≠ 0 := by
  intro hzero
  rw [hzero] at hone
  norm_num [gaussExponent] at hone

/-- Every nonzero root theta region is contained in the minimal region. -/
theorem rootThetaRegion_subset_minimal (j : NonzeroLabel (l := l)) :
    rootThetaRegion (l := l) places tuple cRoot j.1 ⊆
      rootMinimalRegion (l := l) places tuple cRoot oneLabel := by
  intro x hx
  unfold rootMinimalRegion rootThetaRegion at hx ⊢
  have hexp : (1 : Real) <= ((gaussExponent j.1.1).toNat : Real) := by
    exact_mod_cast one_le_exp_of_ne_zero (l := l) j.2
  have hcoeff : ∀ i, cRoot i <= (gaussExponent j.1.1).toNat * cRoot i := by
    intro i
    calc
      cRoot i = 1 * cRoot i := by ring
      _ <= _ := mul_le_mul_of_nonneg_right hexp (hcRoot i)
  have hlat : arithmeticTupleFractionalLattice places tuple
      (fun i => (gaussExponent j.1.1).toNat * cRoot i) <=
      arithmeticTupleFractionalLattice places tuple
        (fun i => (gaussExponent oneLabel.1).toNat * cRoot i) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    rw [hone]
    simpa using hcoeff i
  have hmul := mul_le_mul' hlat
    (le_rfl : arithmeticTupleHolomorphicLattice places tuple <=
      arithmeticTupleHolomorphicLattice places tuple)
  exact hmul hx

/-- The nonzero root union is contained in the minimal region. -/
theorem rootThetaImageSetNZ_subset_minimal :
    rootThetaImageSetNZ (l := l) places tuple cRoot ⊆
      rootMinimalRegion (l := l) places tuple cRoot oneLabel := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
  exact rootThetaRegion_subset_minimal (l := l) places tuple cRoot
    hcRoot oneLabel hone j hj

/-- The minimal region is contained in the closure hull. -/
theorem rootMinimalRegion_subset_hullNZ :
    rootMinimalRegion (l := l) places tuple cRoot oneLabel ⊆
      rootThetaHullNZ (l := l) places tuple cRoot := by
  intro x hx
  apply subset_closure
  exact Set.mem_iUnion.mpr ⟨⟨oneLabel, oneLabel_ne_zero (l := l) oneLabel hone⟩, hx⟩

/-- Exact closedness gap for the minimal region. -/
def RootMinimalRegionClosedGap : Prop :=
  IsClosed (rootMinimalRegion (l := l) places tuple cRoot oneLabel)

/-- Conditional reverse containment: closed minimal region contains the closure
hull. -/
theorem rootThetaHullNZ_subset_minimal_of_closed
    (hclosed : RootMinimalRegionClosedGap (l := l) places tuple cRoot oneLabel) :
    rootThetaHullNZ (l := l) places tuple cRoot ⊆
      rootMinimalRegion (l := l) places tuple cRoot oneLabel := by
  unfold rootThetaHullNZ
  apply closure_minimal
  · exact rootThetaImageSetNZ_subset_minimal (l := l) places tuple cRoot
      hcRoot oneLabel hone
  · exact hclosed

/-- Conditional equality of the nonzero root hull with the minimal region. -/
theorem rootThetaHullNZ_eq_minimal_of_closed
    (hclosed : RootMinimalRegionClosedGap (l := l) places tuple cRoot oneLabel) :
    rootThetaHullNZ (l := l) places tuple cRoot =
      rootMinimalRegion (l := l) places tuple cRoot oneLabel := by
  apply Set.Subset.antisymm
  · exact rootThetaHullNZ_subset_minimal_of_closed (l := l) places tuple
      cRoot hcRoot oneLabel hone hclosed
  · exact rootMinimalRegion_subset_hullNZ (l := l) places tuple cRoot
      oneLabel hone

end LeanFormal.IUT.XiFPaper.RootHullClosednessActual

end
