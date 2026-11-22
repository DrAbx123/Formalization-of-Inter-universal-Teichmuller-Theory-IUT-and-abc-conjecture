import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-! # S779: use only nonzero paper Theta labels in the root Theta hull

The old `rootThetaHull` unions over all `SignedLabel`, including j = 0.  At
j = 0 the coefficient is zero, so `rootThetaRegion 0` is the full
holomorphic region O_hol and contains every positive-label region.  This
makes the old hull degenerate.  This file defines the corrected nonzero
hull over `{j // j ≠ 0}` and proves the exact relation to the minimal region.
-/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe uK uI uV u
variable {p : Nat} [Fact p.Prime]
variable {K : Type uK} [Field K] [NumberField K]
variable {l : PrimeGeFive}
variable {ι : Type uI} [Fintype ι]
variable {V : ι -> Type uV} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (cRoot : ι -> Real)
variable (hcRoot : ∀ i, 0 <= cRoot i)
variable (oneLabel : SignedLabel l.value)
variable (hone : (gaussExponent oneLabel.1).toNat = 1)

abbrev NonzeroLabel := {j : SignedLabel l.value // j.1 ≠ 0}

theorem one_le_exp_of_ne_zero {j : SignedLabel l.value} (hj : j.1 ≠ 0) :
    1 <= (gaussExponent j.1).toNat := by
  have hpos : 0 < j.1 ^ 2 := sq_pos_of_ne_zero hj
  have hcast : ((j.1 ^ 2).toNat : Int) = j.1 ^ 2 :=
    Int.toNat_of_nonneg hpos.le
  unfold gaussExponent
  omega

noncomputable def rootThetaImageSetNonzero :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  ⋃ j : NonzeroLabel (l := l), rootThetaRegion (l := l) places tuple cRoot j.1

noncomputable def rootThetaHullNonzero :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  closure (rootThetaImageSetNonzero (l := l) places tuple cRoot)

noncomputable def rootMinimalRegion :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  rootThetaRegion (l := l) places tuple cRoot oneLabel

theorem oneLabel_ne_zero (hone : (gaussExponent oneLabel.1).toNat = 1) :
    oneLabel.1 ≠ 0 := by
  intro hzero
  rw [hzero] at hone
  norm_num [gaussExponent] at hone

theorem rootThetaRegion_subset_minimal
    (hcRoot : ∀ i, 0 <= cRoot i) (hone : (gaussExponent oneLabel.1).toNat = 1)
    (j : NonzeroLabel (l := l)) :
    rootThetaRegion (l := l) places tuple cRoot j.1 ⊆
      rootMinimalRegion (l := l) places tuple cRoot oneLabel := by
  intro x hx
  unfold rootMinimalRegion at ⊢
  unfold rootThetaRegion at hx ⊢
  have hexp : (1 : Real) <= ((gaussExponent j.1.1).toNat : Real) := by
    exact_mod_cast one_le_exp_of_ne_zero (l := l) j.2
  have hcoef : ∀ i, cRoot i <= (gaussExponent j.1.1).toNat * cRoot i := by
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
    simpa using hcoef i
  have hmul := mul_le_mul' hlat
    (le_rfl : arithmeticTupleHolomorphicLattice places tuple <=
      arithmeticTupleHolomorphicLattice places tuple)
  exact hmul hx

theorem rootThetaImageSetNonzero_subset_minimal
    (hcRoot : ∀ i, 0 <= cRoot i) (hone : (gaussExponent oneLabel.1).toNat = 1) :
    rootThetaImageSetNonzero (l := l) places tuple cRoot ⊆
      rootMinimalRegion (l := l) places tuple cRoot oneLabel := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
  exact rootThetaRegion_subset_minimal (l := l) (places := places) (tuple := tuple)
    (cRoot := cRoot) (oneLabel := oneLabel) (hcRoot := hcRoot) (hone := hone) j hj

theorem rootMinimalRegion_subset_hullNonzero
    (hone : (gaussExponent oneLabel.1).toNat = 1) :
    rootMinimalRegion (l := l) places tuple cRoot oneLabel ⊆
      rootThetaHullNonzero (l := l) places tuple cRoot := by
  intro x hx
  apply subset_closure
  exact Set.mem_iUnion.mpr
    ⟨⟨oneLabel, oneLabel_ne_zero (l := l) oneLabel hone⟩, hx⟩

theorem rootThetaHullNonzero_eq_closure_minimal
    (hcRoot : ∀ i, 0 <= cRoot i) (hone : (gaussExponent oneLabel.1).toNat = 1) :
    rootThetaHullNonzero (l := l) places tuple cRoot =
      closure (rootMinimalRegion (l := l) places tuple cRoot oneLabel) := by
  apply Set.Subset.antisymm
  · unfold rootThetaHullNonzero
    apply closure_minimal
    · exact (rootThetaImageSetNonzero_subset_minimal (l := l) (places := places)
        (tuple := tuple) (cRoot := cRoot) (oneLabel := oneLabel)
        (hcRoot := hcRoot) (hone := hone)).trans subset_closure
    · exact isClosed_closure
  · apply closure_minimal
    · exact rootMinimalRegion_subset_hullNonzero (l := l) places tuple cRoot oneLabel hone
    · exact isClosed_closure

def RootMinimalRegionClosedGap : Prop :=
  IsClosed (rootMinimalRegion (l := l) places tuple cRoot oneLabel)

theorem rootThetaHullNonzero_eq_minimal_of_closed
    (hcRoot : ∀ i, 0 <= cRoot i) (hone : (gaussExponent oneLabel.1).toNat = 1)
    (hclosed : RootMinimalRegionClosedGap (l := l) places tuple cRoot oneLabel) :
    rootThetaHullNonzero (l := l) places tuple cRoot =
      rootMinimalRegion (l := l) places tuple cRoot oneLabel := by
  have h := rootThetaHullNonzero_eq_closure_minimal (l := l) (places := places)
    (tuple := tuple) (cRoot := cRoot) (oneLabel := oneLabel)
    (hcRoot := hcRoot) (hone := hone)
  rw [h]
  exact IsClosed.closure_eq hclosed

section PaperSpecialization

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual

/-- The zero signed label, used only to audit the old zero-inclusive hull. -/
def zeroSignedLabel : SignedLabel l.value :=
  ⟨0, by
    rw [Set.mem_Icc]
    constructor
    · have h : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
    · have h : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega⟩

variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem paperRootCoefficientFamily_nonneg (i : qVFamTensorV) :
    0 <= paperRootCoefficientFamily (l := l) T b i := by
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
  positivity

/-- Corrected paper root Theta hull: nonzero labels only. -/
noncomputable def paperRootThetaHullNonzero : Set (qVFamTensorBlock T b) :=
  rootThetaHullNonzero (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b)

/-- Corrected paper root Theta hull log: nonzero labels only. -/
noncomputable def paperRootThetaHullLogNonzero
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperRootThetaHullNonzero (l := l) T b)

/-- Exact closedness gap for the corrected paper hull. -/
def PaperRootHullNonzeroClosedGap : Prop :=
  IsClosed (rootMinimalRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b) (SignedLabelOneActual.oneLabel l))

/-- Exact bridge required to identify the corrected hull log with the paper
formula log.  Both the closedness gap and the nonzero-label hull are needed. -/
def PaperRootHullNonzeroFormulaBridge : Prop :=
  paperRootThetaHullLogNonzero (l := l) T b Measure.addHaar =
    -((∑ _ : qVFamTensorV, paperRootCoefficientFamily (l := l) T b ()) *
      Real.log (qVFamTensorP T b : Real))

/-- Audit: the old zero-inclusive paper hull contains the j = 0 region. -/
theorem zero_region_subset_old_paperRootThetaHull :
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b)
        (SignedLabel.representative l (0 : Fl l.value)) ⊆ paperRootThetaHull (l := l) T b := by
  intro x hx
  unfold paperRootThetaHull rootThetaHull rootThetaImageSet
  exact subset_closure (Set.mem_iUnion.mpr
    ⟨SignedLabel.representative l (0 : Fl l.value), hx⟩)

/-- Corrected hull alias for S753/S733/S739 consumers: nonzero labels only. -/
noncomputable def S759CorrectedThetaHull : Set (qVFamTensorBlock T b) :=
  paperRootThetaHullNonzero (l := l) T b

/-- Corrected log alias for S753/S733/S739 consumers: nonzero labels only. -/
noncomputable def S759CorrectedThetaHullLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  paperRootThetaHullLogNonzero (l := l) T b mu

/-- Exact correction condition for S733: the corrected nonzero hull log is the
paper per-b hull log. -/
def S733CorrectedHullLogNonzeroCondition : Prop :=
  paperRootThetaHullLogNonzero (l := l) T b Measure.addHaar =
    -((∑ _ : qVFamTensorV, paperRootCoefficientFamily (l := l) T b ()) *
      Real.log (qVFamTensorP T b : Real))

/-- Exact correction condition for S739: the paper-order log must be the
corrected nonzero hull log, not the old zero-inclusive paperRootThetaHullLog. -/
def S739PaperOrderLogNonzeroCondition : Prop :=
  -((∑ _ : qVFamTensorV, paperRootCoefficientFamily (l := l) T b ()) *
      Real.log (qVFamTensorP T b : Real)) =
    paperRootThetaHullLogNonzero (l := l) T b Measure.addHaar

end PaperSpecialization

end LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual

end
