import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-! # q-pilot region inside the qVFamily theta hull: actual nesting

On one arithmetic tensor block, let c_i >= 0.  The q-pilot scaled region is

  qPilotRegion c = F(c) * O_hol.

For every F_l^x label j, the theta region is F(j^2 * c) * O_hol.  Since j is a
unit, its centered signed representative is nonzero, so j^2 >= 1.  Antitonicity
of the fractional lattice (arithmeticTupleFractionalLattice_mono) gives

  F(j^2 * c) <= F(c),

and multiplication monotonicity gives thetaRegion j <= qPilotRegion.  Hence
the theta union is contained in qPilotRegion, and the candidate hull with
hullRegion = qPilotRegion is genuinely a hull of the theta union.

The actual qVFamily coefficient nonnegativity is proved from the qVFamily order,
the local residue degree, and residueNormBase > 1.

The previous fake containment intro x hx; exact hx is replaced by the actual
nesting proof.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVPilotThetaHullNestingActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.ArithmeticQPilotBaseChange
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
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]
variable (c : ι -> Real)

/-- The actual fractional-lattice scaled holomorphic region. -/
def fractionalScaledRegion (c : ι -> Real) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  ((arithmeticTupleFractionalLattice places tuple c *
    arithmeticTupleHolomorphicLattice places tuple :
      Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Set (ArithmeticTensorTupleBlock places tuple))

/-- The actual F_l^x theta coefficient: the signed representative of the unit
label, squared, times c. -/
noncomputable def thetaCoeff (j : ProcessionLabel l) (i : ι) : Real :=
  (gaussExponent
    (SignedLabel.representative l (j : ZMod l.value)).1).toNat * c i

/-- The signed representative of a nonzero F_l^x unit is nonzero. -/
theorem representative_ne_zero (j : ProcessionLabel l) :
    (SignedLabel.representative l (j : ZMod l.value)).1 ≠ 0 := by
  intro hzero
  have hto : ((SignedLabel.representative l
      (j : ZMod l.value)).1 : ZMod l.value) = (j : ZMod l.value) := by
    simpa [SignedLabel.toFiniteLabel, SignedLabel.toFl] using
      SignedLabel.representative_toFl l (j : ZMod l.value)
  haveI : Fact (Nat.Prime l.value) := ⟨l.prime⟩
  have hj0 : (j : ZMod l.value) ≠ 0 := Units.ne_zero j
  apply hj0
  rw [← hto, hzero]
  norm_num

/-- The theta exponent j^2 is at least one for every F_l^x unit label. -/
theorem one_le_thetaExponent (j : ProcessionLabel l) :
    1 <= (gaussExponent
      (SignedLabel.representative l (j : ZMod l.value)).1).toNat := by
  have hx : (SignedLabel.representative l
      (j : ZMod l.value)).1 ≠ 0 := representative_ne_zero (l := l) j
  have hx2 : 0 < (SignedLabel.representative l
      (j : ZMod l.value)).1 ^ 2 := sq_pos_of_ne_zero hx
  have hcast : (((SignedLabel.representative l
      (j : ZMod l.value)).1 ^ 2).toNat : Int) =
      (SignedLabel.representative l (j : ZMod l.value)).1 ^ 2 :=
    Int.toNat_of_nonneg hx2.le
  unfold gaussExponent
  omega

/-- Coefficient domination: if c is nonnegative, c_i <= j^2 c_i. -/
theorem coeff_le_thetaCoeff (hc : ∀ i, 0 <= c i) (j : ProcessionLabel l)
    (i : ι) : c i <= thetaCoeff (l := l) c j i := by
  have hexp : (1 : Real) <= ((gaussExponent
      (SignedLabel.representative l (j : ZMod l.value)).1).toNat : Real) := by
    exact_mod_cast one_le_thetaExponent (l := l) j
  unfold thetaCoeff
  calc
    c i = 1 * c i := by ring
    _ <= _ := mul_le_mul_of_nonneg_right hexp (hc i)

/-- The q-pilot scaled region. -/
abbrev qPilotRegion : Set (ArithmeticTensorTupleBlock places tuple) :=
  fractionalScaledRegion places tuple c

/-- The theta scaled region at an F_l^x label. -/
abbrev thetaRegion (j : ProcessionLabel l) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  fractionalScaledRegion places tuple (thetaCoeff (l := l) c j)

/-- The theta union. -/
abbrev thetaRegionUnion : Set (ArithmeticTensorTupleBlock places tuple) :=
  ⋃ j : ProcessionLabel l, thetaRegion (l := l) places tuple c j

/-- Actual nesting: each theta region is contained in the q-pilot region. -/
theorem thetaRegion_subset_qPilot (hc : ∀ i, 0 <= c i)
    (j : ProcessionLabel l) :
    thetaRegion (l := l) places tuple c j ⊆ qPilotRegion places tuple c := by
  intro x hx
  have hlat : arithmeticTupleFractionalLattice places tuple (thetaCoeff (l := l) c j)
      <= arithmeticTupleFractionalLattice places tuple c :=
    arithmeticTupleFractionalLattice_mono places tuple
      (fun i => coeff_le_thetaCoeff (l := l) (c := c) hc j i)
  have hmul := mul_le_mul' hlat
    (le_rfl : arithmeticTupleHolomorphicLattice places tuple <=
      arithmeticTupleHolomorphicLattice places tuple)
  exact hmul hx

/-- The theta union is contained in the q-pilot region. -/
theorem thetaRegionUnion_subset_qPilot (hc : ∀ i, 0 <= c i) :
    thetaRegionUnion (l := l) places tuple c ⊆ qPilotRegion places tuple c := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
  exact thetaRegion_subset_qPilot (l := l) places tuple c hc j hj

/-- Actual hull candidate on the q-pilot region. -/
structure ThetaHullCandidateData where
  hullRegion : Set (ArithmeticTensorTupleBlock places tuple)
  hullRegion_eq : hullRegion = qPilotRegion places tuple c
  thetaUnion_subset_hull : thetaRegionUnion (l := l) places tuple c ⊆ hullRegion

/-- The actual hull candidate; containment is proved, not assumed. -/
def thetaHullCandidate (hc : ∀ i, 0 <= c i) : ThetaHullCandidateData (l := l) places tuple c where
  hullRegion := qPilotRegion places tuple c
  hullRegion_eq := rfl
  thetaUnion_subset_hull := thetaRegionUnion_subset_qPilot (l := l) places tuple c hc

/-- Conditional monotonicity via the actual normalized log-volume. -/
theorem qPilotLog_le_thetaHullLog (hc : ∀ i, 0 <= c i)
    (hSpos : 0 < μ (qPilotRegion places tuple c))
    (hTfin : μ ((thetaHullCandidate (l := l) places tuple c hc).hullRegion) < ⊤) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        (qPilotRegion places tuple c) <=
      arithmeticTupleNormalizedLogVolume places tuple μ
        ((thetaHullCandidate (l := l) places tuple c hc).hullRegion) := by
  apply arithmeticTupleNormalizedLogVolume_mono places tuple μ _ hSpos hTfin
  intro x hx
  exact hx

/-- Actual formula for the q-pilot log-volume. -/
theorem qPilotLog_eq_neg_sum
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        (qPilotRegion places tuple c) =
      -((∑ i, c i) * Real.log (p : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    places tuple μ data

/-- Actual formula for the candidate theta hull log-volume. -/
theorem thetaHullLog_eq_neg_sum
    (hc : ∀ i, 0 <= c i)
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple μ
        ((thetaHullCandidate (l := l) places tuple c hc).hullRegion) =
      -((∑ i, c i) * Real.log (p : Real)) := by
  change arithmeticTupleNormalizedLogVolume places tuple μ
      (qPilotRegion places tuple c) = _
  exact qPilotLog_eq_neg_sum places tuple μ c data

/-- The actual qVFamily base lattice coefficient. -/
noncomputable def qVFamilyBasePLogCoefficient
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log (residueNormBase b.1) / Real.log (NumberFieldFinitePlace.residueCharacteristic b.1 : Real)

/-- The actual qVFamily lattice coefficient from order and place degrees. -/
noncomputable def qVFamilyLatticeCoefficient
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  ((qVFamily T b).order : Real) *
    (localResidueDegree (k := T.arithmetic.Fmod)
      ((nativeBadLift T).lift b) : Real) *
    qVFamilyBasePLogCoefficient (l := l) T b

/-- Actual qVFamily coefficient nonnegativity: order >= 0, local residue
degree >= 0, and the base p-log coefficient is nonnegative. -/
theorem qVFamilyLatticeCoefficient_nonneg
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    0 <= qVFamilyLatticeCoefficient (l := l) T b := by
  unfold qVFamilyLatticeCoefficient qVFamilyBasePLogCoefficient
  apply mul_nonneg
  · apply mul_nonneg
    · exact_mod_cast Nat.zero_le (qVFamily T b).order
    · exact_mod_cast Nat.zero_le (localResidueDegree (k := T.arithmetic.Fmod)
        ((nativeBadLift T).lift b))
  · apply div_nonneg
    · exact le_of_lt (Real.log_pos (residueNormBase_gt_one b.1))
    · apply le_of_lt
      apply Real.log_pos
      exact_mod_cast (NumberFieldFinitePlace.residueCharacteristic_prime b.1).one_lt

end LeanFormal.IUT.XiFPaper.QVPilotThetaHullNestingActual

end
