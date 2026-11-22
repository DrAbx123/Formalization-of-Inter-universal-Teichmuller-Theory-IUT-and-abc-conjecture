import tmp.sheaf.xif.paper.QVPilotLatticeNormalizedActual
import tmp.sheaf.xif.paper.QVFamThetaImageActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # qVFamily theta lattice coefficients and the theta hull log-volume

Audit first: arithmeticTupleCanonicalHull is the canonical unit-region hull,
independent of any theta value.  Its normalized log-volume therefore depends
only on the unit region and is not a paper Theta scalar.  The old
canonicalHull-normalized scalar cannot be used as -|log Theta|.

Correct construction: convert the actual qVFamily theta values to fractional
lattice coefficients.  The actual Haar formula

  mu_log((F(c) * O_hol)) = - (sum_i c_i) * log p

applies to the arithmetic fractional lattice, not to the canonical unit hull.
For a bad place b and signed label j, the theta value is

  qVFamilyThetaValue b j = qVFamilyQNorm b ^ (gaussExponent j).toNat,

so its lattice coefficient is

  c_{b,j} = (gaussExponent j).toNat * c_b,

where c_b is the qVFamily base lattice coefficient (order * relative residue
degree * base p-log degree).

The theta hull over the procession labels is the scaling with the minimal
gauss exponent on F_l^x, namely j = 1 (exponent 1).  Its actual log-volume is

  qVFamilyThetaHullLogVolume
    = - sum_b c_{b,1} * log p,

a nontrivial value depending on the actual qVFamily order/degree data, not the
zero/canonical-unit value.

The exact comparison/identification with the native qVFamily signed scalar is
recorded, not assumed.  No normalization is rebuilt.  No fake inequality or
equality.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamThetaLatticeHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVPilotLatticeNormalizedActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The canonical hull of the actual C6 data is the unit-region canonical hull. -/
theorem canonicalHull_is_unitRegionHull
    {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type*} [Fintype iota] {W : iota -> Type*}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu] :
    (C6ActualIQData.actual places tuple mu).hull =
      arithmeticTupleCanonicalHull places tuple := rfl

/-- The canonical-hull normalized log-volume is the unit-region normalized
log-volume; no theta value occurs. -/
theorem canonicalHull_normalizedLogVolume_eq
    {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type*} [Fintype iota] {W : iota -> Type*}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu] :
    (C6ActualIQData.actual places tuple mu).normalizedLogVolume =
      arithmeticTupleNormalizedLogVolume places tuple mu := rfl

/-- The actual qVFamily theta lattice coefficient c_{b,j}. -/
noncomputable def qVFamilyThetaLatticeCoefficient
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : Real :=
  (gaussExponent j.1).toNat *
    qVFamilyLatticeCoefficient T b

/-- The actual log of qVFamilyThetaValue b j in p-lattice units. -/
theorem qVFamilyThetaValue_log_eq_lattice
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    Real.log (qVFamilyThetaValue T b j) =
      - qVFamilyThetaLatticeCoefficient T b j *
        Real.log (T.arithmetic.Fmod.p : Real) := by
  rw [qVFamilyThetaValue_log]
  have hlogp : Real.log (T.arithmetic.Fmod.p : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime T.arithmetic.Fmod.p).pos
    · exact_mod_cast (Fact.out : Nat.Prime T.arithmetic.Fmod.p).ne_one
  unfold qVFamilyThetaLatticeCoefficient qVFamilyLatticeCoefficient
    qVFamilyBasePLogCoefficient
  field_simp [hlogp]
  ring

/-- The theta hull coefficient: the minimal F_l^x Gauss exponent is the j = 1
exponent, so the hull coefficient at b is c_{b,1}. -/
noncomputable def qVFamilyThetaHullLatticeCoefficient
    (b : Bad (nativePlaceSelection T)) : Real :=
  qVFamilyThetaLatticeCoefficient T b (oneSignedLabel (l := l))

/-- The actual nontrivial qVFamily theta hull log-volume. -/
noncomputable def qVFamilyThetaHullLogVolume : Real :=
  - (∑ b : Bad (nativePlaceSelection T),
      qVFamilyThetaHullLatticeCoefficient T b) *
    Real.log (T.arithmetic.Fmod.p : Real)

theorem qVFamilyThetaHullLogVolume_eq :
    qVFamilyThetaHullLogVolume T =
      - (∑ b : Bad (nativePlaceSelection T),
          qVFamilyThetaHullLatticeCoefficient T b) *
        Real.log (T.arithmetic.Fmod.p : Real) := rfl

/-- Exact comparison target with the native qVFamily signed scalar. -/
def QVFamThetaHullVsNativeSignedTarget : Prop :=
  qVFamilyThetaHullLogVolume T =
    nativeQVPilotNormalizedSignedLogVolume T

theorem qVFamThetaHullVsNativeSignedTarget_iff :
    QVFamThetaHullVsNativeSignedTarget T ↔
      qVFamilyThetaHullLogVolume T =
        nativeQVPilotNormalizedSignedLogVolume T := Iff.rfl

end LeanFormal.IUT.XiFPaper.QVFamThetaLatticeHullActual

end
