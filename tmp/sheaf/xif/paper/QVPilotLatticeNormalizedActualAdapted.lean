import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # qVFamily lattice coefficients and the normalized q-pilot log-volume

The reusable actual formula

  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic

states that for the fractional lattice F(c) and the holomorphic lattice O_hol,

  mu_log((F(c) * O_hol)) = - (sum_i c_i) * log p.

This file converts the actual qVFamily order/exponent data into the lattice
coefficients c_i:

  c_b = order(qVFamily b) * localResidueDegree(F-place over b)
        * (log(residueNormBase b) / log p).

The last factor is the base residue degree written in p-log units, so that
c_b * log p = order * localResidueDegree * log(residueNormBase b), which is the
actual qVFamily local log-magnitude.

The resulting q-pilot lattice log-volume is

  qPilotLatticeNormalizedLogVolume = - sum_b c_b * log p,

which is negative and has the same sign as the native qVFamily signed scalar
nativeQVPilotNormalizedSignedLogVolume.  The exact comparison target with the
native scalar is recorded, not asserted.

No normalization is rebuilt; no fake equality or inequality. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVPilotLatticeNormalizedActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual base residue degree of b written in p-log units. -/
noncomputable def qVFamilyBasePLogCoefficient
    (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log (residueNormBase b.1) / Real.log (T.arithmetic.Fmod.p : Real)

/-- The actual qVFamily lattice coefficient c_b: qVFamily order times the
relative residue degree times the base residue degree in p-log units. -/
noncomputable def qVFamilyLatticeCoefficient
    (b : Bad (nativePlaceSelection T)) : Real :=
  ((qVFamily T b).order : Real) *
    (localResidueDegree (k := T.arithmetic.Fmod)
      ((nativeBadLift T).lift b) : Real) *
    qVFamilyBasePLogCoefficient T b

/-- The q-pilot lattice normalized log-volume computed from the actual
fractional-lattice formula: - (sum_b c_b) * log p. -/
noncomputable def qPilotLatticeNormalizedLogVolume : Real :=
  - (∑ b : Bad (nativePlaceSelection T),
      qVFamilyLatticeCoefficient T b) * Real.log (T.arithmetic.Fmod.p : Real)

/-- Exact formula for the q-pilot lattice log-volume. -/
theorem qPilotLatticeNormalizedLogVolume_eq :
    qPilotLatticeNormalizedLogVolume T =
      - (∑ b : Bad (nativePlaceSelection T),
          qVFamilyLatticeCoefficient T b) *
        Real.log (T.arithmetic.Fmod.p : Real) := rfl

/-- The local qVFamily lattice term expands to the actual order times the
relative residue degree times the base residue log. -/
theorem qVFamilyLatticeCoefficient_eq_log
    (b : Bad (nativePlaceSelection T)) :
    qVFamilyLatticeCoefficient T b *
        Real.log (T.arithmetic.Fmod.p : Real) =
      ((qVFamily T b).order : Real) *
        (localResidueDegree (k := T.arithmetic.Fmod)
          ((nativeBadLift T).lift b) : Real) *
        Real.log (residueNormBase b.1) := by
  unfold qVFamilyLatticeCoefficient qVFamilyBasePLogCoefficient
  have hlogp : Real.log (T.arithmetic.Fmod.p : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Fact.out : Nat.Prime T.arithmetic.Fmod.p).pos
    · exact_mod_cast (Fact.out : Nat.Prime T.arithmetic.Fmod.p).ne_one
  field_simp [hlogp]
  ring

/-- Exact sign formula: the q-pilot lattice scalar is the negative of the sum
of the actual qVFamily local magnitudes. -/
theorem qPilotLatticeNormalizedLogVolume_eq_neg_sum_localMagnitude :
    qPilotLatticeNormalizedLogVolume T =
      - (∑ b : Bad (nativePlaceSelection T),
          nativeQVPilotLocalMagnitude T b) := by
  unfold qPilotLatticeNormalizedLogVolume nativeQVPilotLocalMagnitude
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  -- each coefficient * log p is the local magnitude of qVFamily b
  rw [qVFamilyLatticeCoefficient_eq_log]
  -- qVFamily_localLogMagnitude_eq supplies the remaining actual identity
  exact (qVFamily_localLogMagnitude_eq (X := ⟨T, by infer_instance⟩) b).symm

/-- Exact comparison target with the native signed qVFamily scalar. -/
def QVPilotLatticeVsNativeSignedTarget : Prop :=
  qPilotLatticeNormalizedLogVolume T =
    nativeQVPilotNormalizedSignedLogVolume T

/-- The target is exactly the identity of the lattice scalar with the native
signed qVFamily scalar. -/
theorem qPilotLatticeVsNativeSignedTarget_iff :
    QVPilotLatticeVsNativeSignedTarget T ↔
      qPilotLatticeNormalizedLogVolume T =
        nativeQVPilotNormalizedSignedLogVolume T := Iff.rfl

end LeanFormal.IUT.XiFPaper.QVPilotLatticeNormalizedActualAdapted

end
