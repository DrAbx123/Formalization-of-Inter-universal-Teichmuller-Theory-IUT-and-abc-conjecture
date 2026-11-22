import tmp.sheaf.xif.paper.S126FormalBoundaryLogUseActual
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

/-! # S132: normalized formal boundary log and source log-shell compatibility

The formal boundary log takes values in K x Z.  Its normalized (field) part is
the first coordinate, i.e. the unit logarithm; its integer coordinate is the
DVR exponent (the formal logPi coordinate).

The source log-shell datum uses the same integral-unit logMap.  This file proves
the actual compatibility between logShellLogFormal and that logMap, and records
the exact uniformizer-change behavior: only the integer formal-logPi coordinate
is a pure integer change; the field/unit-log part changes by the actual
unit-log difference and is NOT silently declared invariant.

No fake field logarithm/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S132FormalLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S101UniformizerChangeActual
open LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual
open LeanFormal.IUT.XiFPaper.S126FormalBoundaryLogUseActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Normalized formal log: forget the integer logPi coordinate, keeping the
actual field/unit-log coordinate. -/
noncomputable def boundaryLogNormalized
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    CommonPrimeCompletion place :=
  (boundaryLogFormal (K := K) (p := p) place x).1

/-- Integer formal-logPi coordinate of the boundary log. -/
noncomputable def boundaryLogInteger
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) : ℤ :=
  (boundaryLogFormal (K := K) (p := p) place x).2

/-- Compatibility with the source log-shell datum's actual logMap: the
normalized formal log is the additive form of the source integral-unit logMap. -/
theorem boundaryLogNormalized_eq_sourceLogMap
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    boundaryLogNormalized (K := K) (p := p) place
        (sourceOTimesToBoundary (K := K) (p := p) place u) =
      Multiplicative.toAdd
        ((sourceLocalLogShellDatum (p := p) place).logMap u) := by
  unfold boundaryLogNormalized
  rw [boundaryLogFormal_ext_unit]
  unfold unitLogFormal sourceLocalLogShellDatum
  change unitLog (K := CommonPrimeCompletion place) u =
    Multiplicative.toAdd
      (unitLogHom (K := CommonPrimeCompletion place) (p := p) u)
  rw [unitLogHom_toAdd_apply]

/-- Formal uniformizer-change formula for an arbitrary pair of uniformizers. -/
theorem boundaryLogFormalFor_change_normalized
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    (boundaryLogFormalFor (K := K) (p := p) place pi hpi x).1 -
        (boundaryLogFormalFor (K := K) (p := p) place pi' hpi' x).1 =
      unitLog (K := CommonPrimeCompletion place)
          (boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).u -
        unitLog (K := CommonPrimeCompletion place)
          (boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).u := by
  unfold boundaryLogFormalFor
  rfl

/-- The integer coordinate changes exactly by n - n'; this is the only part
that is a pure integer multiple of the formal logPi direction. -/
theorem boundaryLogFormalFor_change_integer
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    (boundaryLogFormalFor (K := K) (p := p) place pi hpi x).2 -
        (boundaryLogFormalFor (K := K) (p := p) place pi' hpi' x).2 =
      ((boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).n : ℤ) -
        ((boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).n : ℤ) := by
  unfold boundaryLogFormalFor
  rfl

/-- Exact uniformizer-change decomposition of the normalized part: the field
part changes by the actual unit-log difference, not by zero.  Normalization by
the integer logPi coordinate therefore leaves this unit-log correction. -/
theorem boundaryLogFormalFor_change_normalized_correction
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    (boundaryLogFormalFor (K := K) (p := p) place pi hpi x).1 -
        (boundaryLogFormalFor (K := K) (p := p) place pi' hpi' x).1 =
      unitLog (K := CommonPrimeCompletion place)
          (boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).u -
        unitLog (K := CommonPrimeCompletion place)
          (boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).u :=
  boundaryLogFormalFor_change_normalized (K := K) (p := p) place pi pi' hpi hpi' x

end LeanFormal.IUT.XiFPaper.S132FormalLogVolumeActual

end
