import tmp.sheaf.xif.paper.S60OTriangleBoundaryActual
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

/-! # S63: O-boundary and the local log-shell carrier

The actual local log-shell datum sourceLocalLogShellDatum uses

  Units = (Integers (CommonPrimeCompletion place))^x,

the unit group O-times of the actual norm valuation ring, not O-triangle and
not O-boundary.  This file proves the carrier identification and constructs the
actual map from O-times into the O-boundary monoid (nonzero integral elements of
the norm valuation ring).

S56's O-triangle/O-boundary used NumberFieldFinitePlace.CompletionIntegers; the
log-shell uses the norm valuation ring Integers.  The identification of these
two integral rings is recorded as an exact missing source equality; it is not
assumed.

No fake equality/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- The source local log-shell datum uses the integral-unit carrier O-times. -/
theorem sourceLogShellUnits_eq_integralUnits :
    (sourceLocalLogShellDatum (p := p) place).Units =
      (Integers (CommonPrimeCompletion place))ˣ := rfl

/-- Actual source O-boundary: nonzero elements of the norm integral ring. -/
noncomputable def sourceOBoundaryMonoid :
    Submonoid (CommonPrimeCompletion place) where
  carrier := {x | x ∈ Integers (CommonPrimeCompletion place) ∧ x ≠ 0}
  one_mem' := by
    refine ⟨?_, one_ne_zero⟩
    exact (Integers (CommonPrimeCompletion place)).one_mem
  mul_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    refine ⟨?_, mul_ne_zero hx0 hy0⟩
    exact (Integers (CommonPrimeCompletion place)).mul_mem hx hy

/-- Actual map O-times -> O-boundary for the source integral ring. -/
def sourceOTimesToBoundary
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    sourceOBoundaryMonoid (K := K) (p := p) place :=
  ⟨(u : CommonPrimeCompletion place),
    u.val.property,
    fun h => Units.ne_zero u (Subtype.ext h)⟩

/-- Exact missing equality between the norm integral ring Integers and the
number-field completion integral ring CompletionIntegers used in S56. -/
def CompletionIntegersEqIntegers : Prop :=
  (CompletionIntegers place.val : Type u) = Integers (CommonPrimeCompletion place)

/-- Exact missing log/O-boundary relation: the log-shell is built from O-times;
a logarithm on all of O-boundary is not supplied by the source. -/
structure OBoundaryLogShellGap where
  boundary : Type u
  boundary_eq : boundary = sourceOBoundaryMonoid (K := K) (p := p) place
  logMap : boundary → Additive Real
  unitMap : (Integers (CommonPrimeCompletion place))ˣ →
    sourceOBoundaryMonoid (K := K) (p := p) place
  unitMap_eq : unitMap = sourceOTimesToBoundary (K := K) (p := p) place

/-- Exact O-boundary/log-shell requirement; no inhabitant asserted. -/
def OBoundaryLogShellRequired : Prop :=
  Nonempty (OBoundaryLogShellGap (K := K) (p := p) place)

end LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual

end
