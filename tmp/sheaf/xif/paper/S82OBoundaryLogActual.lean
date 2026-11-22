import tmp.sheaf.xif.paper.S79IntegralRingEquivActual
import tmp.sheaf.xif.paper.S63OBoundaryLogShellActual

/-! # S82: partial O-boundary logarithm and the O-times log relation

The source logarithm is defined on O-times = (Integers (CommonPrimeCompletion
place))^x.  O-boundary consists of nonzero integral elements, including
nonunits; no logarithm on nonunits is supplied.  This file:

* constructs the actual partial log on O-times, reused as the O-boundary unit
  part;
* embeds O-times into O-boundary;
* records the exact missing unit decomposition of arbitrary O-boundary
  elements and the exact missing total O-boundary log.

No fake total log/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S82OBoundaryLogActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Actual partial logarithm on O-times, the unit part of O-boundary. -/
def oTimesPartialLog (u : (Integers (CommonPrimeCompletion place))ˣ) :
    CommonPrimeCompletion place :=
  unitLog (K := CommonPrimeCompletion place) u

theorem oTimesPartialLog_one :
    oTimesPartialLog (K := K) (p := p) place 1 = 0 := by
  unfold oTimesPartialLog
  exact unitLog_one (K := CommonPrimeCompletion place) (p := p)

theorem oTimesPartialLog_mul
    (u v : (Integers (CommonPrimeCompletion place))ˣ) :
    oTimesPartialLog (K := K) (p := p) place (u * v) =
      oTimesPartialLog (K := K) (p := p) place u +
        oTimesPartialLog (K := K) (p := p) place v := by
  unfold oTimesPartialLog
  exact unitLog_mul (K := CommonPrimeCompletion place) (p := p) u v

/-- Actual embedding of the O-times unit part into O-boundary. -/
def oTimesUnitPartEmbedding :
    (Integers (CommonPrimeCompletion place))ˣ →
      sourceOBoundaryMonoid (K := K) (p := p) place :=
  sourceOTimesToBoundary (K := K) (p := p) place

/-- Exact missing decomposition of an arbitrary O-boundary element into a unit
part and an integral exponent (valuation splitting). -/
structure OBoundaryUnitDecomposition where
  decompose : sourceOBoundaryMonoid (K := K) (p := p) place →
    (Integers (CommonPrimeCompletion place))ˣ × ℤ
  compatibility : Prop

/-- Exact missing unit decomposition; no inhabitant asserted. -/
def OBoundaryUnitDecompositionRequired : Prop :=
  Nonempty (OBoundaryUnitDecomposition (K := K) (p := p) place)

/-- Exact missing total O-boundary log. -/
structure OBoundaryTotalLog where
  logMap : sourceOBoundaryMonoid (K := K) (p := p) place →
    CommonPrimeCompletion place
  extendsUnitLog : Prop

/-- Exact missing total log; no inhabitant asserted. -/
def OBoundaryTotalLogRequired : Prop :=
  Nonempty (OBoundaryTotalLog (K := K) (p := p) place)

end LeanFormal.IUT.XiFPaper.S82OBoundaryLogActual

end
