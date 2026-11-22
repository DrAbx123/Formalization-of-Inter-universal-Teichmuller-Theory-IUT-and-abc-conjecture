import tmp.sheaf.xif.paper.S82OBoundaryLogActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia

/-! # S87: DVR unit decomposition of O-boundary and choice-dependent log

The norm integral ring Integers K is a DVR.  Choose an actual uniformizer pi via
IsDiscreteValuationRing.exists_irreducible.  Every nonzero O-boundary element x
has x = u * pi^n with u a unit (eq_unit_mul_pow_irreducible).

Given a chosen logarithm logPi of pi, define boundaryLog x = n • logPi +
unitLog u.  The DVR decomposition and log are actual; the choice of pi and
logPi is noncanonical (recorded by BoundaryLogIndeterminacy).

No fake canonical log/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Actual uniformizer of the norm integral ring. -/
noncomputable def dvrUniformizer : Integers (CommonPrimeCompletion place) := by
  letI : IsDiscreteValuationRing (Integers (CommonPrimeCompletion place)) :=
    isDiscreteValuationRingIntegers (K := CommonPrimeCompletion place) (p := p)
  exact Classical.choose
    (IsDiscreteValuationRing.exists_irreducible
      (Integers (CommonPrimeCompletion place)))

theorem dvrUniformizer_irreducible :
    Irreducible (dvrUniformizer (K := K) (p := p) place) := by
  letI : IsDiscreteValuationRing (Integers (CommonPrimeCompletion place)) :=
    isDiscreteValuationRingIntegers (K := CommonPrimeCompletion place) (p := p)
  exact Classical.choose_spec
    (IsDiscreteValuationRing.exists_irreducible
      (Integers (CommonPrimeCompletion place)))

/-- Convert an O-boundary element to a nonzero element of the norm integral
ring. -/
def boundaryToIntegers
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    Integers (CommonPrimeCompletion place) :=
  ⟨x.1, x.2.1⟩

theorem boundaryToIntegers_ne_zero
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    boundaryToIntegers (K := K) (p := p) place x ≠ 0 := by
  intro h
  apply x.2.2
  exact congrArg Subtype.val h

/-- Actual DVR decomposition data for an O-boundary element. -/
structure OBoundaryUnitDecomp
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) where
  n : ℕ
  u : (Integers (CommonPrimeCompletion place))ˣ
  eq : (x : CommonPrimeCompletion place) =
    (u : CommonPrimeCompletion place) *
      ((dvrUniformizer (K := K) (p := p) place :
        Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^ n

/-- Actual DVR decomposition of an O-boundary element, using the chosen
uniformizer. -/
noncomputable def boundaryUnitDecomposition
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    OBoundaryUnitDecomp (K := K) (p := p) place x := by
  letI : IsDiscreteValuationRing (Integers (CommonPrimeCompletion place)) :=
    isDiscreteValuationRingIntegers (K := CommonPrimeCompletion place) (p := p)
  have hx := boundaryToIntegers_ne_zero (K := K) (p := p) place x
  let hh := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := boundaryToIntegers (K := K) (p := p) place x) hx
    (dvrUniformizer_irreducible (K := K) (p := p) place)
  let n := Classical.choose hh
  let u := Classical.choose (Classical.choose_spec hh)
  refine ⟨n, u, ?_⟩
  exact congrArg (fun z : Integers (CommonPrimeCompletion place) =>
    (z : CommonPrimeCompletion place))
    (Classical.choose_spec (Classical.choose_spec hh))

/-- The actual decomposition equality. -/
theorem boundaryUnitDecomposition_eq
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    (x : CommonPrimeCompletion place) =
      ((boundaryUnitDecomposition (K := K) (p := p) place x).u :
        CommonPrimeCompletion place) *
      ((dvrUniformizer (K := K) (p := p) place :
        Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) ^
        (boundaryUnitDecomposition (K := K) (p := p) place x).n :=
  (boundaryUnitDecomposition (K := K) (p := p) place x).eq

/-- Choice-dependent boundary log: log x = n • logPi + unitLog u. -/
noncomputable def boundaryLogWith
    (logPi : CommonPrimeCompletion place)
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    CommonPrimeCompletion place :=
  let d := boundaryUnitDecomposition (K := K) (p := p) place x
  (d.n : ℤ) • logPi +
    unitLog (K := CommonPrimeCompletion place) d.u

/-- The noncanonical choices in boundaryLogWith. -/
structure BoundaryLogIndeterminacy where
  uniformizer : Integers (CommonPrimeCompletion place)
  uniformizer_irreducible : Irreducible uniformizer
  logPi : CommonPrimeCompletion place

end LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual

end
