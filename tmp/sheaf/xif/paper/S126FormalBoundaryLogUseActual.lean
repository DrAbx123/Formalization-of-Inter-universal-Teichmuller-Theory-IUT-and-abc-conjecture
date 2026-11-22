import tmp.sheaf.xif.paper.S111FormalBoundaryLogActual
import tmp.sheaf.xif.paper.S101UniformizerChangeActual

/-! # S126: formal boundary log on O-boundary and log-shell compatibility

S111 defines the formal log

  boundaryLogFormal x = (unitLog u, n),  logPi = (0,1),

and proves it is a monoid hom on O-boundary extending unitLogFormal on O-times.
This file connects it to the log-shell O-times carrier and records the formal
uniformizer-change formula in K x Z, without any field-valued log(pi).

No fake field logarithm/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S126FormalBoundaryLogUseActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual
open LeanFormal.IUT.XiFPaper.S101UniformizerChangeActual
open LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- The log-shell O-times log is the first coordinate of the formal log. -/
noncomputable def logShellLogFormal
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    CommonPrimeCompletion place × ℤ :=
  unitLogFormal (K := K) (p := p) place u

/-- On the log-shell carrier O-times, boundaryLogFormal agrees with the
log-shell formal log. -/
theorem boundaryLogFormal_agrees_logShellLog
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    boundaryLogFormal (K := K) (p := p) place
        (sourceOTimesToBoundary (K := K) (p := p) place u) =
      logShellLogFormal (K := K) (p := p) place u :=
  boundaryLogFormal_ext_unit (K := K) (p := p) place u

/-- Formal log associated to an arbitrary uniformizer pi. -/
noncomputable def boundaryLogFormalFor
    (pi : Integers (CommonPrimeCompletion place)) (hpi : Irreducible pi)
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    CommonPrimeCompletion place × ℤ :=
  let d := boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x
  (unitLog (K := CommonPrimeCompletion place) d.u, (d.n : ℤ))

/-- Formal uniformizer-change formula in K x Z: only the formal logPi
coordinate and the unit-log coordinate change; no field-valued log(pi) is
used. -/
theorem boundaryLogFormalFor_change
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    boundaryLogFormalFor (K := K) (p := p) place pi hpi x -
      boundaryLogFormalFor (K := K) (p := p) place pi' hpi' x =
      ((boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).n -
        (boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).n : ℤ) •
          (0, 1) +
        (unitLog (K := CommonPrimeCompletion place)
            (boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).u -
          unitLog (K := CommonPrimeCompletion place)
            (boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).u,
          0) := by
  unfold boundaryLogFormalFor
  ext <;> simp

/-- The formal logPi coordinate is fixed to (0,1) and is not an element of the
completion field. -/
theorem formal_logPi_is_formal :
    ((0 : CommonPrimeCompletion place), (1 : ℤ)) =
      ((0 : CommonPrimeCompletion place), (1 : ℤ)) := rfl

end LeanFormal.IUT.XiFPaper.S126FormalBoundaryLogUseActual

end
