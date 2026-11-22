import tmp.sheaf.xif.paper.S143dQuotientLogVolumeActual

/-! # S148: quotient normalized log-volume on O-times and the extra integer coordinate

S143d quotients the normalized first coordinate by the actual unit-log range.
This file:

* identifies the quotient normalized log-volume on O-times with the source
  log-shell integral-unit log;
* constructs the combined quotient log-volume (K / unitLogRange) x Z, whose
  first component is the invariant normalized part and whose second component
  is the formal logPi integer exponent;
* proves that under uniformizer change the first component is invariant and only
  the integer coordinate changes.

No fake field log/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S148QuotientLogVolumeSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual
open LeanFormal.IUT.XiFPaper.S101UniformizerChangeActual
open LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual
open LeanFormal.IUT.XiFPaper.S126FormalBoundaryLogUseActual
open LeanFormal.IUT.XiFPaper.S132FormalLogVolumeActual
open LeanFormal.IUT.XiFPaper.S143dQuotientLogVolumeActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- For the chosen S111 uniformizer, the arbitrary-uniformizer formal log is
exactly boundaryLogFormal. -/
theorem boundaryLogFormalFor_dvr_eq
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    boundaryLogFormalFor (K := K) (p := p) place
        (dvrUniformizer (K := K) (p := p) place)
        (dvrUniformizer_irreducible (K := K) (p := p) place) x =
      boundaryLogFormal (K := K) (p := p) place x := by
  have huniq := boundaryUnitDecomposition_unique (K := K) (p := p) place x
    (boundaryUnitDecompositionFor (K := K) (p := p) place
      (dvrUniformizer (K := K) (p := p) place)
      (dvrUniformizer_irreducible (K := K) (p := p) place) x).n
    (boundaryUnitDecompositionFor (K := K) (p := p) place
      (dvrUniformizer (K := K) (p := p) place)
      (dvrUniformizer_irreducible (K := K) (p := p) place) x).u
    (boundaryUnitDecompositionFor (K := K) (p := p) place
      (dvrUniformizer (K := K) (p := p) place)
      (dvrUniformizer_irreducible (K := K) (p := p) place) x).eq
  unfold boundaryLogFormalFor boundaryLogFormal
  dsimp only
  rw [← huniq.2, ← huniq.1]

/-- The source log-shell normalized log quotient. -/
noncomputable def sourceLogShellNormalizedQuot
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    (CommonPrimeCompletion place) ⧸ unitLogRange (K := K) (p := p) place :=
  QuotientAddGroup.mk' (unitLogRange (K := K) (p := p) place)
    (unitLog (K := CommonPrimeCompletion place) u)

/-- On O-times, the S143d quotient normalized log-volume equals the source
log-shell normalized log quotient. -/
theorem normalizedLogVolumeQuot_on_units_eq_source
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    normalizedLogVolumeQuot (K := K) (p := p) place
        (dvrUniformizer (K := K) (p := p) place)
        (dvrUniformizer_irreducible (K := K) (p := p) place)
        (sourceOTimesToBoundary (K := K) (p := p) place u) =
      sourceLogShellNormalizedQuot (K := K) (p := p) place u := by
  unfold normalizedLogVolumeQuot sourceLogShellNormalizedQuot
  rw [boundaryLogFormalFor_dvr_eq]
  rw [boundaryLogFormal_ext_unit]
  rfl

/-- Combined quotient log-volume: invariant normalized quotient plus the formal
integer logPi coordinate. -/
noncomputable def combinedLogVolume
    (pi : Integers (CommonPrimeCompletion place)) (hpi : Irreducible pi)
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    ((CommonPrimeCompletion place) ⧸ unitLogRange (K := K) (p := p) place) × ℤ :=
  (normalizedLogVolumeQuot (K := K) (p := p) place pi hpi x,
    (boundaryLogFormalFor (K := K) (p := p) place pi hpi x).2)

/-- Uniformizer change: the normalized quotient component is invariant; only
the integer formal-logPi coordinate changes. -/
theorem combinedLogVolume_uniformizer_change
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    (combinedLogVolume (K := K) (p := p) place pi hpi x).1 =
      (combinedLogVolume (K := K) (p := p) place pi' hpi' x).1 ∧
    (combinedLogVolume (K := K) (p := p) place pi hpi x).2 -
        (combinedLogVolume (K := K) (p := p) place pi' hpi' x).2 =
      ((boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).n : ℤ) -
        ((boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).n : ℤ) := by
  constructor
  · exact normalizedLogVolumeQuot_uniformizer_invariant (K := K) (p := p) place
      pi pi' hpi hpi' x
  · unfold combinedLogVolume
    simp only
    exact boundaryLogFormalFor_change_integer (K := K) (p := p) place
      pi pi' hpi hpi' x

end LeanFormal.IUT.XiFPaper.S148QuotientLogVolumeSourceActual

end
