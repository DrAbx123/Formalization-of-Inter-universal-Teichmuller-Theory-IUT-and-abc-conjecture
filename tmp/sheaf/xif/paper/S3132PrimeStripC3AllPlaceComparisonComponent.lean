import tmp.sheaf.xif.paper.PrimeStripLogShellActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132PrimeStripC3AllPlaceComparisonComponent

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-!
# All-place PrimeStrip <-> C3 tensor-index comparison: component analysis

**Component, not a paper object.**  Consumers: the fixed-C Batch A package
`S3130QCLeHCData` and the mainline/lattice `qThetaPilotLogVolumeComparison`
(via the source prime-strip index).

The tree records the all-place identification of the source prime-strip index
`V` with the C3 tensor index as the exact missing record
`PrimeStripC3PlaceComparison` (`PrimeStripLogShellActual.lean`):

* `indexEquiv : V ≃ C3.tensorIndex`;
* `stripPlace : V → FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p`;
* `stripPlace_eq : forall v, stripPlace v =
    C3.tensorPlaces (indexEquiv v) (C3.tensorTuple (indexEquiv v))`.

This module analyses that record against the actual data:

* **Trivialization (negative result, recorded as such).**  Because `stripPlace`
  is *defined* from the C3 tensor places, **any** index equivalence
  `V ≃ C3.tensorIndex` (in particular any arbitrary cardinality matching)
  yields a `PrimeStripC3PlaceComparison`; conversely the record projects to such
  an equivalence.  Hence the existing record is *not* paper-faithful by itself:
  it imposes no link to the actual source places.
* **Forcing.**  For any `P : PrimeStripC3PlaceComparison`, the place map is
  forced to be the C3 tensor places along `P.indexEquiv`, so it carries no
  independent source information.
* **Faithful data required (exact Missing).**  The paper-faithful comparison
  needs the *actual all-place map* from the source initial theta data,
  `placeToMod : V → NumberFieldPlace Fmod` (with bijectivity and the
  residue-characteristic condition), together with the equality of its finite
  members with the selected C3 tensor places.  That map exists in
  `SourceInitialThetaData` (`SourceInitialThetaData.lean:357-362`) but
  `OriginalInput` exposes only `SourceDefinition31Data`, whose fields are the
  selected/bad place *types* (`SourceDefinition31Boundary.lean:667-690`), not
  the V-indexed place map.  It is therefore additional source data, recorded
  here as the exact missing input; it is not fabricated.
* **Relation to the qpilot bad-only comparison.**  The qpilot comparison is
  `Bad (nativePlaceSelection T) ≃ C3.tensorIndex` with provenance from the
  native bad places; the all-place comparison above is on the *whole* source
  index `V`.  If both are available, the all-place `stripPlace` restricted to
  the bad indices must agree with the qpilot bad place map; that compatibility
  is another exact identification, not derivable here.

Source: IUT III, Theorem 3.11 (pp. 160-162); IUT IV, Theorem 1.10 proof
(pp. 26-27); IUT III, Definition 3.1 (source initial theta data, pp. 30-40).
-/

/-- **Trivialization (negative result).**  Any index equivalence `V ≃ C3.tensorIndex`
produces the existing all-place comparison record, with the place map defined by
the C3 tensor places.  Thus the record alone does not encode source-place
provenance. -/
theorem primeStripC3PlaceComparison_of_indexEquiv
    (e : V ≃ C3.tensorIndex) :
    Nonempty (PrimeStripC3PlaceComparison (V := V) (I := I) C3) :=
  ⟨{ indexEquiv := e,
      stripPlace := fun v => C3.tensorPlaces (e v) (C3.tensorTuple (e v)),
      stripPlace_eq := fun v => rfl }⟩

/-- **Characterization.**  The existing all-place comparison is equivalent to the
bare existence of an index equivalence `V ≃ C3.tensorIndex`. -/
theorem primeStripC3PlaceComparisonRequired_iff_indexEquiv :
    PrimeStripC3PlaceComparisonRequired (V := V) (I := I) C3 ↔
      Nonempty (V ≃ C3.tensorIndex) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.indexEquiv⟩
  · rintro ⟨e⟩
    exact primeStripC3PlaceComparison_of_indexEquiv (I := I) C3 e

/-- **Cardinality form.**  For a finite source index, the existing all-place
comparison is equivalent to the cardinality equality
`#V = #C3.tensorIndex` — i.e. to a purely numerical condition.  This is the
negative result: cardinality matching is not paper-faithful. -/
theorem primeStripC3PlaceComparisonRequired_iff_card [Fintype V] :
    PrimeStripC3PlaceComparisonRequired (V := V) (I := I) C3 ↔
      Fintype.card V = Fintype.card C3.tensorIndex :=
  (primeStripC3PlaceComparisonRequired_iff_indexEquiv (I := I) C3).trans
    (Fintype.card_eq).symm

/-- **Forcing of the place map.**  Every all-place comparison record has its
place map forced to be the C3 tensor places along its index equivalence; it
carries no independent source-place information. -/
theorem primeStripC3PlaceComparison_stripPlace_forcing
    (P : PrimeStripC3PlaceComparison (V := V) (I := I) C3) :
    P.stripPlace = fun v =>
      C3.tensorPlaces (P.indexEquiv v) (C3.tensorTuple (P.indexEquiv v)) :=
  funext fun v => P.stripPlace_eq v

#check primeStripC3PlaceComparison_of_indexEquiv
#check primeStripC3PlaceComparisonRequired_iff_indexEquiv
#check primeStripC3PlaceComparisonRequired_iff_card
#check primeStripC3PlaceComparison_stripPlace_forcing

end LeanFormal.IUT.XiFPaper.S3132PrimeStripC3AllPlaceComparisonComponent

end