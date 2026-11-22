import tmp.sheaf.xif.paper.S3132FiberBridgeFromRepoToolsActual
import Iut.Foundations.SourceFinitePlaceMLFBase

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3132UniformFiberMissingActual
open LeanFormal.IUT.XiFPaper.S3132FiberBridgeFromRepoToolsActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132FiberExternalCompletionBridgeActual

universe u v uv upi umon ui

/-!
# task-65 (2): the fiber comparison via the EXTERNAL repo tool `completionRingHom`

**Component, not a paper object.**  Owner: hull.  Consumers: task-62/65 fiber
missing; mainline registry.

The external library `Iut` (lake lib, srcDir tmp/local-cft-port) provides the
actual rational scalar-to-full completion ring homomorphism
(`Iut/Foundations/SourceFinitePlaceMLFBase.lean:41`):

    completionRingHom (place : FinitePlace K) :
      Completion (comap (k := Q) place) →+* Completion place

This is exactly the rational completion → C3 completion map needed for the fiber
half of the uniform HDD/C3 comparison.  Applying it at the selected C3 tensor
place gives `c3CompletionRingHom`, from the rational place `rationalPlaceOfC3`
under the C3 place to the actual C3 completion.

**Data instantiation (not mathematics).**  The remaining inputs are:
* `comap_eq`: all selected C3 tensor places lie over the SAME rational place `v`
  (a single-prime condition; the actual place provenance `placeToMod` is not
  exposed by `OriginalInput`, see the dual-contract-alignment note and the
  all-place negative result);
* `bij`: `completionRingHom` is bijective at each selected place — the paper's
  local-degree-one condition `e = f = 1` (IUT III, Proposition 3.2, (ii),
  pp. 97-99).
Given this data, `missingFiberAt_of_actualPlaceData` constructs the fiber
comparison at the fixed rational place.  The all-`v` form of the task-38 datum is
OVER-STRONG (ring isomorphisms from the same fiber can exist only at rational
places whose residue characteristic matches `C3.p`); the faithful form is the
place-restricted `MissingFiberCompletionComparisonAt`.
Pages: IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.7, (ii), (v),
pp. 108-112.
-/

/-- The rational place under a selected C3 tensor place. -/
noncomputable def rationalPlaceOfC3
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) (i : C3.tensorIndex) :
    NumberField.FinitePlace ℚ :=
  Iut.ThetaFinitePlace.comap (k := ℚ) (c3LogShellPlace C3 i).val

/-- The actual rational completion → C3 completion ring homomorphism (external
repo tool `completionRingHom`). -/
noncomputable def c3CompletionRingHom
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) (i : C3.tensorIndex) :
    Completion (rationalPlaceOfC3 C3 i) →+* Completion (c3LogShellPlace C3 i).val :=
  Iut.ThetaFinitePlace.completionRingHom (c3LogShellPlace C3 i).val

/-- **Data instantiation for the fiber half (place-restricted).**  (i) all
selected C3 places lie over the same rational place; (ii) the rational-to-C3
completion map is bijective at each selected place (local-degree-one `e = f = 1`). -/
structure ActualPlaceDataForC3
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (v : NumberField.FinitePlace ℚ)
    (e : Fin D.rank ≃ C3.tensorIndex) : Prop where
  comap_eq : ∀ i : Fin D.rank, rationalPlaceOfC3 C3 (e i) = v
  bij : ∀ i : Fin D.rank, Function.Bijective (c3CompletionRingHom C3 (e i))

/-- **The faithful (place-restricted) fiber comparison datum.** -/
structure MissingFiberCompletionComparisonAt
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice)
    {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (v : NumberField.FinitePlace ℚ)
    (e : Fin D.rank ≃ C3.tensorIndex) where
  completionEquiv : (i : Fin D.rank) →
    Completion v ≃+* Completion (c3LogShellPlace C3 (e i)).val

/-- **Construction of the fiber comparison at the fixed rational place** from the
external completion map plus the data instantiation. -/
noncomputable def fiberCompletionEquivAt_of_actualPlaceData
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (v : NumberField.FinitePlace ℚ)
    (e : Fin D.rank ≃ C3.tensorIndex)
    (h : ActualPlaceDataForC3 ID C3 D v e) (i : Fin D.rank) :
    Completion v ≃+* Completion (c3LogShellPlace C3 (e i)).val := by
  have hring : Completion (rationalPlaceOfC3 C3 (e i)) ≃+*
      Completion (c3LogShellPlace C3 (e i)).val :=
    RingEquiv.ofBijective (c3CompletionRingHom C3 (e i)) (h.bij i)
  rw [h.comap_eq i] at hring
  exact hring

/-- The place-restricted fiber comparison, constructed from the data. -/
theorem missingFiberAt_of_actualPlaceData
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (v : NumberField.FinitePlace ℚ)
    (e : Fin D.rank ≃ C3.tensorIndex)
    (h : ActualPlaceDataForC3 ID C3 D v e) :
    Nonempty (MissingFiberCompletionComparisonAt ID C3 D v e) :=
  ⟨{ completionEquiv :=
      fun i => fiberCompletionEquivAt_of_actualPlaceData ID C3 D v e h i }⟩

/-- **Projection:** the (over-strong) all-places fiber datum restricts to the
faithful place-restricted datum at every rational place. -/
theorem missingFiberAt_of_allPlacesData
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (ID : Input Label Choice) {l : PrimeGeFive} {V : Type}
    {I2 : OriginalInput.{0, 0, upi, umon, ui} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I2)
    (D : S1300HDDHullDetSource ID)
    (e : Fin D.rank ≃ C3.tensorIndex)
    (M : MissingFiberCompletionComparisonData ID C3 D e)
    (v : NumberField.FinitePlace ℚ) :
    Nonempty (MissingFiberCompletionComparisonAt ID C3 D v e) :=
  ⟨{ completionEquiv := fun i => M.completionEquiv v i }⟩

#check rationalPlaceOfC3
#check c3CompletionRingHom
#check ActualPlaceDataForC3
#check MissingFiberCompletionComparisonAt
#check missingFiberAt_of_actualPlaceData
#check missingFiberAt_of_allPlacesData

end LeanFormal.IUT.XiFPaper.S3132FiberExternalCompletionBridgeActual

end
