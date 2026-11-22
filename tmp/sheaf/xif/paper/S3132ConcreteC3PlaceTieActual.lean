import tmp.sheaf.xif.paper.PrimeStripLogShellActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36PacketNumberField

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1200000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PacketNumberFieldConstruction
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual

namespace LeanFormal.IUT.XiFPaper.S3132ConcreteC3PlaceTieActual

/-!
# task-65 (2): the exact model tie between the abstract C3 tensor places and the
concrete Example 3.6 packet places

**Component, not a paper object.**  Owner: hull.  Consumers: mainline registry.

No concrete `OriginalInput` / `SourcePilotRegionData` instantiation exists in the
tree whose selected C3 tensor places are the concrete Example 3.6 packet places
(greps: `OriginalInput` appears only as variables/parameters; no constructor
definition).  The exact identification needed to instantiate
`ActualPlaceDataForC3` for the model is therefore recorded here as a minimal
`Prop`:

* arithmetic tie: `I.initial.arithmetic.Fmod = packetNumberField = Q(i)`;
* prime tie: `C3.p = 5`;
* tensor-place tie: every selected C3 tensor place (as a `FinitePlaceAtPrime`)
  is the concrete packet place `packetFinitePlace`, expressed heterogeneously
  (`HEq`) because the source place type is an `OriginalInput`-dependent subtype.

All three are exact missing model data, not missing mathematics: their concrete
counterparts on the packet side are already proved
(`packet_completion_finrank_eq_one`, `packet_completionMap_surjective`,
`sourceTheater_arithmetic_Fmod_eq_packet`).  Pages: IUT III, Proposition 3.2,
(ii), pp. 97-99; Proposition 3.7, (ii), (v), pp. 108-112.
-/

/-- Exact model tie: the abstract C3 tensor places are the concrete Example 3.6
packet places.  Minimal exact missing (all three fields recorded). -/
structure MissingConcreteC3PlaceTie
    {l : PrimeGeFive} {V : Type}
    (I : OriginalInput l V)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop where
  fmod_tie : I.initial.arithmetic.Fmod = packetNumberField
  prime_tie : C3.p = 5
  tensorPlace_tie : ∀ i : C3.tensorIndex,
    HEq (c3LogShellPlace C3 i) packetFinitePlace

/-- The exact missing tie as a single `Prop`. -/
abbrev MissingConcreteC3PlaceTieProp
    {l : PrimeGeFive} {V : Type}
    (I : OriginalInput l V)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  Nonempty (MissingConcreteC3PlaceTie I C3)

#check MissingConcreteC3PlaceTie
#check MissingConcreteC3PlaceTieProp

end LeanFormal.IUT.XiFPaper.S3132ConcreteC3PlaceTieActual

end
