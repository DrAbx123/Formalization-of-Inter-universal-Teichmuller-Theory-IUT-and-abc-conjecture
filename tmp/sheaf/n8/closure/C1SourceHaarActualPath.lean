import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import tmp.sheaf.n8.closure.C1QuotientFiberData
import tmp.sheaf.n8.closure.C1ActualSourceInput

/-!
# C1 sourceHaar actual path (V = Unit, q = 1)

SourceUnitRegionHaarDataActual is now green.  This file consumes it directly
and actually constructs:

- sourceHaarActualOriginalInput S : OriginalInput l Unit;
- sourceHaarActualImageRealization S : input.SourceImageRealization ();
- q = 1 at every theater index;
- the corrected C1 quotient target C1PlaceQuotientFiberData at Fmod.

The old SourceInputBinding consumer over this V = Unit input would need
Unit ~ NumberFieldPlaceIndex.  Unit is a subsingleton, so whenever the place
index is nontrivial the old binding is empty; this is the decisive no-go for
the old target on the sourceHaar path.  The corrected consumer below does not
use that equivalence: it carries the actual input/R/q data and the actual
quotient-by-kernel target.  No arbitrary place equivalence is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1SourceHaarActualPath

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1ActualSourceInput
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua

variable {l : PrimeGeFive}

/-- Actual sourceHaar source data: input, selected (), realization, q = 1. -/
structure SourceHaarActualRPath (S : SourceDefinition31Data.{ua} l) where
  input : OriginalInput.{ua, 0, 0, 0, 0} l Unit
  selected : Unit
  realization : input.SourceImageRealization selected
  q_one : ∀ n m : Int, (input.theaterAt n m).thetaPacket.q = 1

/-- Actual construction from the green SourceUnitRegionHaarDataActual. -/
noncomputable def sourceHaarActualRPath (S : SourceDefinition31Data.{ua} l) :
    SourceHaarActualRPath S where
  input := sourceHaarActualOriginalInput (l := l) S
  selected := ()
  realization := sourceHaarActualImageRealization (l := l) S
  q_one := sourceHaarActual_originalInput_theta_q (l := l) S

/-- The corrected C1 consumer on the sourceHaar path: actual R data plus the
actual quotient-by-kernel target.  It deliberately has no Unit-to-place-index
field and no old full-unit fiberMonEquiv. -/
structure SourceHaarActualCorrectedConsumer
    (S : SourceDefinition31Data.{ua} l) where
  rPath : SourceHaarActualRPath S
  quotientTarget : C1PlaceQuotientFiberData (F := S.arithmetic.Fmod)

/-- Actual corrected consumer, zero sorry. -/
noncomputable def sourceHaarActualCorrectedConsumer
    (S : SourceDefinition31Data.{ua} l) :
    SourceHaarActualCorrectedConsumer S where
  rPath := sourceHaarActualRPath S
  quotientTarget := c1PlaceQuotientFiberData (F := S.arithmetic.Fmod)

theorem sourceHaarActualCorrectedConsumer_nonempty
    (S : SourceDefinition31Data.{ua} l) :
    Nonempty (SourceHaarActualCorrectedConsumer S) :=
  ⟨sourceHaarActualCorrectedConsumer S⟩

/-- Actual q = 1 statement on the sourceHaar path. -/
theorem sourceHaarActual_q_one (S : SourceDefinition31Data.{ua} l) (n m : Int) :
    ((sourceHaarActualOriginalInput (l := l) S).theaterAt n m).thetaPacket.q = 1 :=
  sourceHaarActual_originalInput_theta_q (l := l) S n m

/-- Decisive no-go for the old SourceInputBinding on the sourceHaar path: if
the number-field place index is nontrivial, Unit cannot be equivalent to it,
so the old binding over V = Unit is empty. -/
theorem no_sourceInputBinding_sourceHaarActual_of_nontrivial_placeIndex
    (S : SourceDefinition31Data.{ua} l)
    [Nontrivial (NumberFieldPlaceIndex
      (F := (sourceHaarActualOriginalInput (l := l) S).initial.arithmetic.Fmod))] :
    IsEmpty (SourceInputBinding (sourceHaarActualOriginalInput (l := l) S)) := by
  refine ⟨fun O => ?_⟩
  let e := O.place.placeEquiv
  have hsub : Subsingleton (NumberFieldPlaceIndex
      (F := (sourceHaarActualOriginalInput (l := l) S).initial.arithmetic.Fmod)) :=
    ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩
  letI : Subsingleton (NumberFieldPlaceIndex
      (F := (sourceHaarActualOriginalInput (l := l) S).initial.arithmetic.Fmod)) := hsub
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (NumberFieldPlaceIndex
    (F := (sourceHaarActualOriginalInput (l := l) S).initial.arithmetic.Fmod))).exists_pair_ne
  exact hab (Subsingleton.elim a b)

end LeanFormal.IUT.N8Closure.C1SourceHaarActualPath
