import tmp.sheaf.n8.closure.C1ActualSourceInput
import tmp.sheaf.n8.closure.C1QuotientFiberData
import tmp.sheaf.n8.closure.SourceInputBinding

/-!
# C1 actual image realization attempt / independence no-go

Decision: the corrected C1 quotient target does not require
SourceImageRealization.

Exact reasons:
1. SourceImageRealization is indexed by an old OriginalInput I and a place
   v : V: it needs posRealAction : Multiplicative R ->* (I.primeStripAt 0 0).Mon v
   plus degree_of_q.  NativeC1 supplies native places/local fields, not an old
   OriginalInput or its value monoid.
2. The only production R is sourceHaarActualImageRealization, for
   sourceHaarActualOriginalInput with V = Unit and q = 1; its production file
   SourceUnitRegionHaarDataActual.lean is currently red (errors ~303/304/306/514),
   and it is not tied to the native selected place.
3. The corrected target CorrectedC1ActualSourceInput and C1PlaceQuotientFiberData
   contain no SourceImageRealization field.  The actual nonempty theorem below
   constructs the corrected target with no R parameter.

Therefore R is irrelevant to the corrected C1 quotient target.  It remains a
separate gap only for legacy full-unit C4/C7 consumers.  No arbitrary R is
introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1ActualImageRealizationAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C1ActualSourceInput
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive}

/-- Corrected quotient target used by the C1 actual source input.  Its type has
no SourceImageRealization field. -/
abbrev CorrectedC1QuotientTarget (X : N8NativeInput l) : Type :=
  C1PlaceQuotientFiberData (F := X.S.arithmetic.Fmod)

/-- Actual corrected quotient target (zero sorry; no R). -/
theorem correctedC1QuotientTarget_actual (X : N8NativeInput l) :
    Nonempty (CorrectedC1QuotientTarget X) :=
  ⟨c1PlaceQuotientFiberData (F := X.S.arithmetic.Fmod)⟩

/-- Actual corrected C1 source input, constructed without any
SourceImageRealization parameter. -/
theorem correctedC1ActualSourceInput_actual_independent_of_R
    (X : N8NativeInput l) :
    Nonempty (CorrectedC1ActualSourceInput X) :=
  C1ActualSourceInput.correctedC1ActualSourceInput_nonempty X

/-- Legacy target that still asks for an R at an old place.  This is not a
corrected-target field; it is recorded only to keep the old consumer boundary
explicit. -/
def LegacySourceImageRealizationTarget
    {V : Type uv} (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) :
    Prop :=
  Nonempty (I.SourceImageRealization v)

end LeanFormal.IUT.N8Closure.C1ActualImageRealizationAttempt
