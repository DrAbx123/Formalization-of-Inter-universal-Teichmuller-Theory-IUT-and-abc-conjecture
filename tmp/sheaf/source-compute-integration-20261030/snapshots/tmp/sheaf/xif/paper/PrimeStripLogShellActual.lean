import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import tmp.sheaf.n8.closure.SourcePilotRegion

/-! # Actual D-prime / F-prime-strip capsule and local log-shells

IUT III, Proposition 3.2, (i), (ii) (pp. 97-99) attaches to a capsule of
D-prime-strips the local log-shells I(D_v) and their direct sums/tensor
packets.  This file constructs, from the actual source data:

* the actual F-prime-strip at the source theater (OriginalInput.primeStripAt),
  its D-prime-strip, and the proof that the D-strip is the forgetful image;
* the actual local log-shell datum at each C3 tensor place
  (sourceLocalLogShellDatum), whose log-shell is the actual integralLogShell.

It does NOT assert the paper-level identification between the source
prime-strip index V and the C3 tensor index/places.  The exact missing object
is the arithmetic place/index comparison recorded below.

No arbitrary carrier, sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual F-prime-strip of the source theater at (1,0). -/
abbrev ActualFPrimeStrip : FPrimeStrip.{umon, uv, upi} V :=
  I.primeStripAt 1 0

/-- The actual D-prime-strip obtained by forgetting the value monoid. -/
abbrev ActualDPrimeStrip : DPrimeStrip.{upi, uv} V :=
  I.dPrimeStripAt 1 0

/-- The actual D-prime / F-prime-strip capsule: the D-strip is exactly the
forgetful image of the F-strip. -/
structure ActualDFPrimeStripCapsule where
  fStrip : FPrimeStrip.{umon, uv, upi} V
  dStrip : DPrimeStrip.{upi, uv} V
  dStrip_eq : dStrip = fStrip.toDPrimeStrip

/-- The actual capsule from the source theater. -/
noncomputable def actualDFPrimeStripCapsule : ActualDFPrimeStripCapsule (V := V) where
  fStrip := ActualFPrimeStrip (I := I)
  dStrip := ActualDPrimeStrip (I := I)
  dStrip_eq := rfl

/-- The actual selected C3 tensor place at a tensor index. -/
def c3LogShellPlace (i : C3.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  C3.tensorPlaces i (C3.tensorTuple i)

/-- The actual local log-shell datum at the selected C3 tensor place. -/
noncomputable def actualC3LogShellDatum (i : C3.tensorIndex) :
    SourceLogShellDatum :=
  letI : Fact C3.p.Prime := C3.hp
  sourceLocalLogShellDatum (p := C3.p) (c3LogShellPlace C3 i)

/-- The actual local log-shell I(D_v) at the selected C3 tensor place. -/
noncomputable def actualC3LogShell (i : C3.tensorIndex) :
    Set (CommonPrimeCompletion (c3LogShellPlace C3 i)) :=
  (actualC3LogShellDatum C3 i).logShell

/-- The actual log-shell is exactly the integral log-shell of the completed
local field. -/
theorem actualC3LogShell_eq_integralLogShell (i : C3.tensorIndex) :
    actualC3LogShell C3 i =
      ((integralLogShell (p := C3.p) :
        AddSubgroup (CommonPrimeCompletion (c3LogShellPlace C3 i))) :
        Set (CommonPrimeCompletion (c3LogShellPlace C3 i))) := by
  unfold actualC3LogShell actualC3LogShellDatum
  exact sourceLocalLogShellDatum_logShell_eq_integralLogShell
    (p := C3.p) (c3LogShellPlace C3 i)

/-- Exact missing source comparison: the source prime-strip index V is the C3
tensor index, and the arithmetic prime-strip places agree with the selected C3
tensor places.  This is the paper-level place/index identification; it is not
constructed by the prime-strip core or by C3 data alone. -/
structure PrimeStripC3PlaceComparison where
  indexEquiv : V ≃ C3.tensorIndex
  stripPlace : V -> FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p
  stripPlace_eq : forall v,
    stripPlace v = C3.tensorPlaces (indexEquiv v) (C3.tensorTuple (indexEquiv v))

/-- The exact missing comparison as a proposition. -/
def PrimeStripC3PlaceComparisonRequired : Prop :=
  Nonempty (PrimeStripC3PlaceComparison (V := V) (I := I) C3)

/-- Conditional construction of the local log-shell datum on the source
prime-strip index from the exact missing place comparison. -/
noncomputable def logShellDatumOnStrip
    (P : PrimeStripC3PlaceComparison (V := V) (I := I) C3) (v : V) :
    SourceLogShellDatum :=
  letI : Fact C3.p.Prime := C3.hp
  sourceLocalLogShellDatum (p := C3.p) (P.stripPlace v)

/-- Conditional log-shell on the source prime-strip index. -/
noncomputable def logShellOnStrip
    (P : PrimeStripC3PlaceComparison (V := V) (I := I) C3) (v : V) :
    Set (CommonPrimeCompletion (P.stripPlace v)) :=
  (logShellDatumOnStrip (V := V) (I := I) C3 P v).logShell

end LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual

end
