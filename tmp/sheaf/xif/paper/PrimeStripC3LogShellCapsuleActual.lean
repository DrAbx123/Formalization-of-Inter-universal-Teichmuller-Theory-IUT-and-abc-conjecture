import tmp.sheaf.xif.paper.PrimeStripLogShellActual

/-! # Actual prime-strip capsule with C3-indexed log-shells

This is the actual Q7 object: the source D-prime/F-prime-strip capsule at the
source theater index V, together with the actual local log-shells I(D_v)
indexed by the actual C3 tensor places (C3.tensorIndex, C3.tensorPlaces,
C3.tensorTuple), constructed from the actual completed local fields.

The capsule and the C3 log-shell family are both actual objects; no
identification V = C3.tensorIndex is asserted, and no arbitrary equivalence or
identity-projection prime-strip is used.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PrimeStripC3LogShellCapsuleActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual D-prime/F-prime-strip capsule together with the actual C3-indexed
local log-shell data. -/
structure ActualPrimeStripC3LogShellObject where
  fStrip : FPrimeStrip.{umon, uv, upi} V
  dStrip : DPrimeStrip.{upi, uv} V
  dStrip_eq : dStrip = fStrip.toDPrimeStrip
  c3LogShellDatum : (i : C3.tensorIndex) -> SourceLogShellDatum
  c3LogShell : (i : C3.tensorIndex) ->
    Set (CommonPrimeCompletion (c3LogShellPlace C3 i))
  c3LogShell_eq_datum : forall i,
    c3LogShell i = (c3LogShellDatum i).logShell
  c3LogShell_eq_integral : forall i,
    c3LogShell i =
      (integralLogShell
        (K := CommonPrimeCompletion (c3LogShellPlace C3 i))
        (p := C3.p) :
        Set (CommonPrimeCompletion (c3LogShellPlace C3 i)))

/-- The actual source prime-strip capsule with C3-indexed log-shells. -/
noncomputable def actualPrimeStripC3LogShellObject :
    ActualPrimeStripC3LogShellObject (V := V) (I := I) C3 where
  fStrip := (actualDFPrimeStripCapsule (V := V) (I := I)).fStrip
  dStrip := (actualDFPrimeStripCapsule (V := V) (I := I)).dStrip
  dStrip_eq := (actualDFPrimeStripCapsule (V := V) (I := I)).dStrip_eq
  c3LogShellDatum := fun i => actualC3LogShellDatum (I := I) C3 i
  c3LogShell := fun i => actualC3LogShell (I := I) C3 i
  c3LogShell_eq_datum := fun i => rfl
  c3LogShell_eq_integral := fun i =>
    actualC3LogShell_eq_integralLogShell (I := I) C3 i

/-- Actual projection: the F-strip of the object. -/
def actualPrimeStripC3LogShell_fStrip :
    FPrimeStrip.{umon, uv, upi} V :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).fStrip

/-- Actual projection: the D-strip of the object. -/
def actualPrimeStripC3LogShell_dStrip :
    DPrimeStrip.{upi, uv} V :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).dStrip

/-- Actual projection: the C3-indexed log-shell datum. -/
def actualPrimeStripC3LogShell_datum (i : C3.tensorIndex) :
    SourceLogShellDatum :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).c3LogShellDatum i

/-- Actual projection: the C3-indexed log-shell. -/
def actualPrimeStripC3LogShell_shell (i : C3.tensorIndex) :
    Set (CommonPrimeCompletion (c3LogShellPlace C3 i)) :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).c3LogShell i

/-- The actual C3 log-shell projection is the actual local log-shell. -/
theorem actualPrimeStripC3LogShell_shell_eq (i : C3.tensorIndex) :
    actualPrimeStripC3LogShell_shell (V := V) (I := I) C3 i =
      actualC3LogShell (I := I) C3 i := rfl

/-- The actual D-strip projection is the forgetful image of the F-strip. -/
theorem actualPrimeStripC3LogShell_dStrip_eq_toD :
    actualPrimeStripC3LogShell_dStrip (V := V) (I := I) C3 =
      (actualPrimeStripC3LogShell_fStrip (V := V) (I := I) C3).toDPrimeStrip :=
  (actualPrimeStripC3LogShellObject (V := V) (I := I) C3).dStrip_eq

end LeanFormal.IUT.XiFPaper.PrimeStripC3LogShellCapsuleActual

end
