import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2OriginalArrows

set_option pp.universes true
set_option pp.explicit false
set_option pp.fullNames true

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

#check @FPrimeStrip
#check @FPrimeStripEquiv
#check @FStageCapsule
#check @FStageCapsule.mk
-- Public structure fields and projection types; no implementation bodies.
#print FStageCapsule
#check @FStageCapsule.source
#check @FStageCapsule.strip
#check @FStageCapsule.link
#check @H2SpokePermutation
#check @H2FStagePolyIso
#check @H2FStagePolyIso.mk
#check @H2FStagePolyIso.map
#check @H2FStagePolyIso.component
#check @H2FStagePolyIso.naturality
#check @spokeCapsule
#check @stageSpokePolyIso
#check @h2HorizontalFPolyIso
#check @columnFStage
#check @indexOf
#check @fPrimeStripAt

namespace LeanFormal.IUT.Theorem311Source.OriginalInput.LedgerArrowInterfaceUnblock

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}

theorem fPrimeStripAt_eq_indexed_theater_primeStrip
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    I.fPrimeStripAt n m = (I.family.theater (I.indexOf n m)).primeStrip := by
  rfl

theorem columnFStage_strip_eq_fPrimeStripAt
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Int) (k : Nat) (i : Fin (k + 1)) :
    (I.columnFStage n k).strip i = I.fPrimeStripAt n (i.1 : Int) := by
  rfl

#check @fPrimeStripAt_eq_indexed_theater_primeStrip
#check @columnFStage_strip_eq_fPrimeStripAt
#print axioms fPrimeStripAt_eq_indexed_theater_primeStrip
#print axioms columnFStage_strip_eq_fPrimeStripAt

end LeanFormal.IUT.Theorem311Source.OriginalInput.LedgerArrowInterfaceUnblock

#print axioms fPrimeStripAt
#print axioms columnFStage
#print axioms spokeCapsule
#print axioms stageSpokePolyIso
#print axioms h2HorizontalFPolyIso
