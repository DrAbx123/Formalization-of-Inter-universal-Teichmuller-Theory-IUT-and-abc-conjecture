/-
  Target-card diagnostic probe for the ledger-statement-correction run.

  Public compiler metadata only.  Checks and prints the verified public types
  of the imported producer interfaces, and checks the grouping/application
  pattern of the proposed minimally typeable equivariance proposition in the
  abstract form of the actual imported interface.

  The concrete instantiation at
  LeanFormal.IUT.Theorem311Source.OriginalInput.columnProcessionSourceLedger
  cannot be checked here: the type I.ColumnProcessionSourceLedger is declared
  in the owned module SourcePacketDegreeLedger.lean, which does not compile at
  baseline, so no compiled environment contains it and no olean exists.  A
  first version of this probe referenced it directly and the compiler reported
  invalid field ColumnProcessionSourceLedger for the expression I of type
  OriginalInput l V.  This file therefore checks only what the imported
  interfaces can establish.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2OriginalArrows
import LeanFormal.IUT.IUTI.HodgeTheater.LinkVolumeTransport
import Lean

set_option maxHeartbeats 0

namespace LeanFormal.IUT

#check FPrimeStripEquiv.compatAction
#check FPrimeStripEquiv.compatDegree
#check FPrimeStripEquiv.isoPi
#check FPrimeStripEquiv.isoMon
#check FPrimeStrip.action
#check FPrimeStrip.Mon
#check DPrimeStrip.Pi

/-
  Interface-shaped check of the candidate grouping.  This is exactly the
  public statement of compatAction, instantiated at abstract F and F' with an
  element g of the original Pi type and an element x of the original Mon type.
-/
example {V : Type u_1} {F F' : FPrimeStrip V}
    (e : FPrimeStripEquiv F F') (v : V)
    (g : F.Pi v)
    (x : @FPrimeStrip.Mon V F v) :
    e.isoMon v (F.action v g x) =
      F'.action v (e.isoPi v g) (e.isoMon v x) :=
  e.compatAction v g x

end LeanFormal.IUT

namespace LeanFormal.IUT
namespace Theorem311Source

open scoped BigOperators
noncomputable section

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

#check I.fLinkAt_action
#check I.fLinkAt_degree
#check I.columnSource
#check I.columnFStage

end

end Theorem311Source
end LeanFormal.IUT
