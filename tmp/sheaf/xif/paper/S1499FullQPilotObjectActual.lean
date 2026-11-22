import tmp.sheaf.xif.paper.OrigXiFPaperLineBundleODActual

/-! # S1499 full OrigXiFPaperQPilotObject: exact first field D

The full object needs actual Ind3Step preorder + actual O(-D) line bundle;
the O(-D) carrier requires
  D : OrigXiFPaperLineBundleData I,
which S1497 is constructing.  This file records the exact first field only.
No Nonempty/True/arbitrary inhabitant and no completion carrier is used.
-/

noncomputable section

namespace ABCBridge.S1499FullQPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle

universe upi umon ui

variable {l : PrimeGeFive}

/-- Exact first field: the actual q-pilot O(-D) divisor datum. -/
def s1499DExact (I : OriginalInput.{0, 0, upi, umon, ui} l
    (FinitePrimePlace 2 7)) : Type _ :=
  OrigXiFPaperLineBundleData I

end ABCBridge.S1499FullQPilotObjectActual

end
