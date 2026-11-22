/-! # S1516 full OrigXiFPaperQPilotObject: exact missing core unification

Status: MISSING (not EXIT=0 construction).

The duplicate core modules are NOT the same declaration set:
* S1479/OrigXiFPaperQPilotObjectPreorderActual compiles only against
  tmp.sheaf.xif.PaperQPilotObject (uppercase core);
* S1480/OrigXiFPaperLineBundleODActual and OrigXiFPaperLineBundleActual use
  tmp.sheaf.xif.paper.PaperQPilotObject (lowercase core).

Directly importing both yields
  environment already contains
  'LeanFormal.IUT.Theorem311Source.PaperQPilotObject.lineBundle'.
Rebasing S1479 onto the lowercase core fails inside the copied S1479 proofs
(application type mismatches at OrigXiFPaperQPilotObjectActual lines 449/451),
so the two cores have diverged structurally, not only by module name.

EXACT MISSING: one canonical PaperQPilotObject core (same field types and
definitions) with S1479's actual Ind3Step preorder construction and S1480's
actual O(-D) carrier rebased onto it.  Only then can the unified object
  actual preorder + OrigXiFPaperLineBundleCarrier I D + four identifications
be built, conditional on D : OrigXiFPaperLineBundleData I.

No completion carrier, no Nonempty/True/arbitrary inhabitant, and no duplicate
core is introduced.
-/

namespace ABCBridge.S1516FullQPilotObjectUnifiedActual

/-- Exact missing object: a single canonical PaperQPilotObject core for both
the actual preorder object and the actual O(-D) carrier. -/
def s1516ExactMissingCoreUnification : String :=
  "unify tmp.sheaf.xif.PaperQPilotObject and tmp.sheaf.xif.paper.PaperQPilotObject"

end ABCBridge.S1516FullQPilotObjectUnifiedActual

