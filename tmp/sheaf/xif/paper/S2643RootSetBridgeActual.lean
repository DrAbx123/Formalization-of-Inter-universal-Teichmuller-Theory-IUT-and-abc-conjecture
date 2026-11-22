import tmp.sheaf.xif.paper.S2642RootToRangeTransport
import tmp.sheaf.xif.paper.S2494bRootCycleTypeMod29Actual

/-! # S2643: root-set bridge scaffolding -/

noncomputable section
set_option maxHeartbeats 4000000

open Polynomial
open LeanFormal.IUT.XiFPaper.S2642RootToRangeTransport
open LeanFormal.IUT.XiFPaper.S2494bRootCycleTypeMod29Actual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace LeanFormal.IUT.XiFPaper.S2643RootSetBridgeActual

/-- The chosen F'-algebra embedding of the 5-division splitting field into
the algebraic closure of F'. -/
noncomputable def S2643Embedding :
    S2057FiveDivisionField →ₐ[S1720Field] S1906K :=
  IsAlgClosed.lift

#check S2643Embedding
#print axioms S2643Embedding

end LeanFormal.IUT.XiFPaper.S2643RootSetBridgeActual
end
