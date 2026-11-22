import tmp.sheaf.xif.paper.S2587LocalizedResidueDataActual
import tmp.sheaf.xif.paper.S2588FbarIrreducibleActual
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2589TargetAssemblyActual

open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
open LeanFormal.IUT.XiFPaper.S2588FbarIrreducibleActual

/-- With the S2584 witness and the actual fbar irreducibility, only the
localized Dedekind-to-twelve-cycle transport remains. -/
theorem S2589Target_of_transport
    (W : S2584PrimeDegreeOneWitness)
    (htrans : S2587LocalizedDedekindToTwelveCycleS) :
    LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target :=
  S2587Target_of_witness_irreducible W
    (S2587FbarIrreducibleRequired_holds W) htrans

/-- Exact remaining localized Dedekind--Frobenius statement. -/
def S2589LocalizedDedekindRequired : Prop := S2587LocalizedDedekindToTwelveCycleS

theorem S2589Target_of_required
    (W : S2584PrimeDegreeOneWitness) (h : S2589LocalizedDedekindRequired) :
    LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target :=
  S2589Target_of_transport W h

end LeanFormal.IUT.XiFPaper.S2589TargetAssemblyActual
end