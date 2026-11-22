import tmp.sheaf.xif.paper.Mzk1P0LQThetaMemActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LSourceRowsActual
def sourceRows : List (String × String) :=
  [ ("qReadActual", "-|log q| on actualSourcePilotRegionDataL"),
    ("thetaReadActual", "log actual L tensor Haar region"),
    ("qComponentMemGap", "q in each actual C3L local log-shell"),
    ("normalization", "raw Haar to q norm: GAP"),
    ("regionMassPos", "open+nonempty conditional"),
    ("roots/kummer", "not in native core: separate GAP") ]
theorem sourceRows_length : sourceRows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0LSourceRowsActual