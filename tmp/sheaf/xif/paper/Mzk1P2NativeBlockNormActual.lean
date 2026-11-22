import tmp.sheaf.xif.paper.Mzk1P2RankOneChainActual
/-! P2 native block norm comparison -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockNormActual
def nativeBlockNormRows : List String :=
  [ "qVFamBlockLinearEquiv", "conditional linear isometry via QVFamBlockNormPreserving",
    "QVFamBlockNormPreserving missing" ]
theorem nativeBlockNormRows_length : nativeBlockNormRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockNormActual
end
