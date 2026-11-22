import tmp.sheaf.xif.paper.Mzk1RRPunctureDegreeActual
import tmp.sheaf.xif.paper.Mzk1RRInterfaceBundleActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # flt_core RR cluster rollup; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRClusterRollupActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

universe u v

theorem rrClusterRollup_bundle {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (T : Finset (Place K F)) (v : Place K F) :
    Divisor.degree (Curve.punctureDivisor T) = (T.card : ℤ) ∧ v.deg = 1 :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1RRPunctureDegreeActual.rr_puncture_degree T,
    LeanFormal.IUT.XiFPaper.Mzk1RRPunctureDegreeActual.rr_place_degree_one v⟩

def rrClusterRollupRows : List (String × String × String) :=
  [ ("puncture + place degree", "PROVED", "rrClusterRollup_bundle") ]

theorem rrClusterRollupRows_length : rrClusterRollupRows.length = 1 := rfl

#check rrClusterRollup_bundle
#check rrClusterRollupRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRClusterRollupActual
end