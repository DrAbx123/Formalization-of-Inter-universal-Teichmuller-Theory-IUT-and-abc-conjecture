import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel

/-! # S3131 prior-art reuse: concrete IQHullLogVolumeInterface (IQCarrierConcreteModel) -/

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3131IQCarrierModelInterfaceReuseActual

/-- The tree's concrete model interface is the concrete `IQHullLogVolumeInterface Real`
to use for (a)/(b) instantiations (prior art; do not create a new interface). -/
def S3131ConcreteInterface : IQHullLogVolumeInterface Real := iqCarrierModelInterface

def S3131IQCarrierModelAssets : List (String × String) :=
  [ ("IQCarrierConcreteModel.lean:193 iqCarrierModelInterface", "concrete IQHullLogVolumeInterface Real"),
    ("IQCarrierConcreteModel.lean:220/225/230", "iqCarrierModelPointWeight = arithmeticWeight; iqCarrierModelPointHeight = Height.logHeight1; iqCarrierModelLogShellPoint"),
    ("IQCarrierConcreteModel.lean:328 iqCarrierModelLogVolume_region_eq", "region volume = ofReal pointWeight"),
    ("IQCarrierConcreteModel.lean:166 iqCarrierModelLogVolume_union_le", "union subadditivity"),
    ("IQCarrierConcreteModel.lean:531 iqCarrierModel_hmem_hweightvol_incompatible", "membership vs weight-volume warning"),
    ("IQCarrierConcreteModel.lean:193-559", "hunit/hsplit/hptfin/hweightvol/hpoint + epsilonComparison(+Additive) model package") ]

theorem S3131IQCarrierModelAssets_length : S3131IQCarrierModelAssets.length = 6 := rfl

#check iqCarrierModelInterface
#check iqCarrierModelLogVolume_region_eq

end LeanFormal.IUT.XiFPaper.S3131IQCarrierModelInterfaceReuseActual
end