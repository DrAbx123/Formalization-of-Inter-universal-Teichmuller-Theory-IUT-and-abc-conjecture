import LeanFormal.IUT.ABCBridge.Bridge.CertificateHullWiring

/-! # S3131 certificate theta-slot reuse (prior art) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131CertificateThetaSlotReuseActual

def S3131CertificateThetaSlotReuse : List (String × String) :=
  [ ("CertificateHullWiring:173 hull_le_theta", "theta upper-bound slot (hull) -> REUSE with CardAMPL supply"),
    ("CertificateHullWiring:199 target_le_theta", "target upper-bound slot -> REUSE"),
    ("CertificateHullWiring:301 unsat", "satisfiability refutation -> honesty reference, do not assume slot always inhabitable"),
    ("CardAMPLThetaBoundSupply:78/94/116", "supplies hull_logVolume_le / realVolume_le / of_realVolume_le -> reuse for certificate slot") ]

theorem S3131CertificateThetaSlotReuse_length : S3131CertificateThetaSlotReuse.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.S3131CertificateThetaSlotReuseActual
end