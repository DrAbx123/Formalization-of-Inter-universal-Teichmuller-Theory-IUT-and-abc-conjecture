import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2558ProbeNativeDecideAdapted

/-- Probe: one explicit degree-18 modular identity over ZMod 1249. -/
theorem probe_identity :
    ((1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 +
        7 * X ^ 6 + 8 * X ^ 7 + 9 * X ^ 8 + 10 * X ^ 9 : (ZMod 1249)[X]) ^ 2) =
      S2550F10 * (284 + 428 * X + 405 * X ^ 2 + 423 * X ^ 3 + 206 * X ^ 4 +
        750 * X ^ 5 + 556 * X ^ 6 + 634 * X ^ 7 + 100 * X ^ 8) +
      (149 + 633 * X + 583 * X ^ 2 + 957 * X ^ 3 + 461 * X ^ 4 + 9 * X ^ 5 +
        1098 * X ^ 6 + 605 * X ^ 7 + 247 * X ^ 8 + 965 * X ^ 9) := by
  native_decide

end LeanFormal.IUT.XiFPaper.S2558ProbeNativeDecideAdapted

end
