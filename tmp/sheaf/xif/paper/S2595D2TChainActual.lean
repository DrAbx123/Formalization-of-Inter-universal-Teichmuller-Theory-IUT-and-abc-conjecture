import tmp.sheaf.xif.paper.S2593D2ChainActual
import tmp.sheaf.xif.paper.S2561Batch2CorrectActual

noncomputable section
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
open LeanFormal.IUT.XiFPaper.S2561Batch2CorrectActual
open LeanFormal.IUT.XiFPaper.S2593D2ChainActual

namespace LeanFormal.IUT.XiFPaper.S2595D2TChainActual

theorem chainT0 : S2550F10 ∣ X ^ 1024 - T0 := by
  have h : T0 = S2560Batch1CorrectActual.R10 := by unfold T0 S2560Batch1CorrectActual.R10; rfl
  rw [h]
  exact chain10

theorem hstepT0 : T0 * S2560Batch1CorrectActual.R7 = S2550F10 * Qtstep0 + Ntstep0 := by
  simpa [Atstep0, Btstep0, T0, S2560Batch1CorrectActual.R7] using tstep0

theorem chainT1 : S2550F10 ∣ X ^ (1024 + 128) - Ntstep0 := by
  exact dvd_mul_step 1024 128 chainT0 chain7 hstepT0

end LeanFormal.IUT.XiFPaper.S2595D2TChainActual

end