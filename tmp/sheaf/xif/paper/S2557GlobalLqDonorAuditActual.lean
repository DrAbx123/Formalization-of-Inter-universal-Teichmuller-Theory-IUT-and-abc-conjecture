import tmp.sheaf.n8.closure.P6ChainA

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6ChainA

namespace LeanFormal.IUT.XiFPaper.S2557GlobalLqDonorAuditActual

universe u
variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The underconstrained constant donor: accepts the GlobalLqDonor interface
but is not the paper global L_q readout. -/
noncomputable def S2557ConstantGlobalLqDonor : GlobalLqDonor X where
  readout := fun _ => LeanFormal.IUT.N8Closure.C9QPilotRegion.qPilotSignedLog X
  readout_eq_local := rfl

theorem S2557GlobalLqDonor_nonempty : Nonempty (GlobalLqDonor X) :=
  ⟨S2557ConstantGlobalLqDonor X⟩

theorem S2557P6ChainAData_nonempty_iff :
    Nonempty (P6ChainAData X) ↔ Nonempty (GlobalLqDonor X) :=
  ⟨fun ⟨C⟩ => ⟨C.globalLq⟩, fun ⟨D⟩ => ⟨p6ChainAOfGlobalLq X D⟩⟩

theorem S2557P6ChainAData_nonempty : Nonempty (P6ChainAData X) :=
  (S2557P6ChainAData_nonempty_iff X).mpr (S2557GlobalLqDonor_nonempty X)

#check S2557ConstantGlobalLqDonor
#check S2557P6ChainAData_nonempty_iff
#print axioms S2557P6ChainAData_nonempty
end LeanFormal.IUT.XiFPaper.S2557GlobalLqDonorAuditActual
end