import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient

/-!
# Mzk1ThetaPowerKernelActual — power-kernel / projection interface for the etale theta
quotient (iuti-ii theta interface)

STEP 0 prior-art: IUTII/Theta/EtaleThetaQuotient (theta quotient, theta/elliptic power
kernels and their normality, theta-to-elliptic and mod-l maps with surjectivity) -> REUSE;
this file re-exports those facts as a named interface layer for the theta group rows.

No axiom/sorry; registry frozen 14041.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaPowerKernelActual

open LeanFormal.IUT

/-- Normality of the theta power kernel. -/
def thetaPowerKernel_normalT :=
  @thetaPowerKernel_normal

/-- Normality of the elliptic power kernel. -/
def ellipticPowerKernel_normalT :=
  @ellipticPowerKernel_normal

/-- The theta power kernel maps into the elliptic power kernel under thetaToElliptic. -/
def thetaToElliptic_maps_powerKernelT :=
  @thetaToElliptic_maps_powerKernel

/-- The mod-l theta-to-elliptic map. -/
def modLThetaToEllipticT :=
  @modLThetaToElliptic

/-- Surjectivity of the mod-l theta-to-elliptic map. -/
def modLThetaToElliptic_surjectiveT :=
  @modLThetaToElliptic_surjective

/-- Surjectivity of the theta-to-elliptic map. -/
def thetaToElliptic_surjectiveT :=
  @thetaToElliptic_surjective

/-- The commutator kernel sits in the derived subgroup. -/
def thetaCommutatorKernel_le_derivedT :=
  @thetaCommutatorKernel_le_derivedSubgroup

/-- Power-kernel interface rows: (item, tree declaration, status). -/
def thetaPowerKernelRows : List (String × String × String) :=
  [ ("theta power kernel normal", "thetaPowerKernel_normal", "TREE PROOF (re-exported)"),
    ("elliptic power kernel normal", "ellipticPowerKernel_normal", "TREE PROOF (re-exported)"),
    ("theta power kernel maps to elliptic power kernel", "thetaToElliptic_maps_powerKernel", "TREE PROOF (re-exported)"),
    ("mod-l theta-to-elliptic map", "modLThetaToElliptic", "TREE DEFINITION (re-exported)"),
    ("mod-l theta-to-elliptic surjective", "modLThetaToElliptic_surjective", "TREE PROOF (re-exported)"),
    ("theta-to-elliptic surjective", "thetaToElliptic_surjective", "TREE PROOF (re-exported)"),
    ("theta commutator kernel <= derived subgroup", "thetaCommutatorKernel_le_derivedSubgroup", "TREE PROOF (re-exported)"),
    ("geometric realization of the theta groups", "not asserted", "NAMED (EtTh class-B row)") ]

/-- The power-kernel row record has eight rows. -/
theorem thetaPowerKernelRows_length : thetaPowerKernelRows.length = 8 := rfl

#check thetaPowerKernel_normalT
#check ellipticPowerKernel_normalT
#check thetaToElliptic_maps_powerKernelT
#check modLThetaToEllipticT
#check modLThetaToElliptic_surjectiveT
#check thetaToElliptic_surjectiveT
#check thetaCommutatorKernel_le_derivedT
#check thetaPowerKernelRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ThetaPowerKernelActual
end
