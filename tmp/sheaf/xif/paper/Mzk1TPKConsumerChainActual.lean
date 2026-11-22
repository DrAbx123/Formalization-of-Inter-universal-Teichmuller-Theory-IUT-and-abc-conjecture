import tmp.sheaf.xif.paper.Mzk1ThetaPowerKernelActual

/-!
# Mzk1TPKConsumerChainActual — consumer theorems for the etale theta power-kernel interface
(Mzk1ThetaPowerKernelActual + tree EtaleThetaQuotient, EXIT0). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TPKConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPowerKernelActual

/-- Consumer: theta power kernel is normal. -/
theorem consumer_thetaPowerKernel_normal (G : Type) [Group G] (l : ℕ) :
    (thetaPowerKernel G l).Normal :=
  thetaPowerKernel_normal G l

/-- Consumer: elliptic power kernel is normal. -/
theorem consumer_ellipticPowerKernel_normal (G : Type) [Group G] (l : ℕ) :
    (ellipticPowerKernel G l).Normal :=
  ellipticPowerKernel_normal G l

/-- Consumer: theta power kernel maps into the elliptic power kernel. -/
theorem consumer_thetaPowerKernel_le (G : Type) [Group G] (l : ℕ) :
    thetaPowerKernel G l ≤ Subgroup.comap (thetaToElliptic G) (ellipticPowerKernel G l) :=
  thetaToElliptic_maps_powerKernel G l

/-- Consumer: mod-l theta-to-elliptic map is surjective. -/
theorem consumer_modL_surjective (G : Type) [Group G] (l : ℕ) :
    Function.Surjective (modLThetaToElliptic G l) :=
  modLThetaToElliptic_surjective G l

/-- Consumer: theta commutator kernel lies in the derived subgroup. -/
theorem consumer_commutator_le_derived (G : Type) [Group G] :
    thetaCommutatorKernel G ≤ thetaDerivedSubgroup G :=
  thetaCommutatorKernel_le_derivedSubgroup G

#check consumer_thetaPowerKernel_normal
#check consumer_ellipticPowerKernel_normal
#check consumer_thetaPowerKernel_le
#check consumer_modL_surjective
#check consumer_commutator_le_derived

end LeanFormal.IUT.XiFPaper.Mzk1TPKConsumerChainActual
end
