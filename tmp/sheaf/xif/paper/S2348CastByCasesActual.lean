import tmp.sheaf.xif.paper.S2347FinalComposeCastActual
import tmp.sheaf.xif.paper.S2336TransferCompActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2348CastByCasesActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2336TransferCompActual

universe u

theorem S2348_transferAb_subgroupCongr {G : Type u} [Group G]
    {H K : Subgroup G} (h : H = K) [H.FiniteIndex] [K.FiniteIndex] :
    (Abelianization.map (MulEquiv.subgroupCongr h).toMonoidHom).comp
        (Verlagerung.transferAb H) = Verlagerung.transferAb K := by
  cases h
  rw [show MulEquiv.subgroupCongr (rfl : H = H) = MulEquiv.refl H from by
    ext x
    rfl]
  simp

#check S2348_transferAb_subgroupCongr
#print axioms S2348_transferAb_subgroupCongr

end LeanFormal.IUT.XiFPaper.S2348CastByCasesActual

end