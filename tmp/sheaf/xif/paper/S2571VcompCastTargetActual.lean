import tmp.sheaf.xif.paper.S2630CastHelpersActual

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2630CastHelpersActual

namespace LeanFormal.IUT.XiFPaper.S2571VcompCastTargetActual

universe u
variable {F : Type u} [Field F]

theorem vcomp_cast_target
    {A S1 S2 Z : EtaleStackPseudofunctor F} (h : S1 = S2)
    (L : Pseudofunctor.StrongTrans A S1)
    (M : Pseudofunctor.StrongTrans S2 Z) :
    Pseudofunctor.StrongTrans.vcomp (h ▸ L) M =
      Pseudofunctor.StrongTrans.vcomp L (h.symm ▸ M) := by
  cases h
  rfl

#check vcomp_cast_target
#print axioms vcomp_cast_target
end LeanFormal.IUT.XiFPaper.S2571VcompCastTargetActual
end
