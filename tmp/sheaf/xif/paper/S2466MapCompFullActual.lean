import tmp.sheaf.xif.paper.S2465MapCompLemmasActual

noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2465MapCompLemmasActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2466MapCompFullActual
local notation "Xf" => S2482Orbicurve.stack.fiber

noncomputable def S2466MapComp (f g : Iut.SignGroup) :
    S2465Map (g * f) ≅ S2465Map f ≫ S2465Map g := by
  by_cases hf : f = 1
  · by_cases hg : g = 1
    · subst f; subst g
      exact S2465_comp_id_id 1 1 rfl rfl
    · exact S2465_comp_id_nonid f g hf hg
  · by_cases hg : g = 1
    · exact S2465_comp_nonid_id f g hf hg
    · exact S2465_comp_nonid_nonid f g hf hg

#print axioms S2466MapComp

end LeanFormal.IUT.XiFPaper.S2466MapCompFullActual
end
