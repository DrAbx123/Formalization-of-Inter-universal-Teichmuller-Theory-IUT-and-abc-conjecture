import Mathlib
import tmp.sheaf.xif.paper.S3131IUTIVTheoremAInputActual
import tmp.sheaf.xif.paper.S3131IUTIVCor22Cor23InputActual

/-! # S3131 IUT IV logical chain to ABC (statement schema; no proof claims) -/

noncomputable section
open LeanFormal.IUT.XiFPaper.S3131IUTIVTheoremAInputActual
open LeanFormal.IUT.XiFPaper.S3131IUTIVCor22Cor23InputActual

namespace LeanFormal.IUT.XiFPaper.S3131IUTIVChainToABCActual

/-- The IUT IV logical chain shape: Cor 2.2 (suitable initial Theta-data) +
Theorem 1.10 (log-volume estimates) => Theorem A/Cor 2.3 (Diophantine inequalities)
=> ABC as a special case.  GenEll supplies the compactly-bounded-to-general reduction. -/
def IUTIVChainStatement
    (cor22 thm110 genEll theoremA abc : Prop) : Prop :=
  cor22 → thm110 → genEll → ((theoremA → abc) → abc)

/-- Shape-level reading of the chain: if the chain and its components hold, ABC follows. -/
theorem abc_of_chain_shape {cor22 thm110 genEll theoremA abc : Prop}
    (hchain : IUTIVChainStatement cor22 thm110 genEll theoremA abc)
    (h22 : cor22) (h110 : thm110) (hge : genEll) (hta : theoremA → abc) : abc :=
  hchain h22 h110 hge hta

#check IUTIVChainStatement
#check abc_of_chain_shape

end LeanFormal.IUT.XiFPaper.S3131IUTIVChainToABCActual
end