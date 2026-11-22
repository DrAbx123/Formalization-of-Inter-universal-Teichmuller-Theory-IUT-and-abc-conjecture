import tmp.sheaf.xif.paper.Mzk1Section0SaturatedActual
import tmp.sheaf.xif.paper.Mzk1Section0SaturatedSymmActual
import tmp.sheaf.xif.paper.Mzk1Section0CountablyOrderedActual
import tmp.sheaf.xif.paper.Mzk1PStarScaleActual
import tmp.sheaf.xif.paper.Mzk1Section0LinearGraphActual

/-!
# Mzk1Section0ConsumerChainActual — consumer theorems over Section-0 assets
(SAT/SATS/COM/PSTAR/LIN, all EXIT0). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0ConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual.OrientedGraph
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedSymmActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0CountablyOrderedActual
open LeanFormal.IUT.XiFPaper.Mzk1PStarScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0LinearGraphActual

variable {G : OrientedGraph.{0}}

/-- Consumer: the all-co-verticial set is saturated. -/
theorem consumer_covertSet_isSaturated (C : PathComposition G) :
    IsSaturatedPathPairSet C (covertSet G) :=
  covertSet_isSaturated C

/-- Consumer: the all-co-verticial set is symmetrically saturated. -/
theorem consumer_covertSet_isSymmSaturated (C : PathComposition G) :
    IsSymmetricallySaturatedPathPairSet C (covertSet G) :=
  covertSet_isSymmetricallySaturated C

/-- Consumer: Z is countably ordered (tree asset). -/
theorem consumer_countablyOrdered_int : CountablyOrdered ℤ :=
  countablyOrdered_int

/-- Consumer: p* has the paper case split. -/
theorem consumer_pStar_paper (p : ℕ) (hp : p.Prime) :
    sourceLogShellStar p = if p = 2 then p ^ 2 else p :=
  pStar_eq_paperPStar hp

/-- Consumer: nonempty integer interval has interval-graph vertices. -/
theorem consumer_intervalGraph_nonempty {a b : ℤ} (h : a ≤ b) :
    Nonempty (intIntervalGraph a b).V :=
  intIntervalGraph_vertices_nonempty h

#check consumer_covertSet_isSaturated
#check consumer_covertSet_isSymmSaturated
#check consumer_countablyOrdered_int
#check consumer_pStar_paper
#check consumer_intervalGraph_nonempty

end LeanFormal.IUT.XiFPaper.Mzk1Section0ConsumerChainActual
end
