import tmp.sheaf.xif.paper.Mzk1P58iiCor55RowsActual
import tmp.sheaf.xif.paper.Mzk1Section0SaturatedActual
import tmp.sheaf.xif.paper.Mzk1Section0SaturatedClosureActual

/-!
# Mzk1Cor55ConsumerChainActual — consumer theorems for Cor 5.5 auxiliary model and
Section-0 saturated-set closure (C55D/SAT/SATC, EXIT0). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor55ConsumerChainActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual.OrientedGraph
open LeanFormal.IUT.XiFPaper.Mzk1P58iiCor55RowsActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedClosureActual

variable {G : OrientedGraph.{0}}

/-- Consumer: the Cor-5.5 auxiliary L/L-dagger model is inhabited. -/
theorem consumer_cor55_model : Nonempty Cor55DaggerModel :=
  cor55DaggerModel_nonempty

/-- Consumer: the Cor-5.5 auxiliary row record has six rows. -/
theorem consumer_cor55_rows : cor55AuxRows.length = 6 :=
  cor55AuxRows_length

/-- Consumer: the empty saturated path-pair set is saturated. -/
theorem consumer_saturated_empty (C : PathComposition G) :
    IsSaturatedPathPairSet C (∅ : Set (PathPairSigma G)) :=
  saturated_empty C

/-- Consumer: a saturated set is contained in the all-co-verticial set. -/
theorem consumer_saturated_subset_covert (C : PathComposition G) (P : Set (PathPairSigma G))
    (h : IsSaturatedPathPairSet C P) : P ⊆ covertSet G :=
  saturated_subset_covertSet C P h

/-- Consumer: intersections of saturated sets are saturated. -/
theorem consumer_saturated_inter (C : PathComposition G) (P Q : Set (PathPairSigma G))
    (hP : IsSaturatedPathPairSet C P) (hQ : IsSaturatedPathPairSet C Q) :
    IsSaturatedPathPairSet C (P ∩ Q) :=
  saturated_inter C P Q hP hQ

#check consumer_cor55_model
#check consumer_cor55_rows
#check consumer_saturated_empty
#check consumer_saturated_subset_covert
#check consumer_saturated_inter

end LeanFormal.IUT.XiFPaper.Mzk1Cor55ConsumerChainActual
end
