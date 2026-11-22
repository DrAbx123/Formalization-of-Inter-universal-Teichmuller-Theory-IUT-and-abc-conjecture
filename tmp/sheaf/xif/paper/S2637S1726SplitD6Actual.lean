import tmp.sheaf.xif.paper.S2636CoherentScopedD6Actual
import tmp.sheaf.xif.paper.S2632S1726SplitCoverStrongActual

/-! # S2637: D6(c) consumer instantiated at the paper S1726 split cover -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2632S1726SplitCoverStrongActual
open LeanFormal.IUT.XiFPaper.S2635CoherentScopedConsumers
open LeanFormal.IUT.XiFPaper.S2636CoherentScopedD6Actual

namespace LeanFormal.IUT.XiFPaper.S2637S1726SplitD6Actual

/-- The coherent cover underlying the paper split cover. -/
noncomputable def S1726SplitCoherent : CoherentCover :=
  Classical.choose S1726SplitCoherentExists

theorem S1726SplitCoherent_cover :
    S1726SplitCoherent.cover = S1726SplitCover :=
  Classical.choose_spec S1726SplitCoherentExists

/-- Identity cover map of the chosen coherent cover. -/
noncomputable def S1726SplitIdCoverMap :
    S1728CoverMap S1726SplitCoherent.cover S1726SplitCoherent.cover where
  map := Pseudofunctor.StrongTrans.id _
  commutes := Pseudofunctor.StrongTrans.leftUnitor _

/-- Scoped finite-etale cospan field for the paper cover. -/
noncomputable def S1726SplitScopedHg
    (F : CoherentScopedField) :
    S2086CospanGMapFiniteEtaleOnCoherent :=
  cospanGMapFiniteEtaleOnCoherent
    (morphismOfFiniteEtaleStacksOnCoherent F)

/-- D6(c) for the paper split cover, conditional on the scoped geometric
base-change pullback input. -/
noncomputable def S1726SplitD6c
    (F : CoherentScopedField)
    (h : S2086BaseChangePullbackOnCoherent (S1726SplitScopedHg F)) :
    S2043FirstMissingFiniteEtale
      (f := S1726SplitIdCoverMap) (g := S1726SplitIdCoverMap) :=
  D6FiniteEtaleOnCoherent (S1726SplitScopedHg F) h
    S1726SplitCoherent S1726SplitCoherent S1726SplitCoherent
    S1726SplitIdCoverMap S1726SplitIdCoverMap

#check S1726SplitCoherent
#check S1726SplitIdCoverMap
#check S1726SplitD6c
#print axioms S1726SplitD6c

end LeanFormal.IUT.XiFPaper.S2637S1726SplitD6Actual
end
