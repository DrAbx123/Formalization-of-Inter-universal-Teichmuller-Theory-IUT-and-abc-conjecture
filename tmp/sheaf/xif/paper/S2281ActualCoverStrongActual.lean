import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S2086ToAAssemblyActual

/-! # S2281: the actual S2086/S2087 target cover is not necessarily strong

S2086/S2087 quantify over all `S1728Cover`.  S1850's `S1850DoubledCover` is
such a cover, but S1852 shows that it is neither coherent nor strong.  Hence
the strong-cover route cannot be used without adding a strong finite-etale
structure as an input; the unrestricted target cannot be closed this way.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2281ActualCoverStrongActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual

universe u

/-- Not every actual S1728Cover carries a strong finite-etale structure. -/
theorem S2281NotAllCoversStrong :
    ¬ (∀ A : S1728Cover,
        ∃ M : StrongEtaleStackFiniteEtaleMorphism A.map, M.toWeak = A.finiteEtale) := by
  intro h
  obtain ⟨M, hM⟩ := h S1850DoubledCover
  exact S1852Doubled_not_strong ⟨M, hM⟩

/-- The doubled cover is not coherent. -/
theorem S2281NotAllCoversCoherent :
    ¬ ∃ C : CoherentCover, C.cover = S1850DoubledCover :=
  fun ⟨C, hC⟩ => S1852DoubledCover_not_coherent C hC

#print axioms S2281NotAllCoversStrong
#print axioms S2281NotAllCoversCoherent
#check S2281NotAllCoversStrong
#check S2281NotAllCoversCoherent

end LeanFormal.IUT.XiFPaper.S2281ActualCoverStrongActual

end
