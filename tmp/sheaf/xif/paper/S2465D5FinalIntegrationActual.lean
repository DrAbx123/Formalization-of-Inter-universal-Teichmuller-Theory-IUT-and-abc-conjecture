import tmp.sheaf.xif.paper.S2449D5FinalStatusActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2442QE5DegreeOrderSubagentActual
import tmp.sheaf.xif.paper.S2461CycleTypeFinalActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2465D5FinalIntegrationActual

open LeanFormal.IUT.XiFPaper.S2449D5FinalStatusActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2442QE5DegreeOrderSubagentActual
open LeanFormal.IUT.XiFPaper.S2445D5LargeImageChainActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2461CycleTypeFinalActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual

/-- The final D5 exact missing: actual range pair transitivity and actual
range cycle type (10,2) at the selected basis. -/
def S2465D5ExactMissing : Prop :=
  S2449D5ExactFirstMissing

/-- D5 final target, conditional exactly on S2465D5ExactMissing.  This is not
an actual inhabitant of the target. -/
theorem S2465D5LargeImageFive_of_exact
    (h : S2465D5ExactMissing) : S1987D5LargeImageFive :=
  S2449D5LargeImageFive_of_exact h

/-- Pair transitivity follows from the image-tail/large-image input (S2440). -/
theorem S2465PairTransitive_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) :
    S2445RangePairTransitive :=
  S2440RangePairTransitive_of_imageTail h

/-- Pair transitivity follows from the actual large-image target (S2440). -/
theorem S2465PairTransitive_of_largeImage
    (h : S1987D5LargeImageFive) : S2445RangePairTransitive :=
  S2440RangePairTransitive_of_largeImage h

/-- The corrected degree of s2289QE5 under the projective bridge: 240, not
480. -/
theorem S2465CorrectedDegree_eq_240
    (D : S2442Psi5ProjectiveBridge) :
    Module.finrank ℚ s2289QE5 = 240 :=
  S2442Degree_eq_240 D


/-- B2 consumer: the actual range cycle-type target is equivalently the existence
of an absolute Galois element whose matrix has pair cycle type (10,2). -/
theorem S2465CycleType_iff_exists_sigma :
    S2445RangeCycleType ↔ ∃ σ : S1725AbsoluteGalois,
      (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
          ({10, 2} : Multiset ℕ) :=
  S2461Target_iff_exists_sigma

end LeanFormal.IUT.XiFPaper.S2465D5FinalIntegrationActual

end
