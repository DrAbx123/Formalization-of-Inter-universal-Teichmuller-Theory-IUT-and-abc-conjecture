import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2218RangePairTransitiveActual
import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
import tmp.sheaf.xif.paper.S2375RangePairTransitiveActual
import tmp.sheaf.xif.paper.S2378ActualPairTransitiveActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
import tmp.sheaf.xif.paper.S2203D5RangeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.XiFPaper.S2606C9PairTransitiveTerminalActual

open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- Exact terminal pair-transitivity target. -/
abbrev S2606Target : Prop := S2470Target

/-- The target is actual affine-pair transitivity of the mod-5 range. -/
theorem S2606Target_iff_affine :
    S2606Target ↔
      S2218AffinePairTransitive
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  S2470Target_iff_affine

/-- The target is the finite `PairTransitive` property of the actual mod-5 range. -/
theorem S2606Target_iff_pairTransitive :
    S2606Target ↔
      PairTransitive
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range := by
  rw [S2606Target_iff_affine]
  exact S2218AffinePairTransitive_iff _

/-- The target is exactly actual Galois transitivity on the twelve affine pairs. -/
theorem S2606Target_iff_galois :
    S2606Target ↔ S2229GaloisPairTransitive S1982Basis :=
  S2470Target_iff_galois

/-- The target is S2375's exact first missing. -/
theorem S2606Target_iff_S2375 : S2606Target ↔ S2375ExactFirstMissing :=
  S2470Target_iff_S2375

/-- The target is S2378's exact first missing (the weaker pair transitivity, not range top). -/
theorem S2606Target_iff_S2378 : S2606Target ↔ S2378ExactFirstMissing :=
  S2470Target_iff_S2378

/-- Sufficient input: actual SL_2 containment at the selected basis. -/
theorem S2606Target_of_imageTail (h : S1725ImageTail S1987Five S1982Basis) :
    S2606Target :=
  S2470Target_of_imageTail h

/-- Sufficient input: frozen large-image target. -/
theorem S2606Target_of_largeImage (h : S1987D5LargeImageFive) : S2606Target :=
  S2470Target_of_largeImage h

/-- Sufficient input: whole mod-5 range. -/
theorem S2606Target_of_rangeTop (h : S2378RangeTopRequired) : S2606Target :=
  S2470Target_of_rangeTop h

/-- Target plus cycle type gives the D5 endpoint. -/
theorem S2606D5LargeImageFive_of_target_and_cycle
    (h : S2606Target) (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2470D5LargeImageFive_of_target_and_cycle h hcycle

end LeanFormal.IUT.XiFPaper.S2606C9PairTransitiveTerminalActual

end