import tmp.sheaf.xif.paper.S2532PairTransitiveActual
import tmp.sheaf.xif.paper.S2002D5RangeFieldGapsActual
import tmp.sheaf.xif.paper.S2203D5RangeActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S2005PairCycleResidueActual

open LeanFormal.IUT.XiFPaper.S2532PairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2002D5RangeFieldGapsActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-- The actual root-to-range transport packaged from S2532. -/
theorem S2005RootToRangeTransport : S2470RootToRangeTransport :=
  S2532RootToRangeTransport

/-- The exact arithmetic gap for pair transitivity: the concrete residue
certificate (integral model + prime + irreducible degree-12 reduction). -/
def S2005ResidueCertificateRequired : Prop :=
  S2532ResidueCertificateRequired

theorem S2005ResidueCertificateRequired_iff :
    S2005ResidueCertificateRequired ↔
      Nonempty S2470ActualResidueData := Iff.rfl

/-- Residue certificate gives actual range pair transitivity (transport
already actual). -/
theorem S2005PairTransitive_of_residueCertificate
    (h : S2005ResidueCertificateRequired) :
    S2203RangePairTransitiveRequired S1982Basis :=
  S2532Target_of_residueCertificate h

/-- The exact gap for cycle type (10,2) remains the range cycle-type
hypothesis; the root cycle type {2,10} is actual but has no root-to-range
2,10 transport in the tree. -/
def S2005CycleTypeRequired : Prop :=
  S2203RangeCycleTypeRequired S1982Basis

/-- Two explicit arithmetic/index inputs give the D5 large-image target. -/
theorem S2005D5LargeImageFive_of_residue_and_cycle
    (hres : S2005ResidueCertificateRequired)
    (hcycle : S2005CycleTypeRequired) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle
    (S2005PairTransitive_of_residueCertificate hres)

/-- Determinant gap: no actual Weil-pairing/cyclotomic-character interface
is available. -/
def S2005DetSurjectiveRequired : Prop :=
  DetSurjectiveOn
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range

#check S2005RootToRangeTransport
#check S2005PairTransitive_of_residueCertificate
#check S2005D5LargeImageFive_of_residue_and_cycle
#print axioms S2005RootToRangeTransport
#print axioms S2005PairTransitive_of_residueCertificate
#print axioms S2005D5LargeImageFive_of_residue_and_cycle
end LeanFormal.IUT.XiFPaper.S2005PairCycleResidueActual
end