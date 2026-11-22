import tmp.sheaf.xif.paper.S2461CycleTypeFinalActual
import tmp.sheaf.xif.paper.S2005PairCycleResidueActual

/-! # S2641: root-to-range transport for cycle type (10,2) -/

noncomputable section
set_option maxHeartbeats 4000000

open LeanFormal.IUT.XiFPaper.S2461CycleTypeFinalActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2005PairCycleResidueActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual

namespace LeanFormal.IUT.XiFPaper.S2641CycleTypeTransportActualAdapted

/-- Root-to-range transport for cycle type (10,2): a Galois automorphism
acting on the twelve roots of psi_5 with cycle type {10,2} produces an
element of the actual mod-5 matrix range with pair cycle type {10,2}. -/
theorem S2641RootToRangeTransport102
    (σ : S1725AbsoluteGalois)
    (h : (S2461RootPerm σ).cycleType = ({10, 2} : Multiset ℕ)) :
    S2203RangeCycleTypeRequired S1982Basis :=
  S2461Target_of_firstMissing ⟨σ, h⟩

/-- Same transport, packaged as the root-to-range Prop. -/
def S2641RootToRangeTransport102Prop : Prop :=
  ∀ σ : S1725AbsoluteGalois,
    (S2461RootPerm σ).cycleType = ({10, 2} : Multiset ℕ) →
      S2203RangeCycleTypeRequired S1982Basis

theorem S2641RootToRangeTransport102_actual :
    S2641RootToRangeTransport102Prop :=
  fun σ h => S2641RootToRangeTransport102 σ h

/-- Pair form: a Galois automorphism acting on the twelve pairs with cycle
type {10,2} also gives the range cycle-type target. -/
theorem S2641PairToRangeTransport102
    (σ : S1725AbsoluteGalois)
    (h : (S2461PairPerm σ).cycleType = ({10, 2} : Multiset ℕ)) :
    S2203RangeCycleTypeRequired S1982Basis :=
  (S2461Target_iff_exists_pairCycle).mpr ⟨σ, h⟩

#check S2641RootToRangeTransport102
#check S2641RootToRangeTransport102_actual
#check S2641PairToRangeTransport102
#print axioms S2641RootToRangeTransport102_actual
#print axioms S2641PairToRangeTransport102

end LeanFormal.IUT.XiFPaper.S2641CycleTypeTransportActualAdapted
end
