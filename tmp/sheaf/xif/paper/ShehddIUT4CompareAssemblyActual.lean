import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual
import tmp.sheaf.xif.paper.S3131EndgameDependencyLedgerActual

/-!
# ShehddIUT4CompareAssemblyActual — IUT IV comparison assembly (rung iut4_compare)

Real assembly for LADDER rung iut4_compare: the undilated height and region-volume
dictionary bounds give BOTH comparison families (b) and (c) in one consumer theorem; the
endgame conditional theorem shape is consumed by the second theorem.  The undilated bounds
themselves are explicit class-B named inputs (IUT IV Thm 1.10 / Cor 2.2 paper content).
No sorry/axiom, no placeholder.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddIUT4CompareAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
open LeanFormal.IUT.XiFPaper.S3131EndgameDependencyLedgerActual

universe u

/-- **PROVED assembly:** the undilated height bound and the undilated region-volume bound
yield both comparison families (b) and (c) simultaneously. -/
theorem height_and_region_families_of_undilated {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (heightBound : UndilatedHeightBound W pt)
    (regionBound : UndilatedRegionBound W pt) :
    HeightComparisonFamily W pt ∧ RegionVolumeFamily W pt :=
  ⟨heightComparisonFamily_of_undilated heightBound,
    regionVolumeFamily_of_undilated regionBound⟩

/-- **PROVED consumer:** the endgame conditional theorem shape consumed at instantiated
class-A / class-B / model-construction data. -/
theorem endgame_conditional_consumer {classA classB modelConstruction abc : Prop}
    (endgame : S3131EndgameConditionalTheorem classA classB modelConstruction abc)
    (classA_holds : classA) (classB_holds : classB)
    (modelConstruction_holds : modelConstruction) : abc :=
  endgame_conditional classA classB modelConstruction abc endgame
    classA_holds classB_holds modelConstruction_holds

end LeanFormal.IUT.XiFPaper.ShehddIUT4CompareAssemblyActual
end
