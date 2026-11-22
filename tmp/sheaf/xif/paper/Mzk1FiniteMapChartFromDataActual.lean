import tmp.sheaf.xif.paper.Mzk1GeomCoreFiniteMapChartInterfaceActual

/-! # Mzk1FiniteMapChartFromDataActual — real equivalence: ported FiniteMapData <-> chart interface

Real Lean (no sorry/axiom, no adapted copy): the typed 16-field chart interface is
definitionally equivalent to the ported finite-map datum — the forward direction is the
PROVED toFiniteMapData constructor; here we build the reverse and prove the round-trips by
rfl.  This closes the interface-level form of foundation:D.gap.finiteMap (the actual
construction from a function-field zero divisor remains the named gap, unchanged).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMapChartFromDataActual

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- Reverse direction: a ported finite-map datum yields the typed chart interface. -/
def finiteMapChartDataOfFiniteMapData (X : Mzk1FiniteMapData c ε) :
    FiniteMapChartData c ε :=
  { U := X.U
    V := X.V
    f := X.f
    g := X.g
    m := X.m
    isAffineOpen_U := X.isAffineOpen_U
    isAffineOpen_V := X.isAffineOpen_V
    sup_eq_top := X.sup_eq_top
    mem_U_iff := X.mem_U_iff
    inf_eq_basicOpen := X.inf_eq_basicOpen
    inf_eq_basicOpen_g := X.inf_eq_basicOpen_g
    res_f_mul_res_g := X.res_f_mul_res_g
    finite_f := X.finite_f
    finite_g := X.finite_g
    levelSet_free := X.levelSet_free }

/-- Round-trip: chart data of a datum maps back to the datum (rfl). -/
theorem finiteMapChartDataOfFiniteMapData_toFiniteMapData (X : Mzk1FiniteMapData c ε) :
    (finiteMapChartDataOfFiniteMapData X).toFiniteMapData = X := rfl

/-- Round-trip: datum of chart data maps back to the chart data (rfl). -/
theorem toFiniteMapData_finiteMapChartDataOfFiniteMapData (Y : FiniteMapChartData c ε) :
    finiteMapChartDataOfFiniteMapData Y.toFiniteMapData = Y := rfl

/-- Interface-level equivalence: chart data exists iff a finite-map datum exists. -/
theorem finiteMapChartData_nonempty_iff_finiteMapData_nonempty :
    Nonempty (FiniteMapChartData c ε) ↔ Nonempty (Mzk1FiniteMapData c ε) :=
  ⟨fun h => ⟨h.some.toFiniteMapData⟩,
   fun h => ⟨finiteMapChartDataOfFiniteMapData h.some⟩⟩

#check finiteMapChartData_nonempty_iff_finiteMapData_nonempty

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMapChartFromDataActual
end
