import tmp.sheaf.xif.paper.Mzk1GeomCoreFiniteMapChartInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Chart interface basic facts (green dep); no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem chartBasic_m (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m := rfl

theorem chartBasic_U (X : FiniteMapChartData c ε) :
    (X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ := X.coe_U_eq_compl

theorem chartBasic_mem_iff (X : FiniteMapChartData c ε) (x : C) :
    x ∈ X.toFiniteMapData.U ↔ x ∉ Set.range ε.1.base := X.mem_U_iff x

theorem chartBasic_bundle (X : FiniteMapChartData c ε) :
    X.toFiniteMapData.m = X.m ∧
      (X.toFiniteMapData.U : Set C) = (Set.range ε.1.base)ᶜ :=
  ⟨chartBasic_m X, chartBasic_U X⟩

def chartBasicRows : List (String × String × String) :=
  [ ("degree identity", "PROVED", "chartBasic_m"),
    ("U = complement of section range", "PROVED", "chartBasic_U"),
    ("mem_U_iff projection", "PROVED", "chartBasic_mem_iff"),
    ("bundle", "PROVED", "chartBasic_bundle") ]

theorem chartBasicRows_length : chartBasicRows.length = 4 := rfl

#check chartBasic_bundle
#check chartBasicRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBasicFactsActual
end