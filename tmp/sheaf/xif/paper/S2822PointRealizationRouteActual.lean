import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2822PointRealizationRouteActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
universe u
variable (K : Type u) [Field K]

/-- S2822 cover step: every point of `E37ProjGluedScheme` lies in the chart-Z
or chart-Y open chart. This is the scheme-level input for the F-point
surjectivity route. -/
theorem S2822_E37ProjCharts_jointly_surjective
    (e : E37ChartZOverlap K ≅ E37ChartYOverlap K)
    (x : E37ProjGluedScheme K e) :
    (∃ y, E37ProjChartZMap K e y = x) ∨
      (∃ y, E37ProjChartYMap K e y = x) := by
  obtain ⟨i, y, hy⟩ := (E37ProjGlueData K e).openCover.exists_eq x
  rcases i with ⟨b⟩
  cases b
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

#print axioms S2822_E37ProjCharts_jointly_surjective
end LeanFormal.IUT.XiFPaper.S2822PointRealizationRouteActual
end
