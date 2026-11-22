import tmp.sheaf.xif.paper.S2112ContH2LimitActual
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2112ContH2LimitActual
namespace LeanFormal.IUT.XiFPaper.S2114H2SurjectivityGapActual
universe u
section H2Comparison
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : ℕ → Type u) [∀ n, CommGroup (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, IsTopologicalGroup (A n)]
variable (proj : ∀ n, A (n+1) →* A n)
variable (actn : ∀ n, Iut.ContinuousGroupAction G (A n))
variable (compat : ∀ n (g : G) (x : A (n+1)),
  proj n ((actn (n+1)).act g x) = (actn n).act g (proj n x))
/-- The exact statement to prove: surjectivity of the degree-two comparison. -/
def S2114H2ComparisonSurjective : Prop :=
  Function.Surjective (h2Comparison A proj actn compat)
/-- The exact missing representative lift: a compatible family of level H2
classes is represented by one continuous 2-cocycle of the limit.  This is the
cocycle-level form of surjectivity (equivalently the lim^1 H^1 input). -/
structure S2114CompatibleRepresentativeLift where
  lift : LimH2 A proj actn compat →
    ContinuousTwoCocycle (A := LimCoeff A proj)
      (action := limitAction A proj actn compat)
  lift_spec : ∀ y : LimH2 A proj actn compat,
    z2ToLimH2 A proj actn compat (lift y) = y
/-- A compatible representative lift gives surjectivity of the comparison. -/
theorem S2114_surjective_of_representativeLift
    (L : S2114CompatibleRepresentativeLift A proj actn compat) :
    Function.Surjective (h2Comparison A proj actn compat) := by
  intro y
  refine ⟨QuotientGroup.mk (L.lift y), ?_⟩
  rw [h2Comparison_mk]
  exact L.lift_spec y
/-- Conversely, surjectivity produces a representative lift. -/
theorem S2114_representativeLift_of_surjective
    (h : Function.Surjective (h2Comparison A proj actn compat)) :
    Nonempty (S2114CompatibleRepresentativeLift A proj actn compat) := by
  classical
  choose c hc using fun y : LimH2 A proj actn compat =>
    QuotientGroup.mk'_surjective
      (coboundarySubgroup (action := limitAction A proj actn compat))
      (Classical.choose (h y))
  refine ⟨⟨c, ?_⟩⟩
  intro y
  have hspec := Classical.choose_spec (h y)
  have hc' := hc y
  rw [← hc'] at hspec
  simpa [h2Comparison_mk] using hspec
#check S2114H2ComparisonSurjective
#check S2114CompatibleRepresentativeLift
#check S2114_surjective_of_representativeLift
#check S2114_representativeLift_of_surjective
end H2Comparison
end LeanFormal.IUT.XiFPaper.S2114H2SurjectivityGapActual
end
