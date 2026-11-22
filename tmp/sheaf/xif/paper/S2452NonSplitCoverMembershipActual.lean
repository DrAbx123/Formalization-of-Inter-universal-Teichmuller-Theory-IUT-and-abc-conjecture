import tmp.sheaf.xif.paper.S2451NonSplitCoverActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2433NonidentityStrongRepresentable
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S2451NonSplitCoverActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2452NonSplitCoverMembershipActual

/-- The fold projection is etale. -/
theorem S2452Map_etale : AlgebraicGeometry.Etale (Over.Hom.left S2451Map) := by
  rw [S2451Map, S1897CoverOver_left]
  simpa [IUTII.Frobenioid.Example36.EtaleCoverFoundations.FiniteEtaleCover.structureMap]
    using S2433FoldCover.property.1

/-- The projection underlying S2451Map is the fold. -/
theorem S2452Map_left_eq_fold :
    Over.Hom.left S2451Map = Over.Hom.left (S1850Fold S2433T) := by
  rw [S2451Map, S1897CoverOver_left]
  rfl

/-- The fold is surjective because it has the first inclusion as a section. -/
theorem S2452Map_surj : Function.Surjective (Over.Hom.left S2451Map).base := by
  rw [S2452Map_left_eq_fold]
  have hleft : Over.Hom.left (S1850Inl S2433T) ≫
      Over.Hom.left (S1850Fold S2433T) = 𝟙 S2433T.left := by
    have h := congrArg Over.Hom.left (S1850Inl_fold S2433T)
    simpa [Over.comp_left, Over.id_left] using h
  have hbase := congrArg (fun f : S2433T.left ⟶ S2433T.left => f.base) hleft
  rw [AlgebraicGeometry.Scheme.Hom.comp_apply, AlgebraicGeometry.Scheme.Hom.id_base] at hbase
  exact Function.Surjective.of_comp (by
    rw [hbase]
    exact Function.surjective_id)

/-- The singleton fold presieve is an actual etale precoverage cover. -/
theorem S2452Presieve_mem :
    S2451Presieve ∈ (S2093EtalePrecoverage S1726K).coverings S2451S := by
  rw [S2093EtalePrecoverage, CategoryTheory.Precoverage.mem_comap_iff]
  rw [S2451Presieve, Presieve.map_singleton]
  change Presieve.singleton ((Over.forget (AlgebraicGeometry.Spec (CommRingCat.of S1726K))).map S2451Map) ∈
    (AlgebraicGeometry.Scheme.precoverage @AlgebraicGeometry.Etale)
      ((Over.forget (AlgebraicGeometry.Spec (CommRingCat.of S1726K))).obj S2451S)
  rw [AlgebraicGeometry.Scheme.singleton_mem_precoverage_iff]
  exact ⟨S2452Map_surj, S2452Map_etale⟩

#print axioms S2452Map_etale
#print axioms S2452Presieve_mem

end LeanFormal.IUT.XiFPaper.S2452NonSplitCoverMembershipActual

end
