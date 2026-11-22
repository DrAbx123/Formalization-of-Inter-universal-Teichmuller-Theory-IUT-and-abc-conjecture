/-
# Gluing integral schemes

Mathlib-only lemmas: for a glue datum `D` of schemes whose pieces `D.U i` are all integral,
the glued scheme is reduced; it is preirreducible when all pairwise intersections `D.V (i, j)`
are nonempty; and it is integral when moreover the index type is nonempty.

The last nonemptiness hypothesis cannot be dispensed with: if the index type is empty, then
the assumptions are vacuous while the glued scheme is empty, so it is not integral.
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Sets.OpenCover

noncomputable section

open CategoryTheory Function TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.GlueData

variable (D : Scheme.GlueData)

/-- A glued scheme whose pieces are integral is reduced. -/
theorem glued_isReduced [∀ i, IsIntegral (D.U i)] : IsReduced D.glued := by
  haveI h : ∀ x : D.glued, _root_.IsReduced (D.glued.presheaf.stalk x) := by
    intro x
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
    exact isReduced_of_injective _
      (asIso <| (D.ι i).stalkMap y).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk D.glued

/-- A glued scheme whose pieces are integral is preirreducible, provided that all pairwise
intersections are nonempty. -/
theorem glued_preirreducible [∀ i, IsIntegral (D.U i)]
    (hne : ∀ i j, Nonempty (D.V (i, j))) : PreirreducibleSpace D.glued := by
  have hpre (i : D.J) : PreirreducibleSpace ↥((D.ι i).opensRange) := by
    refine Subtype.preirreducibleSpace ?_
    have himg : IsPreirreducible ((D.ι i) '' (Set.univ : Set ↥(D.U i))) :=
      (PreirreducibleSpace.isPreirreducible_univ (X := ↥(D.U i))).image (D.ι i)
        (Scheme.Hom.continuous (D.ι i)).continuousOn
    simpa using himg
  have hn : Pairwise ((¬ Disjoint · ·) on fun i : D.J => (D.ι i).opensRange) := by
    intro i j _
    obtain ⟨x⟩ := hne i j
    have hpt : D.ι j ((D.t i j ≫ D.f j i) x) = D.ι i (D.f i j x) := by
      have h := congrArg (fun g : D.V (i, j) ⟶ D.glued => g x) (D.glue_condition i j)
      exact h
    change ¬ Disjoint ((D.ι i).opensRange) ((D.ι j).opensRange)
    rw [← Opens.coe_disjoint]
    refine Set.not_disjoint_iff_nonempty_inter.mpr ⟨D.ι i (D.f i j x), ?_, ?_⟩
    · exact Scheme.Hom.mem_opensRange.mpr ⟨D.f i j x, rfl⟩
    · rw [← hpt]
      exact Scheme.Hom.mem_opensRange.mpr ⟨(D.t i j ≫ D.f j i) x, rfl⟩
  have hcover : IsOpenCover (fun i : D.J => (D.ι i).opensRange) := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    rw [Opens.mem_iSup]
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
    exact ⟨i, Scheme.Hom.mem_opensRange.mpr ⟨y, rfl⟩⟩
  exact PreirreducibleSpace.of_isOpenCover
    (U := fun i : D.J => (D.ι i).opensRange) hn hcover hpre

/-- A glued scheme whose pieces are integral is integral, provided that all pairwise
intersections are nonempty and that the index type is nonempty. -/
theorem glued_isIntegral [∀ i, IsIntegral (D.U i)]
    (hne : ∀ i j, Nonempty (D.V (i, j))) [Nonempty D.J] : IsIntegral D.glued := by
  haveI : IsReduced D.glued := glued_isReduced D
  haveI : PreirreducibleSpace D.glued := glued_preirreducible D hne
  obtain ⟨i⟩ := ‹Nonempty D.J›
  obtain ⟨y⟩ := (inferInstance : Nonempty (D.U i))
  haveI : Nonempty D.glued := ⟨D.ι i y⟩
  haveI : IrreducibleSpace D.glued :=
    { toPreirreducibleSpace := ‹PreirreducibleSpace D.glued›
      toNonempty := ‹Nonempty D.glued› }
  exact isIntegral_of_irreducibleSpace_of_isReduced D.glued

end Scheme.GlueData

end AlgebraicGeometry

#print axioms AlgebraicGeometry.Scheme.GlueData.glued_isReduced
#print axioms AlgebraicGeometry.Scheme.GlueData.glued_preirreducible
#print axioms AlgebraicGeometry.Scheme.GlueData.glued_isIntegral
