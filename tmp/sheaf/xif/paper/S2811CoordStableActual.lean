import tmp.sheaf.xif.paper.S2809E6FiniteActual
import tmp.sheaf.xif.paper.S2810F6GaloisTorsionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open WeierstrassCurve
open WeierstrassCurve.Affine
noncomputable section
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : S2790EL.curve.IsElliptic := inferInstance
local instance : DecidableEq S2790L := Classical.decEq S2790L
local instance : Nontrivial S2790L := inferInstance
noncomputable def S2811PointMap
    (σ : S2790L ≃ₐ[GaussianField] S2790L) :
    S2790EL.curve.toAffine.Point →+ S2790EL.curve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := S2790E.curve) σ.toAlgHom
example (σ : S2790L ≃ₐ[GaussianField] S2790L)
    (P : S2790EL.curve.toAffine.Point) :
    (S2811PointMap σ P).xRep 0 = σ (P.xRep 0) := by
  cases P with
  | zero =>
      change (0 : S2790EL.curve.toAffine.Point).xRep 0 = σ 1
      rw [WeierstrassCurve.Affine.Point.xRep_zero]
      simp
  | some x y h =>
      change (WeierstrassCurve.Affine.Point.map (W' := S2790E.curve) σ.toAlgHom
        (WeierstrassCurve.Affine.Point.some x y h)).xRep 0 = σ x
      rw [WeierstrassCurve.Affine.Point.map_some]
      rfl

lemma S2811_coords_map
    (σ : S2790L ≃ₐ[GaussianField] S2790L)
    (P : S2790EL.curve.toAffine.Point) :
    σ '' S2790PointCoords P ⊆ S2790PointCoords (S2811PointMap σ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [S2790PointCoords]
  · rintro z ⟨c, hc, rfl⟩
    simp only [S2790PointCoords, Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
    rcases hc with rfl | rfl
    · left
      simp [S2811PointMap, WeierstrassCurve.Affine.Point.map_some]
    · right
      simp [S2811PointMap, WeierstrassCurve.Affine.Point.map_some]


lemma S2811_coordSet_stable
    (σ : S2790L ≃ₐ[GaussianField] S2790L) :
    σ '' S2790CoordSet ⊆ S2790CoordSet := by
  rintro z ⟨c, hc, rfl⟩
  simp only [S2790CoordSet, Set.mem_iUnion] at hc ⊢
  rcases hc with ⟨P, hcP⟩
  refine ⟨⟨(S2811PointMap σ) P.1, ?_⟩, ?_⟩
  · rw [← AddMonoidHom.map_zsmul, P.2, AddMonoidHom.map_zero]
  · exact S2811_coords_map σ P.1 ⟨c, hcP, rfl⟩

/-- Normal: the adjoin of a Galois-stable coordinate set is normal. -/
theorem S2811_normal : Normal GaussianField S2790F6 := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  rw [S2790F6, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  intro x hx
  exact IntermediateField.subset_adjoin GaussianField S2790CoordSet
    (S2811_coordSet_stable σ hx)

/-- F6 is Galois over Q(i). -/
theorem S2811_isGalois : IsGalois GaussianField S2790F6 :=
  LeanFormal.IUT.XiFPaper.S2810F6GaloisTorsionActual.S2810_isGalois_of_normal
    S2811_normal

#check S2811_normal
#check S2811_isGalois
