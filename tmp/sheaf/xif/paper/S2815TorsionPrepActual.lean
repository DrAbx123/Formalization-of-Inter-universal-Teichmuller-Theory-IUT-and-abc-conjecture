import tmp.sheaf.xif.paper.S2812Torsion23Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open WeierstrassCurve
open WeierstrassCurve.Affine
noncomputable section
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
abbrev L1 : Type := AlgebraicClosure S2790F6
abbrev XF6 : PuncturedEllipticCurve S2790F6 := S2790E.baseChange S2790F6
abbrev XL1 : PuncturedEllipticCurve L1 := XF6.baseChange L1
local instance : XL1.curve.IsElliptic := inferInstance
local instance : DecidableEq L1 := Classical.decEq L1
local instance : Nontrivial L1 := inferInstance
local instance : S2790EL.curve.IsElliptic := inferInstance
local instance : DecidableEq S2790L := Classical.decEq S2790L
local instance : Nontrivial S2790L := inferInstance
noncomputable def S2815Equiv : L1 ≃ₐ[S2790F6] S2790L := S2812Equiv
noncomputable def S2815pmap :
    XL1.curve.toAffine.Point →+ S2790EL.curve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := S2790E.curve.toAffine) S2815Equiv.toAlgHom
noncomputable def S2815PointCoords (P : XL1.curve.toAffine.Point) : Set L1 :=
  match P with
  | .zero => ∅
  | .some x y _ => {x, y}
local instance : DecidableEq S2790F6 := Classical.decEq S2790F6
noncomputable def S2815qmap :
    XF6.curve.toAffine.Point →+ XL1.curve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := S2790E.curve.toAffine) (Algebra.ofId S2790F6 L1)
lemma S2815pmap_coords (P : XL1.curve.toAffine.Point) :
    S2815Equiv '' S2815PointCoords P ⊆ S2790PointCoords (S2815pmap P) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [S2815PointCoords]
  · rintro z ⟨c, hc, rfl⟩
    simp only [S2815PointCoords, Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
    rcases hc with rfl | rfl
    · left
      simp [S2815pmap, WeierstrassCurve.Affine.Point.map_some]
    · right
      simp [S2815pmap, WeierstrassCurve.Affine.Point.map_some]
lemma S2815pmap_six (P : XL1.curve.toAffine.Point) (hP : (6 : ℤ) • P = 0) :
    (6 : ℤ) • S2815pmap P = 0 := by
  rw [← AddMonoidHom.map_zsmul, hP, AddMonoidHom.map_zero]
lemma S2815coord_mem (P : XL1.curve.toAffine.Point) (hP : (6 : ℤ) • P = 0)
    {c : L1} (hc : c ∈ S2815PointCoords P) :
    S2815Equiv c ∈ S2790CoordSet := by
  refine Set.mem_iUnion.mpr ⟨⟨S2815pmap P, S2815pmap_six P hP⟩, ?_⟩
  exact S2815pmap_coords P ⟨c, hc, rfl⟩
lemma S2815_hcomp :
    (algebraMap S2790F6 L1).comp (algebraMap GaussianField S2790F6) =
      algebraMap GaussianField L1 := by
  apply RingHom.ext
  intro x
  exact IsScalarTower.algebraMap_apply GaussianField S2790F6 L1 x
lemma S2815_hns_align (x y : L1) (h : XL1.curve.toAffine.Nonsingular x y) :
    (S2790E.baseChange L1).curve.toAffine.Nonsingular x y := by
  simpa [PuncturedEllipticCurve.baseChange, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_map, S2815_hcomp] using h

