/-
# S2513: the separation field of `S2508CuspDatum` for the point at infinity

`S2508CuspDataUB` carries, among its three scheme/stack-level inputs, the
separation field

    separation : ∀ s : S2508ResidueScheme ⟶ S2508AffineOver,
      s ≫ S2508ChartOverMap ≠ point

saying that the point at infinity of `P¹_UB` lies outside the image of the affine
chart.  `S2511InfinityPointUB` supplied the point

    S2511Point : S2508ResidueScheme ⟶ S2508FOver,

the residue-field point `[1 : 0]` of the chart `X 0 ≠ 0`.  This file proves the
separation field for that point, unconditionally:

    S2513Separation : ∀ s, s ≫ S2508ChartOverMap ≠ S2511Point.

## Proof

1. The affine chart `S2508ChartMap = Spec (Away 𝒜 (X 1)) ≅ Spec UB[x] ⟶ P¹_UB` is the
   open immersion of the chart `X 1 ≠ 0`; hence
   `S2508ChartMap.opensRange = Proj.basicOpen 𝒜 (X 1)` (S2513ChartMap_opensRange),
   using `Scheme.Hom.opensRange_comp_of_isIso` and `Proj.opensRange_awayι`.
2. The point `S2511pointMap = Spec (chart0) ≫ awayι (X 0)` factors through the
   chart `X 0 ≠ 0`, so the preimage of `Proj.basicOpen 𝒜 (X 1)` is computed
   by `Proj.awayι_preimage_basicOpen`: it is the basic open of the element
   `X 1 / X 0` of the chart ring `Away 𝒜 (X 0)`.  The residue-field map
   `chart0` sends that element to `phi0 (X 1) / phi0 (X 0) = 0`, and
   `PrimeSpectrum.basicOpen 0 = ⊥`.  Hence the preimage is empty
   (S2513pointMap_preimage), i.e. the point at infinity misses `D₊(X 1)`
   (S2513pointMap_notMem).
3. If `s ≫ S2508ChartOverMap = S2511Point` then on underlying schemes
   `(s ≫ S2508ChartOverMap).left = S2511pointMap`.  Every point of the residue
   scheme `Spec UB` is sent by `(s ≫ S2508ChartOverMap).left = s.left ≫ chart` into
   `S2508ChartMap.opensRange = Proj.basicOpen 𝒜 (X 1)`, while the point at infinity
   misses that open and `Spec UB` is nonempty.  Contradiction.

No `sorry`, no `axiom`, no new hypothesis.  The axiom audit at the end records the
exact cost.
-/
import tmp.sheaf.xif.paper.S2508CuspDataUB
import tmp.sheaf.xif.paper.S2511InfinityPointUB

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2505AwayEquivActual
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB
open LeanFormal.IUT.XiFPaper.S2511InfinityPointUB

namespace LeanFormal.IUT.XiFPaper.S2513SeparationUB

local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chart map of the affine chart `X 1 ≠ 0` is an open immersion (S2508). -/
local instance s2513ChartMapOpenImmersion : IsOpenImmersion S2508ChartMap :=
  S2508ChartMap_isOpenImmersion

/-- The same chart map, read as a morphism of `UB`-schemes. -/
local instance s2513ChartOverMapLeftOpenImmersion :
    IsOpenImmersion S2508ChartOverMap.left :=
  S2508ChartOverMap_isOpenImmersion

/-! ## 1. The image of the affine chart is `D₊(X 1)` -/

/-- **The image of the chart is the open `D₊(X 1)`**: the chart identification
`Away 𝒜 (X 1) ≅ UB[x]` is an isomorphism of schemes and `Proj.awayι` is the open
immersion of `D₊(X 1)`. -/
theorem S2513ChartMap_opensRange :
    S2508ChartMap.opensRange = Proj.basicOpen S2504Grading (MvPolynomial.X 1) := by
  haveI h1 : IsIso (CommRingCat.ofHom S2504AwayRingEquiv.toRingHom) :=
    S2504AwayRingEquiv.toCommRingCatIso.isIso_hom
  haveI h2 : IsIso S2504SpecMap := by
    change IsIso (Spec.map (CommRingCat.ofHom S2504AwayRingEquiv.toRingHom))
    infer_instance
  haveI h3 : IsOpenImmersion S2504OpenMap := by
    change IsOpenImmersion (Proj.awayι S2504Grading (MvPolynomial.X 1)
      (by rw [MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_X UB 1)
      (by norm_num))
    infer_instance
  exact (Scheme.Hom.opensRange_comp_of_isIso S2504SpecMap S2504OpenMap).trans
    (Proj.opensRange_awayι S2504Grading (MvPolynomial.X 1)
      (by rw [MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_X UB 1)
      (by norm_num))

/-- The same statement for the chart map viewed as a morphism of `UB`-schemes. -/
theorem S2513ChartOverMap_opensRange :
    S2508ChartOverMap.left.opensRange = Proj.basicOpen S2504Grading (MvPolynomial.X 1) :=
  S2513ChartMap_opensRange

/-! ## 2. The point at infinity misses `D₊(X 1)` -/

/-- The evaluation at `[1 : 0]` kills the coordinate `X 1`. -/
theorem S2513phi0_X1 : S2511phi0 (MvPolynomial.X 1) = 0 := by
  have h : (fun i : Fin 2 => if i = 0 then (1 : UB) else 0) 1 = 0 := by
    show (if (1 : Fin 2) = 0 then (1 : UB) else 0) = 0
    rw [if_neg (by decide)]
  simpa only [S2511phi0, MvPolynomial.eval₂Hom_X'] using h

/-- **The chart ring map of `[1 : 0]` kills `X 1 / X 0`**: the element whose basic
open is the preimage of `D₊(X 1)` in the chart `X 0 ≠ 0` evaluates to `0 / 1 = 0`. -/
theorem S2513chart0_localizationElem :
    S2511chart0 (Away.isLocalizationElem S2511X0_mem X1_mem) = 0 := by
  have hv : S2511phi0 S2511X0 * (1 : UB) = 1 := by
    rw [S2511phi0_X0, one_mul]
  simp only [S2511chart0, RingHom.comp_apply, Away.isLocalizationElem]
  rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk S2511phi0 S2511X0 (MvPolynomial.X 1 ^ 1) 1 hv 1]
  rw [map_pow, pow_one, S2513phi0_X1]
  simp

/-- **The point at infinity misses the affine chart**: the preimage under
`S2511pointMap` of `D₊(X 1)` is empty. -/
theorem S2513pointMap_preimage :
    S2511pointMap ⁻¹ᵁ (Proj.basicOpen S2504Grading (MvPolynomial.X 1)) = ⊥ := by
  rw [S2511pointMap]
  simp only [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen (𝒜 := S2504Grading)
    S2511X0_mem (by norm_num) X1_mem (by norm_num)]
  rw [S2511pointChart, SpecMap_preimage_basicOpen]
  show PrimeSpectrum.basicOpen
      (S2511chart0 (Away.isLocalizationElem S2511X0_mem X1_mem)) = ⊥
  rw [S2513chart0_localizationElem]
  simp

/-- **Every point of `Spec UB` is sent by the point at infinity outside `D₊(X 1)`. -/
theorem S2513pointMap_notMem (x : Spec (CommRingCat.of UB)) :
    S2511pointMap x ∉ Proj.basicOpen S2504Grading (MvPolynomial.X 1) := by
  intro hx
  have h2 : x ∈ S2511pointMap ⁻¹ᵁ
      (Proj.basicOpen S2504Grading (MvPolynomial.X 1)) :=
    (Scheme.Hom.mem_preimage _).mpr hx
  rw [S2513pointMap_preimage] at h2
  exact TopologicalSpace.Opens.mem_bot.mp h2

/-! ## 3. The separation -/

/-- **The point at infinity is separated from the affine chart.**  No morphism from
the residue scheme `Spec UB` to the affine chart, followed by the chart map, gives the
point `[1 : 0]`. -/
theorem S2513Separation :
    ∀ s : S2508ResidueScheme ⟶ S2508AffineOver,
      s ≫ S2508ChartOverMap ≠ S2511Point := by
  intro s h
  have hleft : (s ≫ S2508ChartOverMap).left = S2511pointMap := by
    rw [h]
    rfl
  let x : Spec (CommRingCat.of UB) := ⟨⊥, Ideal.isPrime_bot⟩
  have hx : S2511pointMap x ∈ Proj.basicOpen S2504Grading (MvPolynomial.X 1) := by
    rw [← hleft]
    have hmem : S2508ChartOverMap.left (s.left x) ∈
        S2508ChartOverMap.left.opensRange :=
      Scheme.Hom.mem_opensRange.mpr ⟨s.left x, rfl⟩
    rw [S2513ChartOverMap_opensRange] at hmem
    show (s ≫ S2508ChartOverMap).left x ∈
      Proj.basicOpen S2504Grading (MvPolynomial.X 1)
    exact hmem
  exact S2513pointMap_notMem x hx

/-! ## 4. The cusp datum with this separation field -/

/-- **The cusp datum of S2508 with two of its three fields discharged**: the boundary
point is `S2511Point` and its separation from the affine chart is
`S2513Separation`.  The only remaining field is the representable
open-immersion property of the chart map of stacks. -/
noncomputable def S2513CuspDatumOf
    (h : Iut.EtaleStackOpenImmersion S2508StackOpenMap) : S2508CuspDatum where
  point := S2511Point
  separation := S2513Separation
  stackOpenImmersion := h

/-- **The exact first missing input of S2508**: `S2508Missing` now follows from the
representable-open-immersion property of the chart map of stacks alone. -/
theorem S2513Missing_of_stackOpenImmersion
    (h : Iut.EtaleStackOpenImmersion S2508StackOpenMap) : S2508Missing :=
  ⟨S2513CuspDatumOf h⟩

/-! ## 5. Target-locked type checks -/

/-- Type lock: the separation statement has exactly the frozen target type. -/
example : ∀ s : S2508ResidueScheme ⟶ S2508AffineOver,
    s ≫ S2508ChartOverMap ≠ S2511Point := S2513Separation

/-- The separation field of `S2508CuspDatum` is available for `S2511Point`. -/
example : ∀ s : S2508ResidueScheme ⟶ S2508AffineOver,
    s ≫ S2508ChartOverMap ≠ S2511Point := fun s => S2513Separation s

/-! ## 6. Axiom audit -/

#print axioms S2513ChartMap_opensRange
#print axioms S2513ChartOverMap_opensRange
#print axioms S2513phi0_X1
#print axioms S2513chart0_localizationElem
#print axioms S2513pointMap_preimage
#print axioms S2513pointMap_notMem
#print axioms S2513Separation
#print axioms S2513CuspDatumOf
#print axioms S2513Missing_of_stackOpenImmersion

end LeanFormal.IUT.XiFPaper.S2513SeparationUB
end
