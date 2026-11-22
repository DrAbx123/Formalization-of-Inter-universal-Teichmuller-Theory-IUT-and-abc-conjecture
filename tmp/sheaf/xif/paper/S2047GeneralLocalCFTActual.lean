import tmp.sheaf.xif.paper.S2027LocalArtinActual
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Infinite

/-!
# S2047: the general local Artin map, torsion identification, norm compatibility

See the final report for the mathematical commentary.  This file is the Lean
counterpart: unconditional carriers and norm theory, the precise missing
inputs, and the strongest actual reduction (construction of the global local
Artin map from the finite-level symbol data).

No `sorry`, no `axiom`, no `Nonempty` gate.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false

noncomputable section
open scoped DirectSum commutatorElement
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual

namespace LeanFormal.IUT.XiFPaper.S2047GeneralLocalCFTActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The norm subgroup of a finite extension of `L` -/

/-- The norm subgroup `N_{M/L} M^×` of a finite extension `M` of `L`, as a
subgroup of `L^×`: the image of the norm map on units. -/
noncomputable def normSubgroup (U : Index p)
    (M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])) :
    Subgroup (localField p U)ˣ :=
  Subgroup.map (Units.map (Algebra.norm (localField p U) : M →* localField p U)) ⊤

/-- Membership in the norm subgroup. -/
theorem mem_normSubgroup {U : Index p}
    {M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])}
    {x : (localField p U)ˣ} :
    x ∈ normSubgroup p U M ↔
      ∃ y : Mˣ, Units.map (Algebra.norm (localField p U)) y = x := by
  simp [normSubgroup]

/-- **The easy half of the norm limitation theorem.**  If `M ≤ N` then every
norm from `N` is a norm from `M`: `N_{N/L} N^× ≤ N_{M/L} M^×`.  This is norm
transitivity `Algebra.norm_norm`, and it is the inclusion that survives
without local class field theory.  The reverse inclusion for `M = N^ab` is the
norm limitation theorem, `NormLimitationHard` below. -/
theorem normSubgroup_antitone {U : Index p}
    {M N : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])}
    (h : M ≤ N) : normSubgroup p U N ≤ normSubgroup p U M := by
  letI : Algebra M N := RingHom.toAlgebra (IntermediateField.inclusion h).toRingHom
  haveI : IsScalarTower (localField p U) M N := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  intro x hx
  rw [mem_normSubgroup] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Units.map (Algebra.norm M) y, ?_⟩
  apply Units.ext
  change Algebra.norm (localField p U) ((Algebra.norm M) (y : ↥N)) =
    Algebra.norm (localField p U) (y : ↥N)
  exact Algebra.norm_norm (R := localField p U) (S := M) (A := N) (a := (y : ↥N))

/-- The norm of a root of unity of `M` is a root of unity of `L`. -/
theorem isOfFinOrder_norm {U : Index p}
    {M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])}
    (u : Mˣ) (hu : IsOfFinOrder u) :
    IsOfFinOrder (Algebra.norm (localField p U) (u : M)) := by
  obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  have hval : ((u : M) ^ n) = 1 := by
    rw [← Units.val_pow_eq_pow_val u n, hun]
    rfl
  rw [← map_pow, hval, map_one]

/-! ## 2. Intermediate fields of `L^ab` are normal over `L` -/

/-- The fixing subgroup of any intermediate field of `L^ab` contains the closed
commutator subgroup of `Gal(Qbar_p/L)`, hence is normal in it. -/
theorem fixingSubgroup_normal_of_le_maximalAbelianExtension {U : Index p}
    (M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p]))
    (hM : M ≤ maximalAbelianExtension p U) : M.fixingSubgroup.Normal := by
  rw [← Subgroup.commutator_top_left_le_iff]
  refine le_trans (Subgroup.commutator_mono le_rfl le_top) ?_
  have h := IntermediateField.fixingSubgroup_antitone hM
  rw [fixingSubgroup_maximalAbelianExtension] at h
  exact le_trans (Subgroup.le_topologicalClosure (commutator (localGaloisGroup p U))) h

/-- **Every intermediate field of `L^ab / L` is normal over `L`.**  Hence
restriction of `L`-automorphisms along inclusions of such fields is available
(`AlgEquiv.restrictNormalHom`), which is what the inverse-limit construction of
the global Artin map needs. -/
theorem normal_of_le_maximalAbelianExtension {U : Index p}
    (M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p]))
    (hM : M ≤ maximalAbelianExtension p U) : Normal (localField p U) M := by
  haveI : IsGalois (localField p U) (AlgebraicClosure ℚ_[p]) := inferInstance
  haveI h : M.fixingSubgroup.Normal :=
    fixingSubgroup_normal_of_le_maximalAbelianExtension p U M hM
  exact (InfiniteGalois.normal_iff_isGalois M).mp h |>.to_normal

/-! ## 3. Finite abelian subextensions of `L^ab` -/

/-- A finite extension `M / L` inside `L^ab`.  Every such `M` is automatically
abelian over `L`, because `Gal(L^ab/L)` is abelian; the structure records the
finitude and the containment. -/
structure FiniteAbSub (U : Index p) where
  /-- The intermediate field. -/
  M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])
  /-- It is finite over `L`. -/
  finite : FiniteDimensional (localField p U) M
  /-- It is contained in `L^ab`. -/
  le_ab : M ≤ maximalAbelianExtension p U

namespace FiniteAbSub

variable {U : Index p}

instance (M : FiniteAbSub p U) : FiniteDimensional (localField p U) M.M := M.finite

instance (M : FiniteAbSub p U) : Normal (localField p U) M.M :=
  normal_of_le_maximalAbelianExtension p U M.M M.le_ab

/-- The norm subgroup of a finite abelian subextension. -/
abbrev norm (M : FiniteAbSub p U) : Subgroup (localField p U)ˣ :=
  normSubgroup p U M.M

end FiniteAbSub

/-- The quotient map `L^×/N_N → L^×/N_M` for `M ≤ N`, induced by the
inclusion of norm subgroups `N_N ≤ N_M`. -/
noncomputable def normQuotientMap {U : Index p} {M N : FiniteAbSub p U}
    (h : M.M ≤ N.M) :
    (localField p U)ˣ ⧸ FiniteAbSub.norm (p := p) (U := U) N →*
      (localField p U)ˣ ⧸ FiniteAbSub.norm (p := p) (U := U) M :=
  QuotientGroup.lift _
    (QuotientGroup.mk' (FiniteAbSub.norm (p := p) (U := U) M))
    (by
      intro x hx
      have hle : FiniteAbSub.norm (p := p) (U := U) N ≤
          FiniteAbSub.norm (p := p) (U := U) M := normSubgroup_antitone p U h
      simpa [QuotientGroup.ker_mk'] using hle hx)

/-- The restriction map `Gal(N/L) →* Gal(M/L)` for `M ≤ N` inside `L^ab`. -/
noncomputable def restrictGal {U : Index p} {M N : FiniteAbSub p U}
    (h : M.M ≤ N.M) :
    Gal(N.M / localField p U) →* Gal(M.M / localField p U) :=
  letI : Algebra M.M N.M := RingHom.toAlgebra (IntermediateField.inclusion h).toRingHom
  haveI : IsScalarTower (localField p U) M.M N.M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  AlgEquiv.restrictNormalHom M.M

/-! ## 4. The finite-level local Artin symbol: the precise missing input -/

/-- **The local reciprocity law for every finite abelian `M / L` inside
`L^ab`**, stated as data: an isomorphism `L^× / N_{M/L} M^× ≃* Gal(M/L)`,
natural in `M`.

This is the theorem of local class field theory whose construction is missing
from Mathlib v4.32.2: the tree has neither the Artin symbol, nor Lubin–Tate
theory, nor the existence theorem.  It is a structure of *data*, not a
`Nonempty` proposition and not an axiom: a provider must supply the actual
isomorphisms and the naturality square.  Everything below is derived from it. -/
structure LocalArtinSymbolData (U : Index p) where
  /-- The finite-level reciprocity isomorphism. -/
  recip : (M : FiniteAbSub p U) →
    (localField p U)ˣ ⧸ FiniteAbSub.norm (p := p) (U := U) M ≃*
      Gal(M.M / localField p U)
  /-- Naturality in `M`: restriction of `rec_N(x)` to `M` is `rec_M(x)`. -/
  natural : ∀ {M N : FiniteAbSub p U} (h : M.M ≤ N.M) (x : (localField p U)ˣ),
    restrictGal p U h (recip N (QuotientGroup.mk x)) =
      recip M (normQuotientMap p U h (QuotientGroup.mk x))

namespace LocalArtinSymbolData

variable {U : Index p} (d : LocalArtinSymbolData p U)

/-- The finite-level map `L^× →* Gal(M/L)`, i.e. `recip` composed with the
quotient projection. -/
noncomputable def recipMap (M : FiniteAbSub p U) :
    (localField p U)ˣ →* Gal(M.M / localField p U) :=
  (d.recip M).toMonoidHom.comp (QuotientGroup.mk' (FiniteAbSub.norm (p := p) (U := U) M))

@[simp] theorem recipMap_apply (M : FiniteAbSub p U) (x : (localField p U)ˣ) :
    d.recipMap M x = d.recip M (QuotientGroup.mk x) := rfl

theorem recipMap_inv (M : FiniteAbSub p U) (x : (localField p U)ˣ) :
    d.recipMap M x⁻¹ = (d.recipMap M x)⁻¹ := map_inv _ _

/-- Naturality in the `recipMap` form. -/
theorem restrict_recipMap {M N : FiniteAbSub p U} (h : M.M ≤ N.M)
    (x : (localField p U)ˣ) :
    restrictGal p U h (d.recipMap N x) = d.recipMap M x := by
  have := d.natural h x
  simpa [recipMap, normQuotientMap] using this

/-- The comparison of the finite-level maps along an inclusion, on elements. -/
theorem recip_restrict_apply {M N : FiniteAbSub p U} (h : M.M ≤ N.M)
    (x : (localField p U)ˣ) (y : ↥M.M) :
    (((d.recipMap N x) ⟨(y : AlgebraicClosure ℚ_[p]), h y.2⟩ : ↥N.M) :
        AlgebraicClosure ℚ_[p]) =
      (((d.recipMap M x) y : ↥M.M) : AlgebraicClosure ℚ_[p]) := by
  have hn := congrArg (fun f : Gal(M.M / localField p U) =>
    ((f y : ↥M.M) : AlgebraicClosure ℚ_[p])) (d.restrict_recipMap (p := p) h x)
  simpa [restrictGal, AlgEquiv.restrictNormalHom_apply] using hn

end LocalArtinSymbolData

/-! ## 5. The field generated by one element of `L^ab` -/

/-- The finite extension of `L` generated by one element of `L^ab`. -/
noncomputable def genField {U : Index p}
    (y : ↥(maximalAbelianExtension p U)) : FiniteAbSub p U where
  M := IntermediateField.adjoin (localField p U) {(y : AlgebraicClosure ℚ_[p])}
  finite := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    haveI : Algebra.IsAlgebraic (localField p U) (AlgebraicClosure ℚ_[p]) := inferInstance
    have hx' : x = (y : AlgebraicClosure ℚ_[p]) := by simpa using hx
    rw [hx']
    exact (Algebra.IsAlgebraic.isAlgebraic (x := (y : AlgebraicClosure ℚ_[p]))).isIntegral
  le_ab := by
    rw [IntermediateField.adjoin_le_iff]
    rintro z rfl
    exact y.2

/-- The generating element lies in the field it generates. -/
theorem mem_genField {U : Index p} (y : ↥(maximalAbelianExtension p U)) :
    (y : AlgebraicClosure ℚ_[p]) ∈ (genField p U y).M :=
  IntermediateField.subset_adjoin (localField p U) {(y : AlgebraicClosure ℚ_[p])}
    (Set.mem_singleton _)

/-- The field generated by `y` is the smallest finite subextension containing
`y`. -/
theorem genField_le_of_mem {U : Index p} {M : FiniteAbSub p U}
    {y : ↥(maximalAbelianExtension p U)}
    (hy : (y : AlgebraicClosure ℚ_[p]) ∈ M.M) : (genField p U y).M ≤ M.M := by
  rw [IntermediateField.adjoin_le_iff]
  rintro z rfl
  exact hy

/-- The finite extension generated by two elements of `L^ab`. -/
noncomputable def pairField {U : Index p}
    (y z : ↥(maximalAbelianExtension p U)) : FiniteAbSub p U where
  M := IntermediateField.adjoin (localField p U)
    {(y : AlgebraicClosure ℚ_[p]), (z : AlgebraicClosure ℚ_[p])}
  finite := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    haveI : Algebra.IsAlgebraic (localField p U) (AlgebraicClosure ℚ_[p]) := inferInstance
    have hx' : x = (y : AlgebraicClosure ℚ_[p]) ∨ x = (z : AlgebraicClosure ℚ_[p]) := by
      simpa using hx
    rcases hx' with h | h
    · rw [h]
      exact (Algebra.IsAlgebraic.isAlgebraic (x := (y : AlgebraicClosure ℚ_[p]))).isIntegral
    · rw [h]
      exact (Algebra.IsAlgebraic.isAlgebraic (x := (z : AlgebraicClosure ℚ_[p]))).isIntegral
  le_ab := by
    rw [IntermediateField.adjoin_le_iff]
    rintro w (rfl | rfl)
    · exact y.2
    · exact z.2

theorem mem_pairField_left {U : Index p} (y z : ↥(maximalAbelianExtension p U)) :
    (y : AlgebraicClosure ℚ_[p]) ∈ (pairField p U y z).M :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem mem_pairField_right {U : Index p} (y z : ↥(maximalAbelianExtension p U)) :
    (z : AlgebraicClosure ℚ_[p]) ∈ (pairField p U y z).M :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem mem_pairField_add {U : Index p} (y z : ↥(maximalAbelianExtension p U)) :
    ((y + z : ↥(maximalAbelianExtension p U)) : AlgebraicClosure ℚ_[p]) ∈
      (pairField p U y z).M := by
  have h1 := mem_pairField_left p U y z
  have h2 := mem_pairField_right p U y z
  have := (pairField p U y z).M.add_mem h1 h2
  simpa using this

theorem mem_pairField_mul {U : Index p} (y z : ↥(maximalAbelianExtension p U)) :
    ((y * z : ↥(maximalAbelianExtension p U)) : AlgebraicClosure ℚ_[p]) ∈
      (pairField p U y z).M := by
  have h1 := mem_pairField_left p U y z
  have h2 := mem_pairField_right p U y z
  have := (pairField p U y z).M.mul_mem h1 h2
  simpa using this
