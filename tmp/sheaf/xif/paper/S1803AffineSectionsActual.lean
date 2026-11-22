/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Artinian.Module
import tmp.sheaf.xif.paper.S1780GeometricFiberFintypeActual

/-!
# S1803: the affine sections bridge and finiteness of sections

S1780 isolates, as the first missing input towards
S1735GeometricFiberFintypeRequired, the finiteness of the section type
S1735BaseScheme ⟶ S1780Model cover, where S1780Model cover is a scheme finite
over the actual base Spec F'.

The mathematical content of that first input is the standard affine-sections
bridge: for an affine scheme Y.left finite over Spec K, the sections of
Y → Spec K are the K-algebra homomorphisms Γ(Y.left, ⊤) →ₐ[K] K.  The
equivalence is built from

* Scheme.ΓSpecIso : Γ(Spec K, ⊤) ≅ K,
* Scheme.isoSpec : X ≅ Spec Γ(X, ⊤) for affine X,
* Scheme.isoSpec_hom_naturality / Scheme.isoSpec_inv_naturality,
* Scheme.Hom.appTop and its functoriality,
* Module.Finite K Γ(Y.left, ⊤), obtained from IsFinite Y.hom
  (Scheme.Hom.finite_appTop) and the ring isomorphism Γ(Spec K) ≅ K.

No equivalence, Fintype instance or finiteness statement is postulated; all
of them are constructed.

## Main results

* pointAlgebra: the K-algebra structure on Γ(Y.left, ⊤) induced by Y → Spec K;
* affineSectionsEquiv: the affine-sections equivalence
  (Spec K ⟶ Y) ≃ (Γ(Y.left, ⊤) →ₐ[K] K);
* schemeSectionsEquiv: the same equivalence for literal scheme sections
  {s : Spec K ⟶ Y.left // s ≫ Y.hom = 𝟙 (Spec K)};
* moduleFinite_globalSections: Module.Finite K Γ(Y.left, ⊤) for finite
  Y → Spec K;
* sectionsFintype: Fintype of the section type for finite Y → Spec K;
* schemeSectionsFintype: Fintype of the literal scheme section type.

## S1780 application

The final section instantiates the bridge at S1780's actual orbicurve data and
proves that S1780SectionFintype holds for every actual cover, i.e. that the
first component of S1780FirstMissing is unconditional.  The only remaining
S1780 input is the separate geometric comparison S1780FiberCovered.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1780GeometricFiberFintypeActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual.Paper

namespace LeanFormal.IUT.XiFPaper.S1803AffineSectionsActual

universe u

variable {K : Type u} [Field K]

/-- Spec K, the base of the affine-sections bridge. -/
abbrev specField (K : Type u) [Field K] : Scheme.{u} := Spec (CommRingCat.of K)

/-- The K-algebra structure on Γ(Y.left, ⊤) induced by the structure map
Y → Spec K.  This is the algebra structure used on the right-hand side of
affineSectionsEquiv. -/
@[reducible] noncomputable def pointAlgebra (Y : Over (specField K)) :
    Algebra K Γ(Y.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.hom.appTop).hom.toAlgebra

/-- The ring hom Γ(Y.left, ⊤) →+* K attached to a section of Y → Spec K. -/
noncomputable def sectionRingHom (Y : Over (specField K))
    (s : Over.mk (𝟙 (specField K)) ⟶ Y) : Γ(Y.left, ⊤) →+* K :=
  (s.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom

/-- A section of Y → Spec K gives a K-algebra map out of global sections.
The key point is that the composite ring map fixes K, using the fact that the
section composed with the structure map is the identity. -/
lemma sectionRingHom_commutes (Y : Over (specField K))
    (s : Over.mk (𝟙 (specField K)) ⟶ Y) (k : K) :
    sectionRingHom Y s
      (@algebraMap K Γ(Y.left, ⊤) _ _ (pointAlgebra Y) k) = k := by
  have hw : Y.hom.appTop ≫ s.left.appTop = 𝟙 Γ(specField K, ⊤) :=
    congrArg Scheme.Hom.appTop s.w
  have hw' : ∀ x, s.left.appTop.hom (Y.hom.appTop.hom x) = x := by
    intro x
    have h := congrArg (fun φ => φ.hom x) hw
    change s.left.appTop.hom (Y.hom.appTop.hom x) = x at h
    exact h
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      (s.left.appTop.hom (Y.hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k))) = k
  rw [hw']
  exact congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K => φ.hom k)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

/-- A section of Y → Spec K, as a K-algebra map
Γ(Y.left, ⊤) →ₐ[K] K. -/
noncomputable def sectionAlgHom (Y : Over (specField K))
    (s : Over.mk (𝟙 (specField K)) ⟶ Y) :
    letI := pointAlgebra Y
    (Γ(Y.left, ⊤) →ₐ[K] K) := by
  letI := pointAlgebra Y
  exact { toRingHom := sectionRingHom Y s
          commutes' := sectionRingHom_commutes Y s }

/-- A K-algebra map out of the global sections of an affine Y.left gives a
section of Y → Spec K, via Spec.map and Scheme.isoSpec.inv. -/
noncomputable def algHomSection (Y : Over (specField K)) [IsAffine Y.left]
    (ψ : letI := pointAlgebra Y
      (Γ(Y.left, ⊤) →ₐ[K] K)) :
    Over.mk (𝟙 (specField K)) ⟶ Y := by
  letI := pointAlgebra Y
  refine Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.left.isoSpec.inv) ?_
  change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.left.isoSpec.inv) ≫ Y.hom =
    𝟙 (specField K)
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality Y.hom]
  rw [← Category.assoc, ← Spec.map_comp]
  have hψ : Y.hom.appTop ≫ CommRingCat.ofHom ψ.toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    have hcomp : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Y.hom.appTop ≫
        CommRingCat.ofHom ψ.toRingHom = 𝟙 (CommRingCat.of K) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro k
      change ψ (@algebraMap K Γ(Y.left, ⊤) _ _ (pointAlgebra Y) k) = k
      simp
    have h' := (Iso.inv_comp_eq (Scheme.ΓSpecIso (CommRingCat.of K))).mp hcomp
    simpa using h'
  rw [hψ]
  rw [← Scheme.isoSpec_Spec_hom]
  exact (Spec (CommRingCat.of K)).isoSpec.hom_inv_id

/-- The two constructions are inverse to one another: a section is recovered
from its induced algebra map by Spec.map and Scheme.isoSpec.inv. -/
theorem algHomSection_sectionAlgHom (Y : Over (specField K)) [IsAffine Y.left]
    (s : Over.mk (𝟙 (specField K)) ⟶ Y) :
    algHomSection Y (sectionAlgHom Y s) = s := by
  letI := pointAlgebra Y
  let g : specField K ⟶ Y.left := s.left
  apply Over.OverMorphism.ext
  change (algHomSection Y (sectionAlgHom Y s)).left = g
  change Spec.map (CommRingCat.ofHom (sectionRingHom Y s)) ≫ Y.left.isoSpec.inv = g
  change Spec.map (g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) ≫
    Y.left.isoSpec.inv = g
  rw [Spec.map_comp]
  rw [← Scheme.isoSpec_Spec_hom]
  rw [Category.assoc]
  rw [Scheme.isoSpec_inv_naturality g]
  rw [Iso.hom_inv_id_assoc]

/-- The other round trip: the algebra map induced by the section attached to
ψ is ψ itself. -/
theorem sectionAlgHom_algHomSection (Y : Over (specField K)) [IsAffine Y.left]
    (ψ : letI := pointAlgebra Y
      (Γ(Y.left, ⊤) →ₐ[K] K)) :
    sectionAlgHom Y (algHomSection Y ψ) = ψ := by
  letI := pointAlgebra Y
  apply AlgHom.ext
  intro x
  change sectionRingHom Y (algHomSection Y ψ) x = ψ x
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    ((Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.left.isoSpec.inv).appTop.hom x) = ψ x
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ.toRingHom)
  have hnat_apply : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      ((Spec.map (CommRingCat.ofHom ψ.toRingHom)).appTop.hom y) =
      ψ.toRingHom ((Scheme.ΓSpecIso Γ(Y.left, ⊤)).hom.hom y) := by
    intro y
    exact congrArg (fun φ => φ.hom y) hnat
  have hinv : Y.left.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y.left, ⊤)).hom =
      𝟙 Γ(Y.left, ⊤) := by
    have h := congrArg Scheme.Hom.appTop (Y.left.isoSpec.hom_inv_id)
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, Scheme.isoSpec_hom,
      Scheme.toSpecΓ_appTop] using h
  have hinv_apply : ∀ y, (Scheme.ΓSpecIso Γ(Y.left, ⊤)).hom.hom
      (Y.left.isoSpec.inv.appTop.hom y) = y := by
    intro y
    have h := congrArg (fun φ => φ.hom y) hinv
    change (Scheme.ΓSpecIso Γ(Y.left, ⊤)).hom.hom
      (Y.left.isoSpec.inv.appTop.hom y) = y at h
    exact h
  have hstep : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      ((Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.left.isoSpec.inv).appTop.hom x) =
      ψ.toRingHom ((Scheme.ΓSpecIso Γ(Y.left, ⊤)).hom.hom
        (Y.left.isoSpec.inv.appTop.hom x)) := by
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact hnat_apply (Y.left.isoSpec.inv.appTop.hom x)
  rw [hstep, hinv_apply]
  rfl

/-- **Affine sections bridge.**  For Y affine over Spec K, sections of
Y → Spec K are equivalent to K-algebra maps Γ(Y.left, ⊤) →ₐ[K] K. -/
noncomputable def affineSectionsEquiv (Y : Over (specField K)) [IsAffine Y.left] :
    (Over.mk (𝟙 (specField K)) ⟶ Y) ≃
      letI := pointAlgebra Y
      (Γ(Y.left, ⊤) →ₐ[K] K) :=
  { toFun := sectionAlgHom Y
    invFun := algHomSection Y
    left_inv := algHomSection_sectionAlgHom Y
    right_inv := sectionAlgHom_algHomSection Y }

/-- Over-category sections are the literal scheme sections
{s : Spec K ⟶ Y.left // s ≫ Y.hom = 𝟙 (Spec K)}. -/
noncomputable def overSectionsEquiv (Y : Over (specField K)) :
    (Over.mk (𝟙 (specField K)) ⟶ Y) ≃
      {s : specField K ⟶ Y.left // s ≫ Y.hom = 𝟙 (specField K)} where
  toFun s := ⟨s.left, by
    have h := s.w
    change s.left ≫ Y.hom = 𝟙 (specField K) at h
    exact h⟩
  invFun s := Over.homMk s.1 (by
    change s.1 ≫ Y.hom = 𝟙 (specField K)
    exact s.2)
  left_inv s := by
    apply Over.OverMorphism.ext
    rfl
  right_inv s := by
    ext
    rfl

/-- The affine sections bridge stated for literal scheme morphisms
Spec K ⟶ Y.left satisfying s ≫ Y.hom = 𝟙 (Spec K). -/
noncomputable def schemeSectionsEquiv (Y : Over (specField K)) [IsAffine Y.left] :
    {s : specField K ⟶ Y.left // s ≫ Y.hom = 𝟙 (specField K)} ≃
      letI := pointAlgebra Y
      (Γ(Y.left, ⊤) →ₐ[K] K) :=
  (overSectionsEquiv Y).symm.trans (affineSectionsEquiv Y)

/-- **Finiteness of global sections.**  If Y → Spec K is finite, then
Γ(Y.left, ⊤) is a finite K-module.  The proof composes the finite ring map
Γ(Spec K) → Γ(Y.left) of Scheme.Hom.finite_appTop with the ring isomorphism
Γ(Spec K) ≅ K. -/
theorem moduleFinite_globalSections (Y : Over (specField K)) [IsAffine Y.left]
    [IsFinite Y.hom] :
    letI := pointAlgebra Y
    Module.Finite K Γ(Y.left, ⊤) := by
  letI := pointAlgebra Y
  have hf := Scheme.Hom.finite_appTop Y.hom
  have hg := RingEquiv.finite
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hcomp := RingHom.Finite.comp hf hg
  change Module.Finite K Γ(Y.left, ⊤)
  exact hcomp

/-- For a finite algebra A over a field K, the K-algebra maps A →ₐ[K] K form
a finite type.  This is the algebraic core used by S1780; it is reproduced
here so that the present file depends only on Mathlib. -/
@[reducible] noncomputable def finiteAlgHomFintype (A : Type u) [CommRing A]
    [Algebra K A] [Module.Finite K A] : Fintype (A →ₐ[K] K) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hkerIsPrime : ∀ φ : A →ₐ[K] K, (RingHom.ker φ.toRingHom).IsPrime :=
    fun φ => RingHom.ker_isPrime φ.toRingHom
  refine Fintype.ofInjective
    (fun φ : A →ₐ[K] K =>
      (⟨RingHom.ker φ.toRingHom, ?_⟩ : MaximalSpectrum A)) ?_
  · haveI := hkerIsPrime φ
    infer_instance
  · intro φ ψ h
    have hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom :=
      congrArg MaximalSpectrum.asIdeal h
    have hker' : ∀ a : A, φ a = 0 ↔ ψ a = 0 := by
      intro a
      have h1 : a ∈ RingHom.ker φ.toRingHom ↔ a ∈ RingHom.ker ψ.toRingHom := by
        rw [hker]
      exact ⟨fun h => RingHom.mem_ker.mpr (h1.mp (RingHom.mem_ker.mp h)),
        fun h => RingHom.mem_ker.mpr (h1.mpr (RingHom.mem_ker.mp h))⟩
    ext x
    by_cases hx : φ x = 0
    · rw [hx, (hker' x).mp hx]
    · have hφ1 : φ ((φ x) • (1 : A)) = φ x := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_one]
        simp
      have hψ1 : ψ ((φ x) • (1 : A)) = φ x := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_one]
        simp
      have hy : φ ((φ x) • (1 : A) - x) = 0 := by
        rw [map_sub, hφ1, sub_self]
      have hy2 : ψ ((φ x) • (1 : A) - x) = 0 := (hker' _).mp hy
      rw [map_sub, hψ1] at hy2
      exact sub_eq_zero.mp hy2

/-- Fintype of the K-algebra maps out of the global sections of a finite
affine scheme over Spec K. -/
@[reducible] noncomputable def sectionAlgHomFintype (Y : Over (specField K)) [IsAffine Y.left]
    [IsFinite Y.hom] :
    letI := pointAlgebra Y
    Fintype (Γ(Y.left, ⊤) →ₐ[K] K) := by
  letI := pointAlgebra Y
  haveI : Module.Finite K Γ(Y.left, ⊤) := moduleFinite_globalSections Y
  exact finiteAlgHomFintype (K := K) Γ(Y.left, ⊤)

/-- **Finiteness of the section type.**  For Y affine and finite over
Spec K, the type of sections of Y → Spec K is finite. -/
@[reducible] noncomputable def sectionsFintype (Y : Over (specField K)) [IsAffine Y.left]
    [IsFinite Y.hom] : Fintype (Over.mk (𝟙 (specField K)) ⟶ Y) := by
  letI := pointAlgebra Y
  haveI : Fintype (Γ(Y.left, ⊤) →ₐ[K] K) := sectionAlgHomFintype Y
  exact Fintype.ofEquiv (Γ(Y.left, ⊤) →ₐ[K] K) (affineSectionsEquiv Y).symm

/-- **Finiteness of literal scheme sections.**  For Y affine and finite over
Spec K, the literal section type
{s : Spec K ⟶ Y.left // s ≫ Y.hom = 𝟙 (Spec K)} is finite. -/
@[reducible] noncomputable def schemeSectionsFintype (Y : Over (specField K))
    [IsAffine Y.left] [IsFinite Y.hom] :
    Fintype {s : specField K ⟶ Y.left // s ≫ Y.hom = 𝟙 (specField K)} := by
  letI := pointAlgebra Y
  haveI : Fintype (Γ(Y.left, ⊤) →ₐ[K] K) := sectionAlgHomFintype Y
  exact Fintype.ofEquiv (Γ(Y.left, ⊤) →ₐ[K] K) (schemeSectionsEquiv Y).symm

/-! ## Application to S1780's first missing component -/

/-- The structure map of S1780Model cover is the underlying scheme morphism
of the projection S1780ModelOver cover. -/
lemma S1803Model_hom_eq (cover : S1735Cover) :
    (S1780Model cover).hom = (S1780ModelOver cover).left := by
  have h := (S1780ModelOver cover).w
  have hbase : S1735BaseScheme.hom = 𝟙 S1735BaseScheme.left := rfl
  rw [hbase, Category.comp_id] at h
  exact h.symm

/-- **S1780's first gap, filled.**  For every actual cover, the section type
S1735BaseScheme ⟶ S1780Model cover is finite. -/
theorem S1803_sectionFintype (cover : S1735Cover) : S1780SectionFintype cover := by
  let Y : Over (specField S1735K) := S1780Model cover
  have hhom : Y.hom = (S1780ModelOver cover).left := S1803Model_hom_eq cover
  haveI : IsFinite Y.hom := by
    rw [hhom]
    exact (S1780Model_finiteEtale cover).1
  haveI : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  exact ⟨sectionsFintype Y⟩

/-- The first conjunct of S1780's packaged first missing input, unconditionally. -/
theorem S1803_firstMissing_sections :
    (∀ cover : S1735Cover, S1780SectionFintype cover) :=
  S1803_sectionFintype

/-! ## Axiom footprint -/

#print axioms sectionRingHom_commutes
#print axioms algHomSection_sectionAlgHom
#print axioms sectionAlgHom_algHomSection
#print axioms affineSectionsEquiv
#print axioms schemeSectionsEquiv
#print axioms moduleFinite_globalSections
#print axioms finiteAlgHomFintype
#print axioms sectionAlgHomFintype
#print axioms sectionsFintype
#print axioms schemeSectionsFintype
#print axioms S1803Model_hom_eq
#print axioms S1803_sectionFintype
#print axioms S1803_firstMissing_sections

end LeanFormal.IUT.XiFPaper.S1803AffineSectionsActual
