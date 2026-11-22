/- PORTED DONOR FILE (grace): tmp/vendor_clone_belyi/Belyi/Dimension.lean + Belyi/Ramification.lean (LANA project, Apache-2.0).
   Changes only: namespace -> LeanFormal.IUT.XiFPaper.BelyiRamification; imports rewritten to Mathlib
   (the donor's `import Belyi.Dimension` is inlined below). No mathematical content change.
   Route use: branch(phi) subset {0,1,infty} for B1; ramification divisor argument for B3 (route L334). -/
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.Tactic

universe u

namespace LeanFormal.IUT.XiFPaper.BelyiRamification

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X : Scheme.{u}}

/-- In a scheme, a strict two-step specialization chain `x ⤳ y ⤳ z` forces the stalk
at `z` to have Krull dimension at least `2`; contrapositively, if the stalk at `z` has
dimension `≤ 1` and `x ⤳ y ⤳ z` with `x ≠ y`, then `y = z`. -/
lemma eq_of_specializes_of_specializes {x y z : X}
    (hdim : Ring.KrullDimLE 1 (X.presheaf.stalk z))
    (hxy : x ⤳ y) (hyz : y ⤳ z) (hne : x ≠ y) : y = z := by
  by_contra hne'
  obtain ⟨p, hp⟩ : x ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hxy.trans hyz
  obtain ⟨q, hq⟩ : y ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hyz
  have hemb : Topology.IsEmbedding (X.fromSpecStalk z).base :=
    (Scheme.Hom.isEmbedding _)
  have hzq : X.fromSpecStalk z (IsLocalRing.closedPoint _) = z :=
    Scheme.fromSpecStalk_closedPoint
  let p' : PrimeSpectrum (X.presheaf.stalk z) := p
  let q' : PrimeSpectrum (X.presheaf.stalk z) := q
  let c' : PrimeSpectrum (X.presheaf.stalk z) := IsLocalRing.closedPoint _
  have hpq : p' < q' := by
    refine lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).mpr ?_) fun h => hne ?_
    · exact hemb.toIsInducing.specializes_iff.mp (by rw [hp, hq]; exact hxy)
    · rw [← hp, ← hq]
      exact congrArg (X.fromSpecStalk z) h
  have hqc : q' < c' := by
    refine lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).mpr ?_) fun h => hne' ?_
    · exact hemb.toIsInducing.specializes_iff.mp (by rw [hq, hzq]; exact hyz)
    · calc y = (X.fromSpecStalk z) q := hq.symm
        _ = (X.fromSpecStalk z) (IsLocalRing.closedPoint _) := congrArg _ h
        _ = z := hzq
  rcases Order.krullDim_le_one_iff.mp hdim.krullDim_le q' with h | h
  · exact h.not_lt hpq
  · exact h.not_lt hqc

/-- On an irreducible scheme with one-dimensional stalks, every non-generic point is
closed. -/
lemma isClosed_singleton_of_ne_genericPoint [IrreducibleSpace X]
    (hdim : ∀ z : X, Ring.KrullDimLE 1 (X.presheaf.stalk z)) {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  have h : closure {x} = {x} := by
    refine subset_antisymm (fun z hz => ?_) subset_closure
    have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hz
    have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    exact (eq_of_specializes_of_specializes (hdim z) hgx hxz (Ne.symm hx)) ▸ rfl
  rw [← h]
  exact isClosed_closure

/-- A Noetherian quasi-sober T1 space is finite: its finitely many irreducible
components are singletons and cover it. -/
lemma finite_of_t1Space {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    [QuasiSober α] [T1Space α] : Finite α := by
  have hsing : ∀ x : α, irreducibleComponent x = {x} := by
    intro x
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober (S := irreducibleComponent x)
      isIrreducible_irreducibleComponent isClosed_irreducibleComponent
    have h : irreducibleComponent x = {ξ} := by
      rw [← hξ.def, closure_singleton]
    have hx : x ∈ irreducibleComponent x := mem_irreducibleComponent
    rw [h] at hx ⊢
    rw [Set.mem_singleton_iff.mp hx]
  have : Finite (irreducibleComponents α) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  refine Finite.of_injective
    (fun x : α => (⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ :
      irreducibleComponents α)) fun a b hab => ?_
  have h : irreducibleComponent a = irreducibleComponent b := congrArg Subtype.val hab
  rw [hsing a, hsing b] at h
  exact Set.singleton_eq_singleton_iff.mp h

/-- On an irreducible Noetherian scheme with one-dimensional stalks, a closed subset
avoiding the generic point is finite. -/
lemma finite_of_isClosed_of_genericPoint_notMem [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : ∀ z : X, Ring.KrullDimLE 1 (X.presheaf.stalk z)) {Z : Set X}
    (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by
  have hQS : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hT1 : T1Space Z := by
    refine ⟨fun z => ?_⟩
    have hcl : IsClosed ({(z : X)} : Set X) :=
      isClosed_singleton_of_ne_genericPoint hdim fun h => hη (h ▸ z.2)
    have h : (Subtype.val ⁻¹' {(z : X)} : Set Z) = {z} := by
      ext w
      simp [Subtype.ext_iff]
    exact h ▸ hcl.preimage continuous_subtype_val
  rw [← Set.finite_coe_iff]
  exact finite_of_t1Space

/-- Fibers of a closed, non-constant morphism out of an irreducible Noetherian scheme
with one-dimensional stalks are finite. Non-constancy is expressed as: the image of
the generic point is not a closed point. -/
lemma finite_preimage_singleton_of_isClosedMap {Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : ∀ z : X, Ring.KrullDimLE 1 (X.presheaf.stalk z))
    (hf : IsClosedMap f.base) (hnc : ¬ IsClosed ({f (genericPoint X)} : Set Y)) (y : Y) :
    (f.base ⁻¹' {y}).Finite := by
  by_cases hy : genericPoint X ∈ f.base ⁻¹' {y}
  · -- the fiber through the generic point is just the generic point
    have h : f.base ⁻¹' {y} = {genericPoint X} := by
      refine subset_antisymm (fun x hx => ?_) (by simpa using hy)
      by_contra hne
      have h1 : IsClosed ({x} : Set X) :=
        isClosed_singleton_of_ne_genericPoint hdim (by simpa using hne)
      have h2 : IsClosed ({y} : Set Y) := by
        have := hf _ h1
        rwa [Set.image_singleton, show f.base x = y from hx] at this
      exact hnc (by rwa [show f (genericPoint X) = y from hy])
    rw [h]
    exact Set.finite_singleton _
  · rcases Set.eq_empty_or_nonempty (f.base ⁻¹' {y}) with h | ⟨x, hx⟩
    · simp [h]
    have hxne : x ≠ genericPoint X := fun h => hy (h ▸ hx)
    have h1 : IsClosed ({x} : Set X) := isClosed_singleton_of_ne_genericPoint hdim hxne
    have h2 : IsClosed ({y} : Set Y) := by
      have := hf _ h1
      rwa [Set.image_singleton, show f.base x = y from hx] at this
    exact finite_of_isClosed_of_genericPoint_notMem hdim
      (h2.preimage f.base.hom.continuous) hy

/-- A scheme quasi-compact and locally of finite type over a Noetherian quasi-compact
scheme (e.g. proper over the spectrum of a field) is Noetherian; in particular its
underlying space is a Noetherian topological space (`IsNoetherian.noetherianSpace`). -/
lemma isNoetherian_of_over (X S : Scheme.{u}) [X.Over S] [IsLocallyNoetherian S]
    [CompactSpace S] [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)] :
    IsNoetherian X where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ S)

end LeanFormal.IUT.XiFPaper.BelyiRamification


namespace LeanFormal.IUT.XiFPaper.BelyiRamification

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X Y Z : Scheme.{u}}

section Defs

variable (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- The **ramification locus** of a morphism: the complement of its smooth locus, i.e.
the set of points where the stalk map fails to be formally smooth. For a morphism of
relative dimension `0` (e.g. a finite morphism of curves) this is the complement of the
étale locus. -/
def Ram : Set X := (f.smoothLocus : Set X)ᶜ

/-- The **branch locus** of a morphism: the image of its ramification locus. -/
def Branch : Set Y := f '' Ram f

lemma mem_ram_iff {x : X} : x ∈ Ram f ↔ ¬ (f.stalkMap x).hom.FormallySmooth := Iff.rfl

lemma mem_branch_iff {y : Y} : y ∈ Branch f ↔ ∃ x ∈ Ram f, f x = y := by
  simp [Branch, Set.mem_image]

/-- The ramification locus is closed. -/
lemma isClosed_ram : IsClosed (Ram f) :=
  f.smoothLocus.2.isClosed_compl

/-- A morphism is smooth exactly when it is unramified everywhere. -/
lemma ram_eq_empty_iff : Ram f = ∅ ↔ Smooth f := by
  rw [Ram, Set.compl_empty_iff, ← Scheme.Hom.smoothLocus_eq_top_iff (f := f)]
  exact ⟨fun h => TopologicalSpace.Opens.ext (by simpa using h),
    fun h => by rw [h]; simp⟩

/-- For a morphism of relative dimension `0`, the ramification locus is empty exactly
when the morphism is étale. -/
lemma ram_eq_empty_iff_etale [SmoothOfRelativeDimension 0 f] :
    Ram f = ∅ ↔ Etale f := by
  rw [ram_eq_empty_iff, Etale.iff_smoothOfRelativeDimension_zero]
  exact ⟨fun _ => inferInstance, fun _ => SmoothOfRelativeDimension.smooth 0 f⟩

lemma branch_eq_empty_iff_ram_eq_empty : Branch f = ∅ ↔ Ram f = ∅ := by
  simp [Branch, Set.image_eq_empty]

end Defs

section Etale

variable (f : X ⟶ Y)

@[simp]
lemma ram_eq_empty_of_etale [LocallyOfFinitePresentation f] [Etale f] : Ram f = ∅ :=
  (ram_eq_empty_iff f).mpr inferInstance

@[simp]
lemma branch_eq_empty_of_etale [LocallyOfFinitePresentation f] [Etale f] :
    Branch f = ∅ :=
  (branch_eq_empty_iff_ram_eq_empty f).mpr (ram_eq_empty_of_etale f)

@[simp]
lemma ram_eq_empty_of_isIso [IsIso f] : Ram f = ∅ := by
  have : IsOpenImmersion f := inferInstance
  exact ram_eq_empty_of_etale f

@[simp]
lemma branch_eq_empty_of_isIso [IsIso f] : Branch f = ∅ := by
  have : IsOpenImmersion f := inferInstance
  exact branch_eq_empty_of_etale f

end Etale

section Comp

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A point is unramified for a composite as soon as it is unramified for the first map
and its image is unramified for the second: the ramification locus of `f ≫ g` is
contained in `Ram f ∪ f⁻¹(Ram g)`. -/
lemma ram_comp_subset [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    [LocallyOfFinitePresentation (f ≫ g)] :
    Ram (f ≫ g) ⊆ Ram f ∪ f ⁻¹' Ram g := by
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or, Set.mem_preimage] at hcon
  obtain ⟨hf, hg⟩ := hcon
  refine hx ?_
  rw [mem_ram_iff, not_not] at hf hg
  change x ∈ (f ≫ g).smoothLocus
  rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.stalkMap_comp]
  exact hg.comp hf

/-- **B2a**: the branch locus of a composite is contained in the image of the branch
locus of the first map together with the branch locus of the second. -/
theorem branch_comp_subset [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    [LocallyOfFinitePresentation (f ≫ g)] :
    Branch (f ≫ g) ⊆ g '' Branch f ∪ Branch g := by
  rintro z ⟨x, hx, rfl⟩
  rcases ram_comp_subset f g hx with h | h
  · exact Or.inl ⟨f x, ⟨x, h, rfl⟩, rfl⟩
  · exact Or.inr ⟨f x, h, rfl⟩

end Comp

section Finite

variable (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- **Finiteness of the ramification locus.** On an irreducible Noetherian scheme whose
local rings have Krull dimension `≤ 1` (e.g. a curve, by issue #75), a morphism that is
smooth at the generic point ramifies only at finitely many points: `Ram f` is a closed
set avoiding the generic point.

For a finite morphism of curves in characteristic zero the hypothesis `hgen` holds
because the function-field extension is separable (generic étaleness). -/
theorem finite_ram [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (hgen : genericPoint X ∈ f.smoothLocus) : (Ram f).Finite :=
  finite_of_isClosed_of_genericPoint_notMem hdim (isClosed_ram f) (by simpa [Ram] using hgen)

/-- The branch locus of a generically smooth morphism as above is finite. -/
theorem finite_branch [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (hgen : genericPoint X ∈ f.smoothLocus) : (Branch f).Finite :=
  (finite_ram f hdim hgen).image f

/-- Over a perfect base field (e.g. in characteristic zero), a morphism from an integral
scheme is automatically smooth at the generic point, so the ramification locus of a
morphism of such schemes over the field is finite as soon as the source has
one-dimensional stalks. -/
theorem finite_ram_of_perfectField {k : Type u} [Field k] [PerfectField k] [IsIntegral X]
    [NoetherianSpace X] (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (g : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation g] : (Ram g).Finite :=
  finite_ram g hdim g.genericPoint_mem_smoothLocus_of_perfectField

end Finite

section GenericEtale

/-- For a **dominant** morphism of integral schemes, the generic point of the source maps
to the generic point of the target. -/
lemma image_genericPoint_eq_of_isDominant (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image (f := ⇑f) f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec Y)

/-- **Generic étaleness.** A dominant morphism of integral schemes that is locally of
finite presentation is smooth at the generic point of the source, provided the function
field of the target is perfect (e.g. in characteristic zero). Indeed the stalk map at the
generic point is the extension of function fields `K(Y) → K(X)`, an essentially finite type
extension of a perfect field, hence formally smooth.

This discharges the `hgen` hypothesis of `finite_ram`/`finite_branch` for a dominant
finite morphism of curves in characteristic zero — in particular for the finite surjective
morphism `X ⟶ ℙ¹` produced by B1. -/
theorem genericPoint_mem_smoothLocus (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [LocallyOfFinitePresentation f] [PerfectField Y.functionField] :
    genericPoint X ∈ f.smoothLocus := by
  have hgen : f (genericPoint X) = genericPoint Y := image_genericPoint_eq_of_isDominant f
  have hess := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  -- the source stalk is the function field of `Y` (a perfect field), via `f genX = genY`
  let ee : Y.presheaf.stalk (f (genericPoint X)) ≃+* Y.functionField :=
    (Y.presheaf.stalkCongr (.of_eq hgen)).commRingCatIsoToRingEquiv
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) :=
    (ee.isField (Field.toIsField Y.functionField)).toField
  letI : PerfectField (Y.presheaf.stalk (f (genericPoint X))) :=
    PerfectField.of_ringEquiv ee.symm
  algebraize [(f.stalkMap (genericPoint X)).hom]
  exact Algebra.FormallySmooth.of_perfectField

/-- The ramification locus of a dominant, locally-of-finite-presentation morphism of
integral schemes is finite, provided the source has one-dimensional stalks and the target
function field is perfect (e.g. a dominant finite morphism of curves in characteristic
zero). -/
theorem finite_ram_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace X] [IsDominant f] [LocallyOfFinitePresentation f]
    [PerfectField Y.functionField]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) : (Ram f).Finite :=
  finite_ram f hdim (genericPoint_mem_smoothLocus f)

/-- The branch locus of such a morphism is finite. -/
theorem finite_branch_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace X] [IsDominant f] [LocallyOfFinitePresentation f]
    [PerfectField Y.functionField]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) : (Branch f).Finite :=
  finite_branch f hdim (genericPoint_mem_smoothLocus f)

end GenericEtale

section Restrict

/-- Composing with an open immersion on the target does not change the smooth locus. -/
lemma smoothLocus_comp_of_isOpenImmersion (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (f ≫ g)] :
    (f ≫ g).smoothLocus = f.smoothLocus := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change x ∈ (f ≫ g).smoothLocus ↔ x ∈ f.smoothLocus
  rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.mem_smoothLocus, Scheme.Hom.stalkMap_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (g.stalkMap (f x)) (f.stalkMap x)

/-- A morphism is smooth over any open subset of the target above which it is
unramified. -/
lemma smooth_morphismRestrict (f : X ⟶ Y) [LocallyOfFinitePresentation f] (U : Y.Opens)
    [LocallyOfFinitePresentation (f ∣_ U)] (h : (f ⁻¹ᵁ U : Set X) ⊆ (f.smoothLocus : Set X)) :
    Smooth (f ∣_ U) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  have h1 : ((f ∣_ U) ≫ U.ι).smoothLocus = (f ∣_ U).smoothLocus :=
    smoothLocus_comp_of_isOpenImmersion _ _
  have h2 : ((f ⁻¹ᵁ U).ι ≫ f).smoothLocus = (f ⁻¹ᵁ U).ι ⁻¹ᵁ f.smoothLocus :=
    (Scheme.Hom.preimage_smoothLocus_eq _ _).symm
  have h3 : ((f ∣_ U) ≫ U.ι).smoothLocus = ((f ⁻¹ᵁ U).ι ≫ f).smoothLocus := by
    congr 1
    exact morphismRestrict_ι f U
  have h4 : (f ⁻¹ᵁ U).ι ⁻¹ᵁ f.smoothLocus = ⊤ :=
    TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => h x.2)
  rw [← h1, h3, h2, h4]

/-- **B2c**: a morphism is smooth over any open subset of the target avoiding its branch
locus. For a morphism of relative dimension `0` (e.g. a finite morphism of curves) this
says it is étale there. -/
theorem smooth_morphismRestrict_of_disjoint_branch (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (U : Y.Opens)
    [LocallyOfFinitePresentation (f ∣_ U)] (h : Disjoint (U : Set Y) (Branch f)) :
    Smooth (f ∣_ U) := by
  refine smooth_morphismRestrict f U fun x hx => ?_
  by_contra hxs
  exact Set.disjoint_left.mp h hx ⟨x, hxs, rfl⟩

end Restrict

section IsoCancel

variable (f : X ⟶ Y)

/-- Precomposing with an isomorphism pulls the ramification locus back along it. -/
lemma ram_isIso_comp (e : Z ⟶ X) [IsIso e] [LocallyOfFinitePresentation f] :
    Ram (e ≫ f) = e ⁻¹' Ram f := by
  rw [Ram, Ram, ← Scheme.Hom.preimage_smoothLocus_eq e f, Scheme.Hom.coe_preimage,
    Set.preimage_compl]

/-- Precomposing with an isomorphism leaves the branch locus unchanged. -/
lemma branch_isIso_comp (e : Z ⟶ X) [IsIso e] [LocallyOfFinitePresentation f] :
    Branch (e ≫ f) = Branch f := by
  have hsurj : Function.Surjective ⇑e := (Scheme.homeoOfIso (asIso e)).surjective
  rw [Branch, Branch, ram_isIso_comp f e, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.image_comp, Set.image_preimage_eq _ hsurj]

/-- Postcomposing with an isomorphism leaves the ramification locus unchanged. -/
lemma ram_comp_isIso (e : Y ⟶ Z) [IsIso e] [LocallyOfFinitePresentation f] :
    Ram (f ≫ e) = Ram f := by
  have : IsOpenImmersion e := inferInstance
  rw [Ram, Ram, smoothLocus_comp_of_isOpenImmersion f e]

/-- Postcomposing with an isomorphism pushes the branch locus forward along it. -/
lemma branch_comp_isIso (e : Y ⟶ Z) [IsIso e] [LocallyOfFinitePresentation f] :
    Branch (f ≫ e) = e '' Branch f := by
  rw [Branch, Branch, ram_comp_isIso f e, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.image_comp]

end IsoCancel

end LeanFormal.IUT.XiFPaper.BelyiRamification

#print axioms LeanFormal.IUT.XiFPaper.BelyiRamification.branch_comp_subset
#print axioms LeanFormal.IUT.XiFPaper.BelyiRamification.ram_comp_subset
#print axioms LeanFormal.IUT.XiFPaper.BelyiRamification.finite_ram
#print axioms LeanFormal.IUT.XiFPaper.BelyiRamification.finite_branch
#print axioms LeanFormal.IUT.XiFPaper.BelyiRamification.ram_eq_empty_iff_etale
#print axioms LeanFormal.IUT.XiFPaper.BelyiRamification.isClosed_ram