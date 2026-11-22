/-
Probe 1: transport PreGalois/Galois/fiber/EssSmall across an equivalence.
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.EssentiallySmall

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.defProp false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace S1778Probe1

universe u₁ u₂ v w

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]

/-- G3 transport. -/
theorem monoInducesIsoOnDirectSummand_of_equivalence
    [PreGaloisCategory D] (E : C ⥤ D) [E.IsEquivalence]
    {X Y : C} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  haveI hpm : PreservesMonomorphisms E :=
    preservesMonomorphisms_of_adjunction E.asEquivalence.symm.toAdjunction
  haveI : Mono (E.map i) := hpm.preserves i
  obtain ⟨Z', u', ⟨hc'⟩⟩ :=
    PreGaloisCategory.monoInducesIsoOnDirectSummand (C := D) (i := E.map i)
  let e := E.asEquivalence
  let Z : C := e.inverse.obj Z'
  let α : E.obj Z ≅ Z' := e.counitIso.app Z'
  let u : Z ⟶ Y := E.preimage (α.hom ≫ u')
  have hu : E.map u = α.hom ≫ u' := E.map_preimage _
  let desc : ∀ {T : C}, (X ⟶ T) → (Z ⟶ T) → (E.obj Y ⟶ E.obj T) :=
    fun {T} a b => hc'.desc (BinaryCofan.mk (E.map a) (α.inv ≫ E.map b))
  refine ⟨Z, u, ⟨?_⟩⟩
  refine BinaryCofan.IsColimit.mk (BinaryCofan.mk i u) (fun {T} a b => E.preimage (desc a b)) ?_ ?_ ?_
  · intro T a b
    apply E.map_injective
    rw [E.map_comp, E.map_preimage]
    exact hc'.fac (BinaryCofan.mk (E.map a) (α.inv ≫ E.map b)) ⟨WalkingPair.left⟩
  · intro T a b
    apply E.map_injective
    rw [E.map_comp]
    change E.map u ≫ E.map (E.preimage (desc a b)) = E.map b
    have hmap : E.map (E.preimage (desc a b)) = desc a b := E.map_preimage _
    rw [hmap, hu, Category.assoc]
    have hfr : u' ≫ desc a b = α.inv ≫ E.map b :=
      hc'.fac (BinaryCofan.mk (E.map a) (α.inv ≫ E.map b)) ⟨WalkingPair.right⟩
    rw [hfr]
    simp
  · intro T a b m hm1 hm2
    let m' : Y ⟶ T := m
    show m' = E.preimage (desc a b)
    have hm1' : i ≫ m' = a := by simpa using hm1
    have hm2' : u ≫ m' = b := by simpa using hm2
    apply E.map_injective
    have hm1'' : E.map i ≫ E.map m' = E.map a := by rw [← E.map_comp, hm1']
    have hm2'' : u' ≫ E.map m' = α.inv ≫ E.map b := by
      have h : E.map u ≫ E.map m' = E.map b := by rw [← E.map_comp, hm2']
      rw [hu] at h
      calc u' ≫ E.map m'
          = α.inv ≫ α.hom ≫ u' ≫ E.map m' := by simp
        _ = α.inv ≫ ((α.hom ≫ u') ≫ E.map m') := by simp only [Category.assoc]
        _ = α.inv ≫ E.map b := congrArg (fun t => α.inv ≫ t) h
    have hmfac : ∀ j : Discrete WalkingPair,
        (BinaryCofan.mk (E.map i) u').ι.app j ≫ E.map m' =
          (BinaryCofan.mk (E.map a) (α.inv ≫ E.map b)).ι.app j := by
      rintro ⟨j⟩
      cases j with
      | left => simpa using hm1''
      | right => simpa using hm2''
    have huniq := hc'.uniq (BinaryCofan.mk (E.map a) (α.inv ≫ E.map b)) (E.map m') hmfac
    rw [huniq, E.map_preimage]

/-- PreGaloisCategory transport. -/
theorem preGaloisCategory_of_equivalence
    [PreGaloisCategory D] (E : C ⥤ D) [E.IsEquivalence] : PreGaloisCategory C where
  hasTerminal := CategoryTheory.hasTerminal_of_equivalence E
  hasPullbacks := CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence E
  hasFiniteCoproducts := ⟨fun n => CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence E⟩
  hasQuotientsByFiniteGroups := fun G _ _ => CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence E
  monoInducesIsoOnDirectSummand := fun i _ => monoInducesIsoOnDirectSummand_of_equivalence E i

/-- Fiber functor transport. -/
theorem fiberFunctor_of_equivalence
    [PreGaloisCategory D] (E : C ⥤ D) [E.IsEquivalence] (P : PreGaloisCategory C)
    (G : D ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor G] :
    @PreGaloisCategory.FiberFunctor C _ P (E ⋙ G) where
  preservesTerminalObjects := by
    letI := P
    infer_instance
  preservesPullbacks := by
    letI := P
    infer_instance
  preservesFiniteCoproducts := by
    letI := P
    infer_instance
  preservesEpis := by
    letI := P
    infer_instance
  preservesQuotientsByFiniteGroups := by
    letI := P
    intro G' _ _
    infer_instance
  reflectsIsos := by
    letI := P
    infer_instance

/-- GaloisCategory transport. -/
theorem galoisCategory_of_equivalence
    [GaloisCategory D] (E : C ⥤ D) [E.IsEquivalence] : GaloisCategory C := by
  let P : PreGaloisCategory C := preGaloisCategory_of_equivalence E
  letI := P
  obtain ⟨G, ⟨hG⟩⟩ := GaloisCategory.hasFiberFunctor (C := D)
  exact
    { toPreGaloisCategory := P
      hasFiberFunctor := ⟨E ⋙ G, ⟨fiberFunctor_of_equivalence E P G⟩⟩ }

/-- EssentiallySmall transport. -/
theorem essentiallySmall_of_equivalence
    (e : C ≌ D) [EssentiallySmall.{0} D] : EssentiallySmall.{0} C :=
  (essentiallySmall_congr e).mpr inferInstance

end S1778Probe1