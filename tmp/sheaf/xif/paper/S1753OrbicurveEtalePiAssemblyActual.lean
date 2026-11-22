import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S1743CoverSliceActual
import tmp.sheaf.xif.paper.S1749FiniteEtaleGaloisAssemblyActual
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

/-!
# S1753: transport of the finite-etale-algebra Galois category to the actual
orbicurve cover type, and the exact missing input

## Context

S1728 gives the actual finite-etale cover type

  S1728Cover = Iut.OrbicurveFiniteEtaleCover S1726Orbicurve  (Type 1),

with a genuine 2-isomorphism-quotient category at the corrected universe
(`S1728ActualCategory11 : Category.{1,1}`).  The target structure
`Iut.OrbicurveEtaleFundamentalGroup` asks for

  coverCategory : Category.{0,1} S1728Cover,
  galoisCategory : GaloisCategory S1728Cover,
  fiber : S1728Cover ⥤ FintypeCat.{0},
  fiberFunctor : PreGaloisCategory.FiberFunctor fiber,

i.e. the four categorical fields studied in this file.

S1749 assembles `GaloisCategory (FiniteEtaleAlg K)` for a field `K`, but only
conditionally on five fields (pullbacks, finite coproducts, finite-group
quotients, the mono/direct-summand axiom, and the geometric fibre functor).
S1743 constructs the object map from actual covers to the affine finite-etale
slice, but explicitly does *not* construct the comparison equivalence.
S1750 has no actual file in this tree; the only S1750 material is a probe
comparing finite-etale algebras over the affine curve coordinate ring with
finite-etale algebras over its function field, not a comparison with
`OrbicurveFiniteEtaleCover`.

## What this file proves

1.  **Transport across an equivalence.**  If `E : C ≌ D` is an equivalence of
    categories and `D` is a Galois category, then `C` is a Galois category.
    The proof constructs the five pre-Galois fields and the fibre functor
    explicitly; the mono/direct-summand field is transported by decomposing
    `E.functor.map i` in `D`, pulling the colimit back along `E.inverse`,
    and cancelling the unit and counit isomorphisms.  This is genuine
    transport, not an assumption.

2.  **Fibre functor transport.**  If `F : D ⥤ FintypeCat` is a fibre functor on
    `D`, then `E.functor ⋙ F` is a fibre functor on `C`.

3.  **Conditional assembly of the four target fields.**  Given the equivalence
    `C ≌ FiniteEtaleAlg K`, a Galois-category structure on `FiniteEtaleAlg K`
    and its fibre functor, the four target fields follow.  The assembly is a
    real construction from those inputs.

4.  **Exact missing statements.**  The equivalence, the S1749 five fields, and
    the S1743 slice comparison are recorded as explicit propositions.  None is
    inhabited here; in particular no equivalence and no group are postulated.

## Honest boundary

The target `Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve G` is not
constructed.  The first missing input of the finite-etale-algebra route is
`S1753CoverAlgEquivalence`; the second is `S1753FiniteEtaleGaloisFields`.
The S1743 route supplies only an object map and a missing comparison.  No
`sorry`, axiom, Shrink, ULift or PUnit is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual

open CategoryTheory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual

/-! ## 1. Transport of a Galois category across an equivalence -/

section Transport

universe u v

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable (E : C ≌ D) [PreGaloisCategory D]

/-- The triangle identity for the unit and counit of an equivalence, in the
form needed for the mono/direct-summand transport: the image under the functor
of the inverse unit component is the counit component. -/
theorem S1753UnitTriangle (X : C) :
    E.functor.map (E.unitIso.inv.app X) =
      E.counitIso.hom.app (E.functor.obj X) := by
  have h := E.counitIso_functor_comp X
  have h2 : E.functor.map (E.unitIso.inv.app X) =
      inv (E.counitIso.inv.app (E.functor.obj X)) :=
    IsIso.eq_inv_of_hom_inv_id h
  simpa using h2

/-- A component of the transported mono decomposition: the right leg in the
target category. -/
theorem S1753TransportRightLeg (Z : D) (Y : C) (u : Z ⟶ E.functor.obj Y) :
    E.functor.map (E.inverse.map u ≫ E.unitIso.inv.app Y) =
      E.counitIso.hom.app Z ≫ u := by
  rw [Functor.map_comp]
  rw [show E.functor.map (E.unitIso.inv.app Y) =
      E.counitIso.hom.app (E.functor.obj Y) from S1753UnitTriangle E Y]
  simpa only [Functor.id_map, Functor.comp_map] using E.counitIso.hom.naturality u

/-- Transport of the pre-Galois structure across an equivalence. -/
@[reducible]
noncomputable def S1753PreGaloisCategory : PreGaloisCategory C where
  hasTerminal := (Equivalence.hasTerminal_iff E).2 inferInstance
  hasPullbacks := Adjunction.hasLimitsOfShape_of_equivalence (J := WalkingCospan) E.functor
  hasFiniteCoproducts :=
    ⟨fun n => Adjunction.hasColimitsOfShape_of_equivalence (J := Discrete (Fin n)) E.functor⟩
  hasQuotientsByFiniteGroups :=
    fun G _ _ => Adjunction.hasColimitsOfShape_of_equivalence (J := SingleObj G) E.functor
  monoInducesIsoOnDirectSummand := by
    intro X Y i _
    haveI : Mono (E.functor.map i) := inferInstance
    obtain ⟨Z, u, ⟨hc⟩⟩ :=
      PreGaloisCategory.monoInducesIsoOnDirectSummand (C := D) (E.functor.map i)
    let u' : E.inverse.obj Z ⟶ Y := E.inverse.map u ≫ E.unitIso.inv.app Y
    refine ⟨E.inverse.obj Z, u', ⟨?_⟩⟩
    let cC : BinaryCofan X (E.inverse.obj Z) := BinaryCofan.mk i u'
    apply isColimitOfReflects E.functor
    let cMap : Cocone (pair X (E.inverse.obj Z) ⋙ E.functor) := E.functor.mapCocone cC
    let gammaIso : (pair X (E.inverse.obj Z) ⋙ E.functor) ≅
        pair (E.functor.obj X) Z :=
      mapPairIso (Iso.refl (E.functor.obj X)) (E.counitIso.app Z)
    let cD'' : Cocone (pair X (E.inverse.obj Z) ⋙ E.functor) :=
      (Cocone.precompose gammaIso.hom).obj (BinaryCofan.mk (E.functor.map i) u)
    have hcD'' : IsColimit cD'' :=
      (IsColimit.precomposeHomEquiv gammaIso (BinaryCofan.mk (E.functor.map i) u)).symm hc
    have hright : E.functor.map u' = E.counitIso.hom.app Z ≫ u :=
      S1753TransportRightLeg E Z Y u
    refine hcD''.ofIsoColimit (Cocone.ext (Iso.refl _) ?_)
    intro j
    rcases j with ⟨⟨⟩⟩
    · simp only [cD'', cMap, cC, gammaIso, Iso.refl_hom, Category.comp_id,
        Functor.mapCocone_ι_app, Cocone.precompose_obj_ι, NatTrans.comp_app,
        mapPairIso_hom_app, BinaryCofan.mk]
      exact Category.id_comp _
    · simp only [cD'', cMap, cC, gammaIso, Iso.refl_hom, Category.comp_id,
        Functor.mapCocone_ι_app, Cocone.precompose_obj_ι, NatTrans.comp_app,
        mapPairIso_hom_app, Category.id_comp, BinaryCofan.mk, hright]
      rfl

/-- Transport of a fibre functor across an equivalence. -/
theorem S1753FiberFunctorTransport
    (F : D ⥤ FintypeCat.{v}) [PreGaloisCategory.FiberFunctor F] :
    @PreGaloisCategory.FiberFunctor C _
      (S1753PreGaloisCategory E) (E.functor ⋙ F) := by
  letI : PreGaloisCategory C := S1753PreGaloisCategory E
  exact
    { preservesTerminalObjects := inferInstance
      preservesPullbacks := inferInstance
      preservesFiniteCoproducts := inferInstance
      preservesEpis := inferInstance
      preservesQuotientsByFiniteGroups := fun G _ _ => inferInstance
      reflectsIsos := inferInstance }

/-- Transport of a Galois-category structure with a prescribed fibre functor:
the fibre functor of the transported Galois category is exactly
`E.functor ⋙ F`. -/
@[reducible]
noncomputable def S1753GaloisCategoryOfFiber
    (F : D ⥤ FintypeCat.{v}) [PreGaloisCategory.FiberFunctor F] :
    GaloisCategory C := by
  letI : PreGaloisCategory C := S1753PreGaloisCategory E
  exact GaloisCategory.mk ⟨E.functor ⋙ F, ⟨S1753FiberFunctorTransport E F⟩⟩

/-- Transport of the Galois-category structure across an equivalence.

The fibre functor required by `GaloisCategory` is the image under `E` of the
fibre functor chosen by `GaloisCategory.getFiberFunctor D`; it is a genuine
fibre functor by `S1753FiberFunctorTransport`. -/
@[reducible]
noncomputable def S1753GaloisCategory [GaloisCategory D] : GaloisCategory C :=
  S1753GaloisCategoryOfFiber E (PreGaloisCategory.GaloisCategory.getFiberFunctor D)

end Transport

/-! ## 2. The specific cover and finite-etale-algebra categories -/

/-- The base field of the S1726 D6 orbicurve. -/
abbrev S1753K : Type := S1726K

/-- The actual finite-etale cover type of the S1726 orbicurve. -/
abbrev S1753Cover : Type 1 := S1728Cover

/-- The opposite of the category of finite-etale `S1753K`-algebras. -/
abbrev S1753Alg : Type 1 :=
  S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg S1753K

/-- The Mathlib affine finite-etale slice over the S1726 base. -/
abbrev S1753Slice : Type 1 := S1733Slice

/-- The four target fields of `Iut.OrbicurveEtaleFundamentalGroup`, mirrored
with the same dependent types. -/
structure S1753TargetFields where
  /-- The target's `coverCategory` field: a genuine `Category.{0,1}` on the
  actual cover type. -/
  coverCategory : Category.{0, 1} S1753Cover
  /-- The target's `galoisCategory` field. -/
  galoisCategory :
    letI := coverCategory
    @GaloisCategory S1753Cover coverCategory
  /-- The target's `fiber` field. -/
  fiber :
    letI := coverCategory
    S1753Cover ⥤ FintypeCat.{0}
  /-- The target's `fiberFunctor` field. -/
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber

/-- Every actual `OrbicurveEtaleFundamentalGroup` for the S1726 orbicurve
supplies the four fields above, with literally the same types.  This is the
machine-checked statement that `S1753TargetFields` is not a lookalike. -/
noncomputable def S1753TargetFields.ofOrbicurveEtaleFundamentalGroup
    {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve G) :
    S1753TargetFields where
  coverCategory := D.coverCategory
  galoisCategory := D.galoisCategory
  fiber := D.fiber
  fiberFunctor := D.fiberFunctor

/-! ## 3. The finite-etale-algebra route -/

/-- Data for the finite-etale-algebra route to the target fields: a
`Category.{0,1}` on the actual cover type, an equivalence to
`FiniteEtaleAlg K`, a Galois category on the algebra side, and its fibre
functor. -/
structure S1753FiniteEtaleRoute where
  /-- The actual cover category at the target universe. -/
  coverCategory : Category.{0, 1} S1753Cover
  /-- Its hom types are the actual cover maps (the target's
  `coverMorphism_bijective` content). -/
  coverHomEquiv : ∀ A B,
    @Quiver.Hom _ coverCategory.toQuiver A B ≃ S1728CoverMap A B
  /-- The comparison equivalence to finite-etale algebras. -/
  equivalence : @CategoryTheory.Equivalence S1753Cover S1753Alg
    coverCategory (S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.category (K := S1753K))
  /-- The pre-Galois category on finite-etale algebras (conditional in S1749). -/
  preGaloisCategoryAlg : PreGaloisCategory S1753Alg
  /-- The geometric fibre functor on finite-etale algebras. -/
  fiberAlg : S1753Alg ⥤ FintypeCat.{0}
  /-- The fibre-functor structure on `fiberAlg`. -/
  fiberFunctorAlg : @PreGaloisCategory.FiberFunctor S1753Alg
    (S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.category (K := S1753K))
    preGaloisCategoryAlg fiberAlg

/-- Assembly of the four target fields from the finite-etale-algebra route.
This is genuine transport: the cover Galois category and fibre functor are
constructed by `S1753GaloisCategory` and `S1753FiberFunctorTransport`. -/
noncomputable def S1753TargetFields.ofFiniteEtaleRoute
    (R : S1753FiniteEtaleRoute) : S1753TargetFields := by
  letI : Category.{0, 1} S1753Cover := R.coverCategory
  letI : Category.{0, 1} S1753Alg :=
    S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.category (K := S1753K)
  letI : PreGaloisCategory S1753Alg := R.preGaloisCategoryAlg
  letI : PreGaloisCategory.FiberFunctor R.fiberAlg := R.fiberFunctorAlg
  letI : GaloisCategory S1753Alg :=
    GaloisCategory.mk ⟨R.fiberAlg, ⟨R.fiberFunctorAlg⟩⟩
  letI : GaloisCategory S1753Cover :=
    S1753GaloisCategoryOfFiber R.equivalence R.fiberAlg
  exact
    { coverCategory := R.coverCategory
      galoisCategory := S1753GaloisCategoryOfFiber R.equivalence R.fiberAlg
      fiber := R.equivalence.functor ⋙ R.fiberAlg
      fiberFunctor := S1753FiberFunctorTransport R.equivalence R.fiberAlg }

/-! ## 4. The exact missing statements -/

/-- The actual small cover category: a genuine `Category.{0,1}` on the
actual cover type whose hom types are the actual cover maps.  This is the
first target field, and the first missing geometric input; S1728 proves that
the target implies the small hom data, S1733/S1744 isolate the affine-model
comparison that would supply it. -/
def S1753ActualCoverCategoryMissing : Prop :=
  ∃ C : Category.{0, 1} S1753Cover,
    Nonempty (∀ A B,
      @Quiver.Hom _ C.toQuiver A B ≃ S1728CoverMap A B)

/-- **The first missing input of the finite-etale-algebra route**: the actual
small cover category together with an equivalence to `FiniteEtaleAlg K`.

The category part is the first target field; the equivalence is the transport
input.  No such equivalence is constructed in the tree.  At the time of
writing, S1750 has no actual construction file; its probes compare finite-etale
algebras over the affine curve ring with those over the function field, not
with the actual stack cover type.  S1743 gives an object map to the affine
slice and isolates the missing comparison, but not an equivalence to
`FiniteEtaleAlg K`. -/
def S1753CoverAlgEquivalence : Prop :=
  ∃ (C : Category.{0, 1} S1753Cover)
    (_ : ∀ A B, @Quiver.Hom _ C.toQuiver A B ≃ S1728CoverMap A B),
    Nonempty (@CategoryTheory.Equivalence S1753Cover S1753Alg C
      (S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.category (K := S1753K)))

/-- The first missing input alone supplies the first target field. -/
theorem S1753ActualCoverCategoryMissing_of_coverAlgEquivalence
    (h : S1753CoverAlgEquivalence) : S1753ActualCoverCategoryMissing := by
  rcases h with ⟨C, hhom, _⟩
  exact ⟨C, ⟨hhom⟩⟩

/-- The exact first missing statement, named. -/
abbrev S1753FirstMissing : Prop := S1753CoverAlgEquivalence

/-- **The second missing input**: the five field hypotheses of S1749 for
`GaloisCategory (FiniteEtaleAlg K)`, including the fibre-functor condition.

S1749 proves the assembly from these hypotheses but does not supply them. -/
def S1753FiniteEtaleGaloisFields : Prop :=
  ∃ (hPull : HasPullbacks S1753Alg)
    (hCoprod : HasFiniteCoproducts S1753Alg)
    (hQuot : ∀ (G : Type) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) S1753Alg)
    (hMono : ∀ {X Y : S1753Alg} (i : X ⟶ Y), Mono i →
      ∃ (Z : S1753Alg) (u : Z ⟶ Y),
        Nonempty (IsColimit (BinaryCofan.mk i u))),
    @S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.FiberFunctorField S1753K _
      (S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.preGaloisCategory
        hPull hCoprod hQuot hMono)

/-- **The S1743 missing comparison**: the equivalence between the actual
2-isomorphism-quotient cover category and the affine finite-etale slice.
This is S1743's own missing statement, imported here by name. -/
abbrev S1753S1743Missing : Prop := S1743CoverSliceComparisonMissing

/-- The S1743 missing comparison gives an actual `Category.{0,1}` on the
cover type (via S1743's conditional construction), but it does not by itself
give an equivalence to `FiniteEtaleAlg K`. -/
theorem S1753Category01_of_S1743Missing (h : S1753S1743Missing) :
    Nonempty (Category.{0, 1} S1753Cover) := by
  rcases h with ⟨d⟩
  exact S1743Category01_of_comparison d

/-! ## 5. Conditional assembly from the exact missing inputs -/

/-- From the exact missing equivalence and the exact missing S1749 fields, the
four target fields are obtained by the genuine transport above. -/
theorem S1753TargetFields_of_missing
    (heq : S1753CoverAlgEquivalence)
    (hgal : S1753FiniteEtaleGaloisFields) :
    Nonempty S1753TargetFields := by
  rcases heq with ⟨C, hhom, ⟨E⟩⟩
  rcases hgal with ⟨hPull, hCoprod, hQuot, hMono, hFiber⟩
  letI : Category.{0, 1} S1753Cover := C
  letI : Category.{0, 1} S1753Alg :=
    S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.category (K := S1753K)
  let hPre : PreGaloisCategory S1753Alg :=
    S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.preGaloisCategory
      hPull hCoprod hQuot hMono
  letI : PreGaloisCategory S1753Alg := hPre
  letI : PreGaloisCategory.FiberFunctor
      (S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.geometricFiber S1753K) := hFiber
  refine ⟨S1753TargetFields.ofFiniteEtaleRoute
    { coverCategory := C
      coverHomEquiv := hhom
      equivalence := E
      preGaloisCategoryAlg := hPre
      fiberAlg := S1749FiniteEtaleGaloisAssembly.FiniteEtaleAlg.geometricFiber S1753K
      fiberFunctorAlg := hFiber }⟩

/-- The first missing input alone supplies the category field once combined
with the S1749 fields; this is the precise reduction of the four target fields
to the two missing inputs. -/
theorem S1753TargetFields_of_firstMissing
    (hfirst : S1753FirstMissing) (hgal : S1753FiniteEtaleGaloisFields) :
    Nonempty S1753TargetFields :=
  S1753TargetFields_of_missing hfirst hgal

/-- The first missing input already supplies the target's `coverCategory`
field. -/
theorem S1753Category01_of_coverAlgEquivalence
    (h : S1753CoverAlgEquivalence) :
    Nonempty (Category.{0, 1} S1753Cover) := by
  rcases h with ⟨C, _, _⟩
  exact ⟨C⟩

/-! ## 6. Checks and axiom audit -/

#check S1753PreGaloisCategory
#check S1753FiberFunctorTransport
#check S1753GaloisCategoryOfFiber
#check S1753GaloisCategory
#check S1753TargetFields
#check S1753TargetFields.ofOrbicurveEtaleFundamentalGroup
#check S1753FiniteEtaleRoute
#check S1753TargetFields.ofFiniteEtaleRoute
#check S1753ActualCoverCategoryMissing
#check S1753CoverAlgEquivalence
#check S1753ActualCoverCategoryMissing_of_coverAlgEquivalence
#check S1753FirstMissing
#check S1753FiniteEtaleGaloisFields
#check S1753S1743Missing
#check S1753Category01_of_S1743Missing
#check S1753TargetFields_of_missing
#check S1753TargetFields_of_firstMissing
#check S1753Category01_of_coverAlgEquivalence

#print axioms S1753UnitTriangle
#print axioms S1753TransportRightLeg
#print axioms S1753PreGaloisCategory
#print axioms S1753FiberFunctorTransport
#print axioms S1753GaloisCategoryOfFiber
#print axioms S1753GaloisCategory
#print axioms S1753TargetFields.ofOrbicurveEtaleFundamentalGroup
#print axioms S1753TargetFields.ofFiniteEtaleRoute
#print axioms S1753Category01_of_S1743Missing
#print axioms S1753ActualCoverCategoryMissing_of_coverAlgEquivalence
#print axioms S1753TargetFields_of_missing
#print axioms S1753TargetFields_of_firstMissing
#print axioms S1753Category01_of_coverAlgEquivalence

end LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual
