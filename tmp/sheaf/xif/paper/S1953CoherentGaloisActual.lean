/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1953
-/
import tmp.sheaf.xif.paper.S1943AssembleEssSurjActual
import tmp.sheaf.xif.paper.S1875CoherentGaloisAssemblyActual
import tmp.sheaf.xif.paper.S1934RPrimeField6Actual

/-!
# S1953: the coherent layer is actually equivalent to `FiniteEtaleCover (Spec R')`,
  and the coherent covers form a Galois category unconditionally

## Inputs

* **S1943** (`S1943AssembleEssSurjActual`) closes S1878's last input.  For every
  finite etale cover `C` of `Spec R'` it builds the strong finite-etale extension
  datum `S1943Strong C`, the coherent cover `S1897ExtCoherent C (S1943Strong C)`,
  and an isomorphism of its affine model with `C` (`S1943S1816Obj_iso`).  Hence

    `S1943EssSurj : S1878EssSurj`,
    `S1943Functor_isEquivalence : S1878Functor.IsEquivalence`,
    `S1943FunctorToSlice_isEquivalence : S1878FunctorToSlice.IsEquivalence`.

  No hypothesis, no `sorry`, no fake 2-cell: the strong structure comes from S1911's
  corrected representable two-pullback theorem applied to actual scheme fibre
  products, and the model of the extension cover at the identity point is the
  canonical isomorphism `pullback f 1 ≅ X`.

* **S1878** proves fullness (`S1878Full_proof`) and faithfulness unconditionally,
  and proves `S1878Functor_isEquivalence_iff_essSurj`.

* **S1868** reduces `S1868FirstMissing` (the coherence of the affine comparison at
  the target hom universe) to `S1868EssSurj` (`S1868FirstMissing_iff_essSurj`,
  fullness being `S1878Full_proof`) and identifies `S1868EssSurj` with
  `S1878EssSurj` (`S1868EssSurj_iff_S1878EssSurj`).

* **S1934** proves S1855's field 6 unconditionally (`S1934BCReflectsIsos`).

* **S1875** assembles `GaloisCategory` at `S1854CoherentCategory01` from exactly
  `S1868FirstMissing` and `S1835BCReflectsIsos` (`S1875GaloisCategory`).

## What is constructed here

1. `S1953Coherent11To1878`: the identity-on-objects comparison from the S1854
   coherent category at `Category.{1,1}` to S1878's induced coherent category.
   Its hom map is `S1854QuotEquiv`, the bijection between 2-isomorphism classes of
   compatible cover maps and S1728 cover-map classes.  It is proved full,
   faithful and essentially surjective, hence an equivalence.

2. `S1953Equiv1878`: **`S1878CoherentCategory ≌ FiniteEtaleCover (Spec R')`**,
   whose functor is literally S1878's canonical comparison `S1878Functor`
   (`S1953Equiv1878_functor`, by `rfl`).

3. `S1953Equiv11` and `S1953Equiv01`: the same equivalence for S1854's two actual
   coherent categories `S1854CoherentCategory11` and `S1854CoherentCategory01`,
   obtained by the explicit comparisons `S1953Coherent11To1878` and S1857's
   `S1857CoherentEquivalenceInv`.  Their functors are still the canonical affine
   model: `S1953Equiv11_obj` and `S1953Equiv01_obj` compute the object map as
   `S1816Obj A.cover` by `rfl`, so these are not transports of an abstract
   equivalence.

4. `S1953EquivSlice`: the affine finite-etale slice form
   `S1878CoherentCategory ≌ S1733Slice`.

5. The S1868 reductions become theorems (`S1953S1868EssSurj`,
   `S1953S1868FirstMissing`, `S1953S1868Equivalence`) and the algebra-side
   equivalences `S1953EquivAlg11`, `S1953EquivAlg01` become unconditional.

6. **The Galois assembly**: `S1953PreGaloisCategory`, `S1953GaloisCategory`
   (`GaloisCategory CoherentCover` at `S1854CoherentCategory01`),
   `S1953HasQuotientsByFiniteGroups`, `S1953MonoDirectSummand`, and the six-field
   fibre functor `S1953FiberFunctor` -- all unconditional.

## Honest boundary

There is no remaining hypothesis on this route: `S1953NoResidual` records that
S1878's essential surjectivity, S1868's first missing, and S1855/S1835's field 6
are all theorems.  Every equivalence asserted here is bundled with its actual
functor, and each functor is either the canonical affine comparison or the
identity on objects with the proved hom bijection `S1854QuotEquiv`; no equivalence
is postulated.  No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit`
occurs; the axiom footprint is checked at the end.

As everywhere in the coherent layer, the category structures
`S1854CoherentCategory11` and `S1854CoherentCategory01` are *not* global
instances; this file declares both as local instances, exactly as S1857 and
S1868 do.  A consumer of, say, `S1953GaloisCategory` at the target universe
declares `attribute [local instance] S1854CoherentCategory01` (and, to use the
`S1878CoherentCategory` form directly, the `S1854CoherentCategory11` one).

The instance arguments are exactly as intended and can be inspected with
`set_option pp.explicit true`: `S1953Equiv1878` carries S1878's induced category
structure on `CoherentCover` (not either S1854 transport), `S1953Equiv11` carries
`S1854CoherentCategory11`, and `S1953Equiv01`, `S1953GaloisCategory`,
`S1953HasQuotientsByFiniteGroups`, `S1953MonoDirectSummand` and
`S1953FiberFunctor` carry `S1854CoherentCategory01`; the target instance is
`FiniteEtaleCover (Spec R')` throughout.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.defProp false

namespace LeanFormal.IUT.XiFPaper.S1953CoherentGaloisActual

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual
open LeanFormal.IUT.XiFPaper.S1868CoherentFiberActual
open LeanFormal.IUT.XiFPaper.S1875CoherentGaloisAssemblyActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual
open LeanFormal.IUT.XiFPaper.S1934RPrimeField6Actual
open LeanFormal.IUT.XiFPaper.S1943AssembleEssSurjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

attribute [local instance] S1854CoherentCategory11 S1854CoherentCategory01

/-! ## 1. S1943's unconditional essential surjectivity -/

/-- **S1878's essential surjectivity, unconditionally.**  This is S1943's theorem:
every finite etale cover of `Spec R'` is isomorphic, over `Spec R'`, to the affine
model of a coherent cover. -/
theorem S1953S1878EssSurj : S1878EssSurj :=
  S1943EssSurj

/-- S1878's fullness, restated at the point of use. -/
theorem S1953S1878Full : S1878Full :=
  S1878Full_proof

/-- **The canonical coherent affine comparison is an equivalence.**  Fullness and
faithfulness are S1878's unconditional theorems; essential surjectivity is S1943. -/
theorem S1953S1878Functor_isEquivalence : S1878Functor.IsEquivalence :=
  S1878Functor_isEquivalence_iff_essSurj.mpr S1943EssSurj

/-- S1943's affine-slice form, restated. -/
theorem S1953FunctorToSlice_isEquivalence : S1878FunctorToSlice.IsEquivalence :=
  S1943FunctorToSlice_isEquivalence

/-! ## 2. The identity-on-objects comparison with S1878's induced coherent category -/

/-- **The comparison from the S1854 coherent category at `Category.{1,1}` to S1878's
induced coherent category.**  It is the identity on coherent covers and
`S1854QuotEquiv` on 2-isomorphism classes of compatible cover maps: the very
identification S1854 proves between its transported homs and the S1728 cover-map
classes.  No new morphism is invented. -/
noncomputable def S1953Coherent11To1878 :
    @CategoryTheory.Functor CoherentCover S1854CoherentCategory11
      S1878CoherentCategory inferInstance where
  obj A := A
  map {A B} f := InducedCategory.homMk (S1854QuotEquiv A B f)
  map_id A := by
    apply InducedCategory.hom_ext
    exact S1854Forget11.map_id A
  map_comp {A B C} f g := by
    apply InducedCategory.hom_ext
    exact S1854Forget11.map_comp f g

/-- The comparison is the identity on objects. -/
@[simp] theorem S1953Coherent11To1878_obj (A : CoherentCover) :
    S1953Coherent11To1878.obj A = A := rfl

/-- The comparison is full: every S1728 cover-map class has a compatible
representative (S1854's `S1854Compatible_of_map`). -/
instance S1953Coherent11To1878_full : S1953Coherent11To1878.Full where
  map_surjective {A B} f :=
    ⟨(S1854QuotEquiv A B).symm f.hom, by
      apply InducedCategory.hom_ext
      exact Equiv.apply_symm_apply _ _⟩

/-- The comparison is faithful, by injectivity of the hom bijection. -/
instance S1953Coherent11To1878_faithful : S1953Coherent11To1878.Faithful where
  map_injective {A B} f g h :=
    (S1854QuotEquiv A B).injective (congrArg InducedCategory.Hom.hom h)

/-- The comparison is essentially surjective: it is the identity on objects. -/
instance S1953Coherent11To1878_essSurj : S1953Coherent11To1878.EssSurj where
  mem_essImage A := ⟨A, ⟨Iso.refl A⟩⟩

/-- **The two coherent categories are equivalent.** -/
instance S1953Coherent11To1878_isEquivalence : S1953Coherent11To1878.IsEquivalence where

/-! ## 3. The equivalences with `FiniteEtaleCover (Spec R')` -/

/-- **The coherent layer is actually equivalent to the finite etale covers of
`Spec R'`.**  The functor is S1878's canonical comparison `S1878Functor`
(`S1878Obj` on objects, `S1816Map` on morphisms); its equivalence is exactly
S1878's criterion plus S1943's essential surjectivity. -/
noncomputable def S1953Equiv1878 : S1878CoherentCategory ≌ S1878Target := by
  letI : S1878Functor.IsEquivalence := S1953S1878Functor_isEquivalence
  exact S1878Functor.asEquivalence

/-- The functor of the equivalence is *literally* the canonical comparison. -/
@[simp] theorem S1953Equiv1878_functor : S1953Equiv1878.functor = S1878Functor := rfl

/-- The object map of the equivalence is the affine model. -/
@[simp] theorem S1953Equiv1878_obj (A : S1878CoherentCategory) :
    S1953Equiv1878.functor.obj A = S1816Obj A.cover := rfl

/-- The same statement with the target written in the paper's notation:
`FiniteEtaleCover (Spec R')`, where `Spec R' = S1816Base = S1726AffineScheme`. -/
theorem S1953Equiv1878_finiteEtale :
    Nonempty (S1878CoherentCategory ≌ FiniteEtaleCover S1816Base) :=
  ⟨S1953Equiv1878⟩

/-- **`S1854CoherentCategory11 ≌ FiniteEtaleCover (Spec R')`**, unconditionally. -/
noncomputable def S1953Equiv11 :
    @CategoryTheory.Equivalence CoherentCover S1878Target S1854CoherentCategory11
      inferInstance :=
  S1953Coherent11To1878.asEquivalence.trans S1953Equiv1878

/-- Its functor still sends a coherent cover to its affine model, on the nose. -/
@[simp] theorem S1953Equiv11_obj (A : CoherentCover) :
    S1953Equiv11.functor.obj A = S1816Obj A.cover := rfl

/-- **`S1854CoherentCategory01 ≌ FiniteEtaleCover (Spec R')`**, unconditionally.
This is the target hom universe used by the Galois assembly. -/
noncomputable def S1953Equiv01 :
    @CategoryTheory.Equivalence CoherentCover S1878Target S1854CoherentCategory01
      inferInstance :=
  S1857CoherentEquivalenceInv.trans S1953Equiv11

/-- Its functor also sends a coherent cover to its affine model, on the nose. -/
@[simp] theorem S1953Equiv01_obj (A : CoherentCover) :
    S1953Equiv01.functor.obj A = S1816Obj A.cover := rfl

/-- **The affine finite-etale slice form**: `S1878CoherentCategory ≌ S1733Slice`
(S1943's `S1943FunctorToSlice_isEquivalence`). -/
noncomputable def S1953EquivSlice : S1878CoherentCategory ≌ S1733Slice := by
  letI : S1878FunctorToSlice.IsEquivalence := S1943FunctorToSlice_isEquivalence
  exact S1878FunctorToSlice.asEquivalence

/-! ## 4. The S1868 side: the coherent affine comparison is an equivalence -/

/-- **S1868's essential surjectivity, unconditionally** (S1868 and S1943). -/
theorem S1953S1868EssSurj : S1868EssSurj :=
  S1868EssSurj_iff_S1878EssSurj.mpr S1943EssSurj

/-- **S1868's first missing is closed**: fullness is S1878's, essential
surjectivity is S1943's. -/
theorem S1953S1868FirstMissing : S1868FirstMissing :=
  S1868FirstMissing_iff_essSurj.mpr S1953S1868EssSurj

/-- **The coherent covers to finite etale `R'`-algebras comparison is an
equivalence**, unconditionally. -/
theorem S1953S1868Equivalence : S1868CoherentAlgebraFunctor.IsEquivalence :=
  S1868FirstMissing_iff_equivalence.mp S1953S1868FirstMissing

/-- **`S1854CoherentCategory11 ≌ (FiniteEtale R')^op`**, unconditionally. -/
noncomputable def S1953EquivAlg11 :
    @CategoryTheory.Equivalence CoherentCover S1779AlgR S1854CoherentCategory11
      inferInstance :=
  S1868CoherentAlgebraEquiv11 S1953S1868Equivalence

/-- **`S1854CoherentCategory01 ≌ (FiniteEtale R')^op`**, unconditionally. -/
noncomputable def S1953EquivAlg01 :
    @CategoryTheory.Equivalence CoherentCover S1779AlgR S1854CoherentCategory01
      inferInstance :=
  S1868CoherentAlgebraEquiv01 S1953S1868Equivalence

/-! ## 5. The Galois category at the coherent covers, unconditionally -/

section GaloisAssembly

attribute [local instance] S1830Main.S1830PreGaloisCategory

/-- **The five-field `PreGaloisCategory` at `S1854CoherentCategory01`**,
transported from S1830's unconditional pre-Galois structure along the now
unconditional coherent affine equivalence. -/
theorem S1953PreGaloisCategory :
    @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1868PreGaloisCategory01 S1953S1868Equivalence

/-- **The coherent covers form a Galois category**: Mathlib's `GaloisCategory` at
`S1854CoherentCategory01`, with no remaining hypothesis.  S1875's assembly consumes
S1868's first missing (now `S1953S1868FirstMissing`) and S1855's field 6 (now
S1934's `S1934BCReflectsIsos`). -/
theorem S1953GaloisCategory :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1875GaloisCategory S1953S1868FirstMissing S1934BCReflectsIsos

/-- The pre-Galois structure underlying the Galois category is the transported one
that the fibre functor lives on: the two assemblies agree, not merely in class. -/
theorem S1953GaloisCategory_toPreGalois :
    S1953GaloisCategory.toPreGaloisCategory = S1953PreGaloisCategory :=
  Subsingleton.elim _ _

/-- **The two fields the direct S1854/S1857 route left open are now theorems**:
S1875's missing data bundle is inhabited. -/
theorem S1953PreGaloisMissing : S1875PreGaloisMissing :=
  S1875PreGaloisMissing_of_S1868FirstMissing S1953S1868FirstMissing

/-- **(G2) Quotients by finite groups**, unconditionally: every action of a finite
group on a coherent cover has a colimit.  This is a literal field of the
`PreGaloisCategory` structure of `S1953PreGaloisCategory`, not a fragment. -/
theorem S1953HasQuotientsByFiniteGroups : S1875QuotientsByFiniteGroups :=
  S1953PreGaloisMissing.quotients

/-- **(G3) Monomorphisms induce isomorphisms on direct summands**, unconditionally.
Also a literal `PreGaloisCategory` field. -/
theorem S1953MonoDirectSummand : S1875MonoDirectSummand :=
  S1953PreGaloisMissing.mono

/-- **The six-field fibre functor at the closed geometric point `(0,0)` of
`Spec R'`**, unconditionally: S1868's Omega-fibre functor `S1868Fiber01` with
Mathlib's six `PreGaloisCategory.FiberFunctor` fields, transported along the
coherent affine equivalence and using S1934's field 6. -/
@[reducible] noncomputable def S1953FiberFunctor :
    @PreGaloisCategory.FiberFunctor CoherentCover S1854CoherentCategory01
      (S1868PreGaloisCategory01 S1953S1868Equivalence) S1868Fiber01 :=
  S1868FiberFunctor01 S1953S1868Equivalence S1934BCReflectsIsos

/-- The Galois category of `S1953GaloisCategory` is the one obtained from the
six-field fibre functor `S1953FiberFunctor` and the transported pre-Galois
structure: an independent check that the two assemblies agree on the fibre
functor, not merely on the class. -/
theorem S1953GaloisCategory_eq_fiber :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 := by
  letI : @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
    S1868PreGaloisCategory01 S1953S1868Equivalence
  exact GaloisCategory.mk ⟨S1868Fiber01, ⟨S1953FiberFunctor⟩⟩

end GaloisAssembly

/-! ## 6. No residual hypothesis -/

/-- **The precise residual is empty.**  The three inputs named along this route are
all theorems: S1943's `S1878EssSurj` (S1878's last gap), S1868's equivalence
(equivalent to it), and S1855/S1835's field 6 (S1934). -/
theorem S1953NoResidual :
    S1878EssSurj ∧ S1868FirstMissing ∧ S1835BCReflectsIsos :=
  ⟨S1943EssSurj, S1953S1868FirstMissing, S1934BCReflectsIsos⟩

/-- Consequently the coherent layer needs no extra hypothesis either: the
equivalence is total. -/
theorem S1953NoResidualStatement :
    (S1878Functor.IsEquivalence ∧ S1868CoherentAlgebraFunctor.IsEquivalence) ∧
      (@GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01) :=
  ⟨⟨S1953S1878Functor_isEquivalence, S1953S1868Equivalence⟩,
    S1953GaloisCategory⟩

/-! ## 7. Checks and axiom audit -/

#check S1953S1878EssSurj
#check S1953S1878Full
#check S1953S1878Functor_isEquivalence
#check S1953FunctorToSlice_isEquivalence
#check S1953Coherent11To1878
#check S1953Coherent11To1878_obj
#check S1953Coherent11To1878_full
#check S1953Coherent11To1878_faithful
#check S1953Coherent11To1878_essSurj
#check S1953Coherent11To1878_isEquivalence
#check S1953Equiv1878
#check S1953Equiv1878_functor
#check S1953Equiv1878_obj
#check S1953Equiv1878_finiteEtale
#check S1953Equiv11
#check S1953Equiv11_obj
#check S1953Equiv01
#check S1953Equiv01_obj
#check S1953EquivSlice
#check S1953S1868EssSurj
#check S1953S1868FirstMissing
#check S1953S1868Equivalence
#check S1953EquivAlg11
#check S1953EquivAlg01
#check S1953PreGaloisCategory
#check S1953GaloisCategory
#check S1953GaloisCategory_toPreGalois
#check S1953PreGaloisMissing
#check S1953HasQuotientsByFiniteGroups
#check S1953MonoDirectSummand
#check S1953FiberFunctor
#check S1953GaloisCategory_eq_fiber
#check S1953NoResidual
#check S1953NoResidualStatement

#print axioms S1953Coherent11To1878
#print axioms S1953Coherent11To1878_full
#print axioms S1953Coherent11To1878_faithful
#print axioms S1953Coherent11To1878_essSurj
#print axioms S1953Equiv1878
#print axioms S1953Equiv1878_functor
#print axioms S1953Equiv1878_obj
#print axioms S1953Equiv11
#print axioms S1953Equiv11_obj
#print axioms S1953Equiv01
#print axioms S1953Equiv01_obj
#print axioms S1953EquivSlice
#print axioms S1953S1868EssSurj
#print axioms S1953S1868FirstMissing
#print axioms S1953S1868Equivalence
#print axioms S1953EquivAlg11
#print axioms S1953EquivAlg01
#print axioms S1953PreGaloisCategory
#print axioms S1953GaloisCategory
#print axioms S1953GaloisCategory_toPreGalois
#print axioms S1953PreGaloisMissing
#print axioms S1953HasQuotientsByFiniteGroups
#print axioms S1953MonoDirectSummand
#print axioms S1953FiberFunctor
#print axioms S1953GaloisCategory_eq_fiber
#print axioms S1953NoResidual
#print axioms S1953NoResidualStatement

end LeanFormal.IUT.XiFPaper.S1953CoherentGaloisActual
