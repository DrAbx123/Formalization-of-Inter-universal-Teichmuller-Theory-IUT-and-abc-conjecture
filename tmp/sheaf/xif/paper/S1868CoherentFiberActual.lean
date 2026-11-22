/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1868
-/
import tmp.sheaf.xif.paper.S1857CoherentLimits01Actual
import tmp.sheaf.xif.paper.S1816OrbicurveCoversToAffineActual
import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual
import tmp.sheaf.xif.paper.S1855RPrimeFiberIntegrationActual
import tmp.sheaf.xif.paper.S1753OrbicurveEtalePiAssemblyActual
import tmp.sheaf.xif.paper.S1829FiberCoveredYonedaActual
import tmp.sheaf.xif.paper.S1803AffineSectionsActual
import tmp.sheaf.xif.paper.S1878CoherentAffineBridgeActual

/-!
# S1868: the coherent-cover fibre functor at the closed geometric point (0,0)

## The question

S1854 built the actual category

  S1854CoherentCategory11 : Category.{1,1} CoherentCover

and S1857 proved that it is equivalent to the target-universe category

  S1854CoherentCategory01 : Category.{0,1} CoherentCover.

S1852 proved that every coherent cover satisfies S1756's source-representability
(the identity-point unit 2-cell).  The present file asks for the fibre functor of
these coherent covers at the closed geometric point (0,0) of Spec R',
together with the six fields of Mathlib's PreGaloisCategory.FiberFunctor
(terminal objects, pullbacks, finite coproducts, epimorphisms, quotients by
finite groups, reflection of isomorphisms), or for the exact first missing
piece.

## The construction

The fibre at (0,0) is the geometric fibre of the affine model of a coherent
cover at the geometric point Omega = AlgebraicClosure F' (Mathlib's
CommAlgCat.FiniteEtale.fiber R' Omega).  The comparison from coherent covers
to the algebra side is the composite

  S1854Forget11                     : CoherentCover -> S1728Cover
  S1816Obj / S1816Map               : S1728Cover -> FiniteEtaleCover (Spec R')
  S1814AlgEquiv.inverse             : FiniteEtaleCover (Spec R') -> (FiniteEtale R')^op.

The identity law of this composite is exactly S1756End A = 1, which S1852
proves for every coherent cover; composition is S1816's unconditional
S1816Map_comp.  Hence

  S1868CoherentAlgebraFunctor : S1854CoherentCategory11 ⥤ S1779AlgR

is an unconditional functor, and it is faithful.  Composing with S1835's
geometric fibre functor gives the unconditional candidate

  S1868Fiber11 : S1854CoherentCategory11 ⥤ FintypeCat,
  S1868Fiber11.obj A = Hom_{R'}(Gamma(S1733Model A.cover), Omega).

Its objects are the Omega-points of the affine model of the cover, i.e. the
geometric fibre at the geometric point (0,0).

## The six fields and the exact first missing

The six-field structure is transported from S1855's six-field fibre functor on
(FiniteEtale R')^op (S1835's fiber R' Omega).  The transport requires the
comparison S1868CoherentAlgebraFunctor to be an equivalence.  The coherent
hom comparison has two halves:

  S1868Full    = the comparison is full,
  S1868EssSurj = every finite etale R'-algebra is the affine model of a
                 coherent cover,

  S1868FirstMissing = S1868Full ∧ S1868EssSurj
                    ↔ S1868CoherentAlgebraFunctor.IsEquivalence.

S1868Full and S1868EssSurj are exactly the coherent-cover parts of S1816's
hom comparison and affine-extension statements (S1868Full_iff_S1816,
S1868EssSurj_iff_S1816).  **S1878 proves S1868Full unconditionally**
(S1878Full_proof, used in S1868Full_proof).  Hence the exact first missing is
only the essential-surjectivity half,

  S1868EssSurj ↔ S1868FirstMissing  (S1868FirstMissing_iff_essSurj),

and it is exactly S1878's S1878EssSurj (S1868EssSurj_iff_S1878EssSurj).

At the target hom universe C01, once S1868EssSurj holds, S1753's transport
gives a genuine PreGaloisCategory on CoherentCover and a six-field
PreGaloisCategory.FiberFunctor S1868Fiber01.  On the algebra side, S1855
already proves fields 1--5 and leaves exactly field 6, S1835BCReflectsIsos;
hence after S1868EssSurj the only remaining input is S1855's field 6.
(At C11 the hom universe is 1, while (FiniteEtale R')^op has hom universe 0;
S1753's transport requires the same hom universe on both sides.  The
unconditional C11 candidate S1868Fiber11 is still constructed, and S1857
carries it to C01, where the six fields are assembled.)

## The literal scheme-valued fibre of S1735/S1780/S1829

S1735's S1735Fiber is the *scheme-valued* fibre at Spec F' (the F'-points
of the base-change model), not the Omega-points used by the Galois fibre
functor.  It is a different type.  What S1780/S1829 provide for it is
finiteness and coverage: under discreteness of the source stack value at the
base site, S1735Fiber A.cover is finite for every coherent cover
(S1868CoherentLiteralFiberFintype).  No identification of the two fibres is
asserted; the six-field construction uses the Omega-fibre, as a Galois fibre
functor must.

## Honest boundary

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs in this file.  The
functor S1868CoherentAlgebraFunctor and the candidate fibre functor
S1868Fiber11 are unconditional.  The six-field structure is *conditional* on
the exact first missing S1868EssSurj and on S1855's field 6; both are named,
neither is assumed.  Only propext, Classical.choice and Quot.sound occur; see
the audit block at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1868CoherentFiberActual

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual
open LeanFormal.IUT.XiFPaper.S1735GeometricFiberActual.Paper
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1780GeometricFiberFintypeActual
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
open LeanFormal.IUT.XiFPaper.S1803AffineSectionsActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1829FiberCoveredYonedaActual
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1855RPrimeFiberIntegrationActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual

universe u

/-! ## 1. The coherent covers to finite etale R'-algebras comparison -/

section Coherent11

attribute [local instance] S1854CoherentCategory11

/-- **The coherent covers to finite etale R'-algebras functor.**

A coherent cover is sent to the finite etale algebra of global sections of its
identity-point affine model S1733Model A.cover.  The morphism map is the
S1816 affine comparison composed with the global-sections functor of S1799.
The identity law is the coherent source-representability
S1852FirstMissingOnCoherent; the composition law is unconditional
S1816Map_comp. -/
noncomputable def S1868CoherentAlgebraFunctor :
    CoherentCover ⥤ S1779AlgR where
  obj A := S1814AlgEquiv.inverse.obj (S1816Obj A.cover)
  map {A B} f := S1814AlgEquiv.inverse.map
    (S1816Map A.cover B.cover (S1854QuotEquiv A B f))
  map_id A := by
    have hq : S1854QuotEquiv A A (𝟙 A) = 𝟙 A.cover :=
      S1854Forget11.map_id A
    have h16 : S1816Map A.cover A.cover (𝟙 A.cover) =
        𝟙 (S1816Obj A.cover) :=
      (S1816Map_id_iff A.cover).mpr (S1852FirstMissingOnCoherent A)
    rw [hq, h16]
    exact S1814AlgEquiv.inverse.map_id (S1816Obj A.cover)
  map_comp {A B C} f g := by
    have hq := S1854Forget11.map_comp f g
    change S1814AlgEquiv.inverse.map
        (S1816Map A.cover C.cover (S1854Forget11.map (f ≫ g))) =
      S1814AlgEquiv.inverse.map
          (S1816Map A.cover B.cover (S1854Forget11.map f)) ≫
        S1814AlgEquiv.inverse.map
          (S1816Map B.cover C.cover (S1854Forget11.map g))
    rw [hq, S1816Map_comp, S1814AlgEquiv.inverse.map_comp]
    rfl

/-- The object formula: the algebra is the global sections of the affine model. -/
theorem S1868CoherentAlgebraFunctor_obj (A : CoherentCover) :
    S1868CoherentAlgebraFunctor.obj A =
      S1814AlgEquiv.inverse.obj (S1816Obj A.cover) := rfl

/-- The functor is faithful: the S1854 forgetful functor is faithful, the S1816
comparison is injective on 2-isomorphism classes, and the S1814 algebra
equivalence is faithful. -/
instance S1868CoherentAlgebraFunctor_faithful :
    S1868CoherentAlgebraFunctor.Faithful where
  map_injective {A B} f g h := by
    apply (S1854QuotEquiv A B).injective
    apply S1816Map_injective A.cover B.cover
    exact S1814AlgEquiv.inverse.map_injective h

/-! ## 2. Fullness, essential surjectivity and the exact first missing -/

/-- Fullness of the coherent affine comparison. -/
def S1868Full : Prop :=
  ∀ (A B : CoherentCover),
    Function.Surjective
      (fun f : A ⟶ B => S1868CoherentAlgebraFunctor.map f)

/-- Essential surjectivity: every finite etale R'-algebra is the affine model
of a coherent cover. -/
def S1868EssSurj : Prop :=
  ∀ X : S1779AlgR,
    ∃ A : CoherentCover,
      Nonempty (S1868CoherentAlgebraFunctor.obj A ≅ X)

/-- Fullness as a functor property is exactly the named statement. -/
theorem S1868Full_iff : S1868CoherentAlgebraFunctor.Full ↔ S1868Full := by
  constructor
  · intro hF A B
    exact hF.map_surjective
  · intro hF
    exact ⟨fun {A B} => hF A B⟩

/-- Fullness of the coherent affine comparison is exactly the S1816 hom
comparison (S1816Map) being surjective on coherent covers.  This is the
coherent-cover part of S1816's named S1816Full. -/
theorem S1868Full_iff_S1816 :
    S1868Full ↔
      ∀ (A B : CoherentCover),
        Function.Surjective (S1816Map A.cover B.cover) := by
  constructor
  · intro h A B g
    obtain ⟨f, hf⟩ := h A B (S1814AlgEquiv.inverse.map g)
    refine ⟨S1854QuotEquiv A B f, ?_⟩
    exact S1814AlgEquiv.inverse.map_injective hf
  · intro h A B φ
    obtain ⟨g, hg⟩ := S1814AlgEquiv.inverse.map_surjective φ
    obtain ⟨q, hq⟩ := h A B g
    refine ⟨(S1854QuotEquiv A B).symm q, ?_⟩
    change S1814AlgEquiv.inverse.map
        (S1816Map A.cover B.cover
          (S1854QuotEquiv A B ((S1854QuotEquiv A B).symm q))) = φ
    rw [show S1854QuotEquiv A B ((S1854QuotEquiv A B).symm q) = q from
      Equiv.apply_symm_apply _ _]
    rw [hq, hg]

/-- Fullness of the S1816 comparison on coherent covers, proved by S1878. -/
theorem S1868S1816Full_on_coherent :
    ∀ (A B : CoherentCover),
      Function.Surjective (S1816Map A.cover B.cover) := by
  intro A B g
  obtain ⟨f, hf⟩ := S1878Full_proof A B g
  exact ⟨f.hom, by simpa only [S1878Functor_map] using hf⟩

/-- **Fullness is unconditional**: S1878's coherent affine fullness. -/
theorem S1868Full_proof : S1868Full :=
  S1868Full_iff_S1816.mpr S1868S1816Full_on_coherent

/-- Essential surjectivity of the coherent affine comparison is exactly the
coherent-cover part of S1816's essential-surjectivity statement: every finite
etale R'-algebra is the affine model of a coherent cover (up to isomorphism). -/
theorem S1868EssSurj_iff_S1816 :
    S1868EssSurj ↔
      ∀ X : S1779AlgR, ∃ A : CoherentCover,
        Nonempty (S1816Obj A.cover ≅ S1814AlgEquiv.functor.obj X) := by
  constructor
  · intro h X
    obtain ⟨A, ⟨e⟩⟩ := h X
    exact ⟨A, ⟨(S1814AlgEquiv.counitIso.app (S1816Obj A.cover)).symm ≪≫
      S1814AlgEquiv.functor.mapIso e⟩⟩
  · intro h X
    obtain ⟨A, ⟨e⟩⟩ := h X
    exact ⟨A, ⟨S1814AlgEquiv.inverse.mapIso e ≪≫
      (S1814AlgEquiv.unitIso.app X).symm⟩⟩

/-- The reduced first missing is exactly S1878's essential-surjectivity
statement for the canonical coherent affine functor. -/
theorem S1868EssSurj_iff_S1878EssSurj :
    S1868EssSurj ↔ S1878EssSurj := by
  constructor
  · intro h C
    let X := S1814AlgEquiv.functor.objPreimage C
    let eX : S1814AlgEquiv.functor.obj X ≅ C :=
      S1814AlgEquiv.functor.objObjPreimageIso C
    obtain ⟨A, ⟨eA⟩⟩ := (S1868EssSurj_iff_S1816.mp h) X
    exact ⟨A, ⟨eA ≪≫ eX⟩⟩
  · intro h
    exact S1868EssSurj_iff_S1816.mpr
      (fun X => h (S1814AlgEquiv.functor.obj X))

/-- Essential surjectivity as a functor property is exactly the named statement. -/
theorem S1868EssSurj_iff :
    S1868CoherentAlgebraFunctor.EssSurj ↔ S1868EssSurj := by
  constructor
  · intro hE X
    obtain ⟨A, ⟨e⟩⟩ := hE.mem_essImage X
    exact ⟨A, ⟨e⟩⟩
  · intro hE
    exact ⟨fun X => hE X⟩

/-- **The exact first missing for the coherent fibre functor**: the coherent
affine comparison must be an equivalence, equivalently full and essentially
surjective (faithfulness is unconditional). -/
def S1868FirstMissing : Prop := S1868Full ∧ S1868EssSurj

/-- The named first missing is exactly S1868CoherentAlgebraFunctor.IsEquivalence. -/
theorem S1868FirstMissing_iff_equivalence :
    S1868FirstMissing ↔ S1868CoherentAlgebraFunctor.IsEquivalence := by
  constructor
  · rintro ⟨hf, he⟩
    exact ⟨inferInstance, S1868Full_iff.mpr hf, S1868EssSurj_iff.mpr he⟩
  · intro hE
    exact ⟨S1868Full_iff.mp hE.full, S1868EssSurj_iff.mp hE.essSurj⟩

/-- **After S1878's unconditional fullness, the exact first missing is only
essential surjectivity**: every finite etale R'-algebra is the affine model of
a coherent cover. -/
theorem S1868FirstMissing_iff_essSurj :
    S1868FirstMissing ↔ S1868EssSurj :=
  ⟨fun h => h.2, fun h => ⟨S1868Full_proof, h⟩⟩

/-- The exact first missing in its reduced form: essential surjectivity of the
coherent affine comparison. -/
def S1868EssSurjFirstMissing : Prop := S1868EssSurj

/-- The reduced first missing is exactly the original one. -/
theorem S1868EssSurjFirstMissing_iff :
    S1868EssSurjFirstMissing ↔ S1868FirstMissing :=
  S1868FirstMissing_iff_essSurj.symm

/-- The reduced first missing is exactly the equivalence
S1868CoherentAlgebraFunctor.IsEquivalence: fullness is automatic. -/
theorem S1868EssSurj_iff_equivalence :
    S1868EssSurj ↔ S1868CoherentAlgebraFunctor.IsEquivalence :=
  S1868FirstMissing_iff_essSurj.symm.trans S1868FirstMissing_iff_equivalence

/-- The bundled equivalence from the first missing datum. -/
noncomputable def S1868CoherentAlgebraEquiv11
    (hE : S1868CoherentAlgebraFunctor.IsEquivalence) :
    CoherentCover ≌ S1779AlgR := by
  letI : S1868CoherentAlgebraFunctor.IsEquivalence := hE
  exact S1868CoherentAlgebraFunctor.asEquivalence

@[simp] theorem S1868CoherentAlgebraEquiv11_functor
    (hE : S1868CoherentAlgebraFunctor.IsEquivalence) :
    (S1868CoherentAlgebraEquiv11 hE).functor =
      S1868CoherentAlgebraFunctor := rfl

/-! ## 3. The geometric fibre functor at the closed point (0,0) -/

/-- The Omega-points of the affine model of a coherent cover: the geometric
fibre at the closed geometric point (0,0) of Spec R'. -/
noncomputable abbrev S1868GeometricPointFiber (A : CoherentCover) : Type :=
  (S1835Fiber.obj (S1868CoherentAlgebraFunctor.obj A)).obj

/-- **The candidate coherent geometric fibre functor.**  Its object at a
coherent cover is the geometric fibre Hom_{R'}(Gamma(S1733Model A.cover), Omega)
at the closed geometric point; the morphism map is induced by the affine model
action.  It is unconditional. -/
noncomputable def S1868Fiber11 :
    CoherentCover ⥤ FintypeCat.{0} :=
  S1868CoherentAlgebraFunctor ⋙ S1835Fiber

/-- The underlying type of the functor's object is exactly the geometric fibre. -/
@[simp] theorem S1868Fiber11_obj_obj (A : CoherentCover) :
    (S1868Fiber11.obj A).obj = S1868GeometricPointFiber A := rfl

/-- The functor's object formula. -/
@[simp] theorem S1868Fiber11_obj (A : CoherentCover) :
    S1868Fiber11.obj A =
      S1835Fiber.obj (S1868CoherentAlgebraFunctor.obj A) := rfl

/-! ## 4. Universe bookkeeping for the six-field transport

S1753's fibre-functor transport requires the same hom universe on the two
sides of the equivalence.  The coherent category at the 2-isomorphism universe,
S1854CoherentCategory11, has homs in Type 1, while
(FiniteEtale R')^op has homs in Type 0; hence the six-field structure is
not asserted at C11.  S1857's equivalence S1857CoherentEquivalence carries
C11 to the target-universe S1854CoherentCategory01, where both sides have
Type-0 homs.  The transport is performed in Section 5. -/

set_option linter.defProp false

/-! ## 5. The target universe Category.{0,1} -/

section Coherent01

attribute [local instance] S1854CoherentCategory01
attribute [local instance] S1830Main.S1830PreGaloisCategory

/-- The coherent affine comparison at the target hom universe. -/
noncomputable def S1868CoherentAlgebraFunctor01 :
    CoherentCover ⥤ S1779AlgR :=
  S1857Coherent01To11 ⋙ S1868CoherentAlgebraFunctor

/-- The candidate coherent fibre functor at the target hom universe. -/
noncomputable def S1868Fiber01 :
    CoherentCover ⥤ FintypeCat.{0} :=
  S1868CoherentAlgebraFunctor01 ⋙ S1835Fiber

/-- The coherent affine equivalence at the target hom universe, from the
Category.{1,1} comparison and S1857's equivalence of the two coherent
categories. -/
noncomputable def S1868CoherentAlgebraEquiv01
    (hE : S1868CoherentAlgebraFunctor.IsEquivalence) :
    CoherentCover ≌ S1779AlgR := by
  letI : S1868CoherentAlgebraFunctor.IsEquivalence := hE
  exact S1857CoherentEquivalenceInv.trans
    S1868CoherentAlgebraFunctor.asEquivalence

@[simp] theorem S1868CoherentAlgebraEquiv01_functor
    (hE : S1868CoherentAlgebraFunctor.IsEquivalence) :
    (S1868CoherentAlgebraEquiv01 hE).functor =
      S1868CoherentAlgebraFunctor01 := rfl

/-- The transported PreGaloisCategory at the target hom universe. -/
@[reducible] noncomputable def S1868PreGaloisCategory01
    (hE : S1868CoherentAlgebraFunctor.IsEquivalence) :
    PreGaloisCategory CoherentCover :=
  S1753PreGaloisCategory (S1868CoherentAlgebraEquiv01 hE)

/-- **The six-field coherent fibre functor at the target universe
Category.{0,1}**, conditional exactly on the coherent affine equivalence and
on S1855's field 6. -/
@[reducible] noncomputable def S1868FiberFunctor01
    (hE : S1868CoherentAlgebraFunctor.IsEquivalence)
    (hIso : S1835BCReflectsIsos) :
    @PreGaloisCategory.FiberFunctor CoherentCover S1854CoherentCategory01
      (S1868PreGaloisCategory01 hE) S1868Fiber01 := by
  letI : PreGaloisCategory.FiberFunctor S1835Fiber :=
    S1855FiberFunctor hIso
  exact S1753FiberFunctorTransport (S1868CoherentAlgebraEquiv01 hE) S1835Fiber

/-- **The exact reduction of the six fields.**  S1868FirstMissing (the
coherent affine equivalence) plus S1855's field 6 give the six-field fibre
functor at the target universe. -/
theorem S1868FiberFunctor01_of_firstMissing
    (h : S1868FirstMissing) (hIso : S1835BCReflectsIsos) :
    Nonempty
      (@PreGaloisCategory.FiberFunctor CoherentCover S1854CoherentCategory01
        (S1868PreGaloisCategory01
          (S1868FirstMissing_iff_equivalence.mp h)) S1868Fiber01) :=
  ⟨S1868FiberFunctor01 (S1868FirstMissing_iff_equivalence.mp h) hIso⟩

/-- **The six-field functor from the reduced first missing.**  Fullness is
unconditional (S1878); only essential surjectivity and S1855's field 6 remain. -/
theorem S1868FiberFunctor01_of_essSurj
    (h : S1868EssSurj) (hIso : S1835BCReflectsIsos) :
    Nonempty
      (@PreGaloisCategory.FiberFunctor CoherentCover S1854CoherentCategory01
        (S1868PreGaloisCategory01
          (S1868FirstMissing_iff_equivalence.mp
            (S1868FirstMissing_iff_essSurj.mpr h))) S1868Fiber01) :=
  S1868FiberFunctor01_of_firstMissing
    (S1868FirstMissing_iff_essSurj.mpr h) hIso

/-- **The first missing is named, not assumed.**  The six-field coherent fibre
functor at the target universe reduces exactly to the coherent affine
equivalence (S1868FirstMissing) and, on the algebra side, to S1855's field 6. -/
theorem S1868SixFieldsReduction :
    (S1868FirstMissing ↔ S1868EssSurj) ∧
      (∀ (h : S1868EssSurj) (hIso : S1835BCReflectsIsos),
        Nonempty
          (@PreGaloisCategory.FiberFunctor CoherentCover
            S1854CoherentCategory01
            (S1868PreGaloisCategory01
              (S1868FirstMissing_iff_equivalence.mp
                (S1868FirstMissing_iff_essSurj.mpr h))) S1868Fiber01)) :=
  ⟨S1868FirstMissing_iff_essSurj,
    fun h hIso => S1868FiberFunctor01_of_essSurj h hIso⟩

end Coherent01

end Coherent11

/-! ## 6. The literal scheme-valued fibre of S1735/S1780/S1829 -/

/-- Discreteness of the source stack value at the actual base site, restricted
to coherent covers.  This is the coherent part of S1829's S1829FiberDiscrete. -/
def S1868LiteralFiberDiscrete : Prop :=
  ∀ A : CoherentCover,
    IsDiscrete ((A.cover.source.fiber).obj S1780Site)

/-- Under the coherent fibre discreteness, the literal scheme-valued geometric
fibre S1735Fiber A.cover is finite.  This uses S1829's section coverage and
S1803's affine-sections finiteness (the two halves of S1780's reduction). -/
theorem S1868CoherentLiteralFiberFintype
    (h : S1868LiteralFiberDiscrete) (A : CoherentCover) :
    Nonempty (Fintype (S1735Fiber A.cover)) := by
  classical
  haveI : IsDiscrete ((A.cover.source.fiber).obj S1780Site) := h A
  have hcov : S1780FiberCovered A.cover :=
    S1829FiberCovered_of_isDiscrete A.cover
  haveI : Fintype (S1735BaseScheme ⟶ S1780Model A.cover) :=
    Classical.choice (S1803_sectionFintype A.cover)
  exact ⟨Fintype.ofSurjective (S1780SectionToFiber A.cover) hcov⟩

/-! ## 7. Checks and axiom audit -/

#check S1868CoherentAlgebraFunctor
#check S1868CoherentAlgebraFunctor_faithful
#check S1868Full
#check S1868EssSurj
#check S1868Full_iff_S1816
#check S1868EssSurj_iff_S1816
#check S1868EssSurj_iff_S1878EssSurj
#check S1868Full_proof
#check S1868FirstMissing
#check S1868FirstMissing_iff_essSurj
#check S1868EssSurjFirstMissing
#check S1868EssSurjFirstMissing_iff
#check S1868EssSurj_iff_equivalence
#check S1868FirstMissing_iff_equivalence
#check S1868CoherentAlgebraEquiv11
#check S1868GeometricPointFiber
#check S1868Fiber11
#check S1868CoherentAlgebraFunctor01
#check S1868Fiber01
#check S1868CoherentAlgebraEquiv01
#check S1868PreGaloisCategory01
#check S1868FiberFunctor01
#check S1868FiberFunctor01_of_firstMissing
#check S1868FiberFunctor01_of_essSurj
#check S1868SixFieldsReduction
#check S1868LiteralFiberDiscrete
#check S1868CoherentLiteralFiberFintype

#print axioms S1868CoherentAlgebraFunctor
#print axioms S1868CoherentAlgebraFunctor_faithful
#print axioms S1868Full_iff
#print axioms S1868EssSurj_iff
#print axioms S1868Full_iff_S1816
#print axioms S1868EssSurj_iff_S1816
#print axioms S1868EssSurj_iff_S1878EssSurj
#print axioms S1868Full_proof
#print axioms S1868FirstMissing_iff_equivalence
#print axioms S1868FirstMissing_iff_essSurj
#print axioms S1868EssSurjFirstMissing_iff
#print axioms S1868EssSurj_iff_equivalence
#print axioms S1868CoherentAlgebraEquiv11
#print axioms S1868Fiber11
#print axioms S1868PreGaloisCategory01
#print axioms S1868FiberFunctor01
#print axioms S1868FiberFunctor01_of_firstMissing
#print axioms S1868FiberFunctor01_of_essSurj
#print axioms S1868SixFieldsReduction
#print axioms S1868CoherentLiteralFiberFintype

end LeanFormal.IUT.XiFPaper.S1868CoherentFiberActual