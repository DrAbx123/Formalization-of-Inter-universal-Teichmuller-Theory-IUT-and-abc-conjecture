/-
# S1865: coherent coproducts from the coherent affine bridge

S1878 now proves fullness of the coherent affine functor unconditionally
(S1878Full_proof); only S1878EssSurj (every finite etale cover of Spec R'
is the affine model of a coherent cover) remains.  This file uses that
bridge to construct finite coproducts on the coherent category, at both
the S1854 Category.{1,1} and the target Category.{0,1} structures.

With S1871EssSurj (every weak cover is isomorphic to a coherent one), it
also gets finite coproducts on the weak S1728 category, the equivalence of
the weak category with the affine target, and hence S1833FirstMissing.

The strict S1854CoproductApexCoherent is not used: it asks the arbitrary
Classical.choice representatives of HasInitial/HasBinaryCoproducts to be
literally coherent.  The choice-free statement is
S1865EssentialCoproductApex, and it is exactly S1871EssSurj.

Exact first missing: S1878EssSurj and S1871EssSurj.  Neither is proved here
and no fake limit or axiom is introduced.
-/

import tmp.sheaf.xif.paper.S1878CoherentAffineBridgeActual
import tmp.sheaf.xif.paper.S1871CoherentEssSurjActual
import tmp.sheaf.xif.paper.S1854CoherentCategoryActual
import tmp.sheaf.xif.paper.S1857CoherentLimits01Actual
import tmp.sheaf.xif.paper.S1856CoherentLimitsActual
import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual
import tmp.sheaf.xif.paper.S1779CorrectFiniteEtaleTargetActual
import tmp.sheaf.xif.paper.S1833ActualCoverCoproductsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1865CoprodApexActual

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual
open LeanFormal.IUT.XiFPaper.S1871CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual

theorem S1865AlgHasFiniteCoproducts : HasFiniteCoproducts S1779AlgR := inferInstance

theorem S1865TargetHasFiniteCoproducts : HasFiniteCoproducts S1878Target := by
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    S1878Target _ S1779AlgR _ (Discrete (Fin n)) _
    S1814AlgEquiv.symm.functor
    S1814AlgEquiv.symm.isEquivalence_functor
    (inferInstance : HasColimitsOfShape (Discrete (Fin n)) S1779AlgR)

theorem S1865CoherentHasFiniteCoproducts (h : S1878EssSurj) :
    @HasFiniteCoproducts S1878CoherentCategory inferInstance := by
  letI : S1878Functor.IsEquivalence := S1878Functor_isEquivalence_iff_essSurj.mpr h
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    S1878CoherentCategory _ S1878Target _ (Discrete (Fin n)) _
    S1878Functor inferInstance
    (S1865TargetHasFiniteCoproducts.out n)

attribute [local instance] S1854CoherentCategory11

noncomputable def S1865CoherentTo1854 :
    @CategoryTheory.Functor S1878CoherentCategory inferInstance
      CoherentCover S1854CoherentCategory11 where
  obj C := C
  map {C D} f := (S1854QuotEquiv C D).symm f.hom
  map_id C := by
    change (S1854QuotEquiv C C).symm (𝟙 (CoherentCover.cover C)) = S1857Id11 C
    rw [S1857Id11_def]
  map_comp {C D E} f g := by
    change (S1854QuotEquiv C E).symm (f.hom ≫ g.hom) =
      S1857Comp11 ((S1854QuotEquiv C D).symm f.hom)
        ((S1854QuotEquiv D E).symm g.hom)
    rw [S1857Comp11_def]
    congr 1
    simp only [Equiv.apply_symm_apply]

instance S1865CoherentTo1854_faithful : S1865CoherentTo1854.Faithful where
  map_injective {C D} f g h := by
    apply InducedCategory.hom_ext
    exact (S1854QuotEquiv C D).symm.injective h

instance S1865CoherentTo1854_full : S1865CoherentTo1854.Full where
  map_surjective {C D} (f : S1854CoherentQuot C D) :=
    ⟨InducedCategory.homMk (S1854QuotEquiv C D f), by
      change (S1854QuotEquiv C D).symm (S1854QuotEquiv C D f) = f
      exact Equiv.symm_apply_apply _ _⟩

instance S1865CoherentTo1854_essSurj : S1865CoherentTo1854.EssSurj where
  mem_essImage C := ⟨C, ⟨Iso.refl C⟩⟩

instance S1865CoherentTo1854_isEquivalence : S1865CoherentTo1854.IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

theorem S1865Coherent11HasFiniteCoproducts (h : S1878EssSurj) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 := by
  haveI := S1865CoherentHasFiniteCoproducts h
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory11 S1878CoherentCategory inferInstance
    (Discrete (Fin n)) _
    S1865CoherentTo1854.asEquivalence.inverse
    (Equivalence.isEquivalence_inverse S1865CoherentTo1854.asEquivalence)
    (inferInstance : HasColimitsOfShape (Discrete (Fin n)) S1878CoherentCategory)

theorem S1865Coherent01HasFiniteCoproducts (h : S1878EssSurj) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory01 := by
  letI : Category.{0, 1} CoherentCover := S1854CoherentCategory01
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory01 CoherentCover S1854CoherentCategory11
    (Discrete (Fin n)) _
    S1857Coherent01To11 S1857Coherent01To11_isEquivalence
    ((S1865Coherent11HasFiniteCoproducts h).out n)

theorem S1865WeakHasFiniteCoproducts
    (h : S1878EssSurj) (hE : S1871EssSurj) : HasFiniteCoproducts S1728Cover := by
  haveI := S1865CoherentHasFiniteCoproducts h
  let F := inducedFunctor (F := CoherentCover.cover)
  letI : F.EssSurj := ⟨fun A => hE A⟩
  letI : F.IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    S1728Cover _ S1878CoherentCategory _ (Discrete (Fin n)) _
    F.asEquivalence.inverse
    (Equivalence.isEquivalence_inverse F.asEquivalence)
    (inferInstance : HasColimitsOfShape (Discrete (Fin n)) S1878CoherentCategory)

theorem S1865WeakEquivTarget (h : S1878EssSurj) (hE : S1871EssSurj) :
    Nonempty (S1728Cover ≌ S1878Target) := by
  letI : S1878Functor.IsEquivalence := S1878Functor_isEquivalence_iff_essSurj.mpr h
  let F := inducedFunctor (F := CoherentCover.cover)
  letI : F.EssSurj := ⟨fun A => hE A⟩
  letI : F.IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  exact ⟨F.asEquivalence.symm.trans S1878Functor.asEquivalence⟩

theorem S1865WeakAlgEquiv (h : S1878EssSurj) (hE : S1871EssSurj) :
    Nonempty (S1728Cover ≌ S1779AlgR) := by
  obtain ⟨e⟩ := S1865WeakEquivTarget h hE
  exact ⟨e.trans S1814AlgEquiv.symm⟩

theorem S1865S1833FirstMissing (h : S1878EssSurj) (hE : S1871EssSurj) :
    S1833FirstMissing :=
  S1833FirstMissing_iff.mpr (S1865WeakAlgEquiv h hE)

def S1865EssentialCoproductApex : Prop :=
  (∀ h0 : HasInitial S1728Cover,
    Nonempty { P : CoherentCover // Nonempty (P.cover ≅ (⊥_ S1728Cover)) }) ∧
  (∀ h2 : HasBinaryCoproducts S1728Cover, ∀ A B : CoherentCover,
    Nonempty { P : CoherentCover // Nonempty (P.cover ≅ (A.cover ⨿ B.cover)) })

theorem S1865EssentialCoproductApex_of_essSurj
    (hE : S1871EssSurj) : S1865EssentialCoproductApex := by
  constructor
  · intro h0
    letI := h0
    obtain ⟨C, ⟨e⟩⟩ := hE (⊥_ S1728Cover)
    exact ⟨C, ⟨e⟩⟩
  · intro h2 A B
    letI := h2
    obtain ⟨C, ⟨e⟩⟩ := hE (A.cover ⨿ B.cover)
    exact ⟨C, ⟨e⟩⟩

theorem S1865StrictApex_implies_essential
    (h0 : HasInitial S1728Cover) (h2 : HasBinaryCoproducts S1728Cover)
    (hA : S1854CoproductApexCoherent h0 h2) :
    (Nonempty { P : CoherentCover // Nonempty (P.cover ≅ (⊥_ S1728Cover)) }) ∧
      (∀ A B : CoherentCover,
        Nonempty { P : CoherentCover // Nonempty (P.cover ≅ (A.cover ⨿ B.cover)) }) := by
  constructor
  · obtain ⟨P, hP⟩ := hA.1
    exact ⟨P, ⟨eqToIso hP⟩⟩
  · intro A B
    obtain ⟨P, hP⟩ := hA.2 A B
    exact ⟨P, ⟨eqToIso hP⟩⟩

theorem S1865HasInitial_of_hasFiniteCoproducts
    {C : Type*} [Category C] [HasFiniteCoproducts C] : HasInitial C := by
  let F : Discrete (Fin 0) ⥤ C := functorOfIsEmpty _ _
  haveI : HasColimit F := (HasFiniteCoproducts.out 0).has_colimit F
  have hinit : IsInitial (colimit F) :=
    (isColimitEquivIsInitialOfIsEmpty (C := C) (J := Discrete (Fin 0)) (F := F)
      (colimit.cocone F)).toFun (colimit.isColimit F)
  exact IsInitial.hasInitial hinit

/-- The strict S1856 coproduct first-missing follows from the (false, by
S1871) equality version of coherent essential surjectivity.  This isolates the
extra content of the strict condition: the chosen Classical.choice apexes must
be literally coherent. -/
theorem S1865S1856CoproductFirstMissing_of_eqSurj
    (h : S1833FirstMissing)
    (hEq : ∀ A : S1728Cover, ∃ C : CoherentCover, C.cover = A) :
    S1856CoproductFirstMissing := by
  haveI hFC : HasFiniteCoproducts S1728Cover :=
    S1833HasFiniteCoproducts_of_firstMissing h
  haveI hInit : HasInitial S1728Cover := S1865HasInitial_of_hasFiniteCoproducts
  refine ⟨h, hInit, inferInstance, ?_⟩
  constructor
  · obtain ⟨C, hC⟩ := hEq (⊥_ S1728Cover)
    exact ⟨C, hC⟩
  · intro A B
    obtain ⟨C, hC⟩ := hEq (A.cover ⨿ B.cover)
    exact ⟨C, hC⟩

structure S1865CoproductInputs where
  essSurj : S1878EssSurj
  coherentEssSurj : S1871EssSurj

theorem S1865CoproductInputs_hasFiniteCoproducts (d : S1865CoproductInputs) :
    (@HasFiniteCoproducts CoherentCover S1854CoherentCategory11) ∧
      (@HasFiniteCoproducts CoherentCover S1854CoherentCategory01) :=
  ⟨S1865Coherent11HasFiniteCoproducts d.essSurj,
   S1865Coherent01HasFiniteCoproducts d.essSurj⟩

theorem S1865CoproductInputs_hasWeakCoproducts (d : S1865CoproductInputs) :
    S1833FirstMissing ∧ HasFiniteCoproducts S1728Cover :=
  ⟨S1865S1833FirstMissing d.essSurj d.coherentEssSurj,
   S1865WeakHasFiniteCoproducts d.essSurj d.coherentEssSurj⟩

theorem S1865CoproductInputs_essentialApex (d : S1865CoproductInputs) :
    S1865EssentialCoproductApex :=
  S1865EssentialCoproductApex_of_essSurj d.coherentEssSurj

#print axioms S1865TargetHasFiniteCoproducts
#print axioms S1865CoherentHasFiniteCoproducts
#print axioms S1865CoherentTo1854
#print axioms S1865CoherentTo1854_isEquivalence
#print axioms S1865Coherent11HasFiniteCoproducts
#print axioms S1865Coherent01HasFiniteCoproducts
#print axioms S1865WeakHasFiniteCoproducts
#print axioms S1865WeakEquivTarget
#print axioms S1865WeakAlgEquiv
#print axioms S1865S1833FirstMissing
#print axioms S1865EssentialCoproductApex_of_essSurj
#print axioms S1865StrictApex_implies_essential
#print axioms S1865CoproductInputs_hasFiniteCoproducts
#print axioms S1865CoproductInputs_hasWeakCoproducts
#print axioms S1865CoproductInputs_essentialApex
#print axioms S1865S1856CoproductFirstMissing_of_eqSurj

end LeanFormal.IUT.XiFPaper.S1865CoprodApexActual