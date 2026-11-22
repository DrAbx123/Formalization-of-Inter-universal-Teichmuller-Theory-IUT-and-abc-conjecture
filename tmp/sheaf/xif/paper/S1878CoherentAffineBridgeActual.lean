/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1878
-/
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1816OrbicurveCoversToAffineActual
import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual

/-!
# S1878: the coherent-cover affine bridge

## The question

Are the *coherent* covers of S1852 equivalent to the affine finite-etale slice
S1733Slice, or equivalently to FiniteEtaleCover (Spec R')?

S1841 and S1816 showed that the canonical comparison

    S1816Obj : S1728Cover -> FiniteEtaleCover (Spec R'),

built from the identity-point base change, is a functor only under S1756's
source-representability statement: its identity law at A is exactly
S1756End A = 1 (S1816Map_id_iff).  S1850 refutes that statement on the
recorded (weak) cover type, so no functor with the canonical object and morphism
maps exists on all weak covers (S1878NoCanonicalWeakFunctor below).

S1852 supplies the coherent cover datum: a strong finite-etale presentation at
every test point, hence the full 2-universal property of the identity-point
square.  In particular every coherent cover satisfies S1756End A = 1
(S1852FirstMissingOnCoherent).  This is exactly what is needed for the
identity law.

## What is constructed here

1. S1878CoherentCategory: the induced category on coherent covers, whose
   morphisms are morphisms of the underlying recorded covers.  Coherence is an
   object-level datum, so this is the full subcategory on coherent objects;
   no strong-morphism structure is invented.

2. S1878Functor : S1878CoherentCategory ⥤ FiniteEtaleCover (Spec R'), with
   object map S1816Obj C.cover and morphism map S1816Map; the identity law
   is supplied by S1852FirstMissingOnCoherent, the composition law by the
   unconditional S1816Map_comp.

3. S1878Functor_faithful: the canonical functor is faithful, unconditionally,
   from S1816Map_injective.

4. S1878Full: **fullness is unconditional on coherent covers**, and
   S1878Full_proof/S1878Functor_full prove it.  Given a target morphism g
   between the affine models, the coherent unit gives a quasi-equivalence
   between each model stack and its cover source; conjugating g by the model
   sections gives a cover map (S1878CoverMap) whose 2-Yoneda comparison is g
   (S1878MapOfCoverMap_eq).  Thus the canonical functor is full and faithful.

5. S1878EssSurj: the one remaining missing statement, that every finite etale
   cover of Spec R' is the affine model of a coherent cover (the
   extension/inverse construction).  S1878Functor_isEquivalence_iff_essSurj
   proves the canonical functor is an equivalence **iff** this statement
   holds.

6. S1878FunctorToSlice: the composite with S1814's unconditional equivalence
   S1733Slice ≌ FiniteEtaleCover (Spec R').  Hence the same single missing
   statement is exactly the missing equivalence between coherent covers and
   the affine slice S1733Slice
   (S1878FunctorToSlice_isEquivalence_iff_essSurj).

## Honest boundary

No equivalence is asserted.  Coherence removes the identity-law obstruction of
S1816 and, as proved here, also gives fullness, but it does not by itself prove
essential surjectivity (the extension/inverse construction).  That statement is
named, not assumed.  No sorry, no axiom, no Shrink/ULift/PUnit, and no fake
functor or equivalence is introduced.  The axiom footprint is checked at the
end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual

open CategoryTheory
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-! ## 1. The induced category on coherent covers -/

/-- The category of coherent covers, with the underlying recorded-cover
morphisms.  The extra strong/coherent data is object-level, so this is the full
subcategory on the coherent objects. -/
abbrev S1878CoherentCategory : Type 1 :=
  InducedCategory S1728Cover CoherentCover.cover

example : Category.{1, 1} S1878CoherentCategory := inferInstance

/-- The underlying recorded cover of an object of the induced category. -/
abbrev S1878Underlying (C : S1878CoherentCategory) : S1728Cover :=
  CoherentCover.cover C

/-- The target: finite etale covers of Spec R'. -/
abbrev S1878Target : Type 1 := S1816Target

/-- The affine model object of a coherent cover. -/
noncomputable def S1878Obj (C : S1878CoherentCategory) : S1878Target :=
  S1816Obj (S1878Underlying C)

/-- The object map is literally the S1816 affine representative of the
underlying recorded cover. -/
@[simp] theorem S1878Obj_eq_S1816Obj (C : S1878CoherentCategory) :
    S1878Obj C = S1816Obj (S1878Underlying C) := rfl

/-- The carrier of the affine model. -/
@[simp] theorem S1878Obj_carrier (C : S1878CoherentCategory) :
    FiniteEtaleCover.carrier (S1878Obj C) = (S1733Model (S1878Underlying C)).left := rfl

/-- The structure morphism of the affine model. -/
@[simp] theorem S1878Obj_structureMap (C : S1878CoherentCategory) :
    FiniteEtaleCover.structureMap (S1878Obj C) =
      (S1733ModelOver (S1878Underlying C)).left := rfl

/-- The canonical comparison functor from coherent covers to finite etale
covers of Spec R'.  The identity law is exactly the coherent cover's
source-representability (S1852FirstMissingOnCoherent); composition is
S1816Map_comp. -/
noncomputable def S1878Functor : S1878CoherentCategory ⥤ S1878Target where
  obj C := S1878Obj C
  map {C D} f := S1816Map (S1878Underlying C) (S1878Underlying D) f.hom
  map_id C :=
    (S1816Map_id_iff (S1878Underlying C)).mpr
      (S1852FirstMissingOnCoherent C)
  map_comp {C D E} f g := S1816Map_comp _ _ _ f.hom g.hom

/-- The object map of the canonical functor. -/
@[simp] theorem S1878Functor_obj (C : S1878CoherentCategory) :
    S1878Functor.obj C = S1816Obj (S1878Underlying C) := rfl

/-- The morphism map of the canonical functor. -/
@[simp] theorem S1878Functor_map {C D : S1878CoherentCategory}
    (f : C ⟶ D) :
    S1878Functor.map f =
      S1816Map (S1878Underlying C) (S1878Underlying D) f.hom := rfl

/-- The canonical functor is faithful, unconditionally. -/
instance S1878Functor_faithful : S1878Functor.Faithful where
  map_injective {C D} f g h := by
    apply InducedCategory.hom_ext
    exact S1816Map_injective (S1878Underlying C) (S1878Underlying D) h

/-! ## 2. Fullness and essential surjectivity -/

/-- Fullness of the canonical functor on coherent covers.  This is proved
unconditionally as `S1878Full_proof`. -/
def S1878Full : Prop :=
  ∀ C D : S1878CoherentCategory,
    Function.Surjective (fun f : C ⟶ D => S1878Functor.map f)

/-- Essential surjectivity onto FiniteEtaleCover (Spec R'): every finite etale
cover of Spec R' is isomorphic to the affine model of a coherent cover. -/
def S1878EssSurj : Prop :=
  ∀ C : S1878Target,
    ∃ A : S1878CoherentCategory, Nonempty (S1878Obj A ≅ C)

/-- Fullness of the functor is exactly the named statement. -/
theorem S1878Functor_full_iff :
    S1878Functor.Full ↔ S1878Full := by
  constructor
  · intro hF C D
    exact hF.map_surjective
  · intro hF
    exact ⟨fun {C D} => hF C D⟩

/-- Essential surjectivity of the functor is exactly the named statement. -/
theorem S1878Functor_essSurj_iff :
    S1878Functor.EssSurj ↔ S1878EssSurj := by
  constructor
  · intro hE C
    obtain ⟨A, ⟨e⟩⟩ := hE.mem_essImage C
    exact ⟨A, ⟨e⟩⟩
  · intro hE
    exact ⟨fun C => hE C⟩

/-! ### 2b. Fullness of the canonical functor (unconditional) -/

/-- The S1816 affine model morphism underlying a target morphism.  A target
morphism is a scheme morphism over Spec R'; it is automatically over Spec F'
because the structure maps to Spec F' factor through Spec R'. -/
noncomputable def S1878ModelOverHom (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    S1733Model (S1878Underlying C) ⟶ S1733Model (S1878Underlying D) :=
  Over.homMk g.hom.left (by
    have hcomp : g.hom.left ≫ (S1733ModelOver (S1878Underlying D)).left =
        (S1733ModelOver (S1878Underlying C)).left := g.hom.w
    calc
      g.hom.left ≫ (S1733Model (S1878Underlying D)).hom
          = g.hom.left ≫ ((S1733ModelOver (S1878Underlying D)).left ≫
              S1726AffineOver.hom) := by
            rw [← (S1733ModelOver (S1878Underlying D)).w]
            rfl
      _ = (g.hom.left ≫ (S1733ModelOver (S1878Underlying D)).left) ≫
            S1726AffineOver.hom := by
            rw [← Category.assoc]
      _ = (S1733ModelOver (S1878Underlying C)).left ≫ S1726AffineOver.hom := by
            rw [hcomp]
            rfl
      _ = (S1733Model (S1878Underlying C)).hom :=
            (S1733ModelOver (S1878Underlying C)).w)

@[simp] theorem S1878ModelOverHom_left (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    (S1878ModelOverHom C D g).left = g.hom.left := rfl


/-- The Yoneda strong transformation of a target morphism is compatible with
the identity-point projections to the base. -/
noncomputable def S1878YonedaProjectionIso (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) (S1878ModelOverHom C D g))
        (S1756ProjectionMap (S1878Underlying D)))
      (S1756ProjectionMap (S1878Underlying C)) :=
  (S1756IsoOfEvalEq _ _ _ _ (by
    rw [S1743YonedaEval_vcomp, S1743YonedaEval_eq_S1742,
      S1742HomOfStrongTrans_strongTransOfHom,
      S1756YonedaEval_projectionMap, S1756YonedaEval_projectionMap]
    exact (by
      apply Over.OverMorphism.ext
      change (S1878ModelOverHom C D g).left ≫
        (S1733ModelOver (S1878Underlying D)).left =
        (S1733ModelOver (S1878Underlying C)).left
      rw [S1878ModelOverHom_left]
      exact g.hom.w))).some


/-- The strong transformation of cover sources induced by a target morphism:
the model section of the source, the Yoneda transformation of the model
morphism, and the identity-point comparison of the target. -/
noncomputable def S1878MapTrans (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    Pseudofunctor.StrongTrans (S1743Source (S1878Underlying C))
      (S1743Source (S1878Underlying D)) :=
  Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.StrongTrans.vcomp
      (S1743Lift (S1878Underlying C))
      (S1742StrongTransOfHom (F := S1726K) (S1878ModelOverHom C D g)))
    (S1756ToSource (S1878Underlying D))

set_option maxHeartbeats 4000000 in
noncomputable def S1878Commutes (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1878MapTrans C D g)
        (S1878Underlying D).map)
      (S1878Underlying C).map := by
  let Lc := S1743Lift (S1878Underlying C)
  let Ld := S1743Lift (S1878Underlying D)
  let Tc := S1756ToSource (S1878Underlying C)
  let Td := S1756ToSource (S1878Underlying D)
  let Pc := S1756ProjectionMap (S1878Underlying C)
  let Pd := S1756ProjectionMap (S1878Underlying D)
  let Y := S1742StrongTransOfHom (F := S1726K) (S1878ModelOverHom C D g)
  let B := S1733BasePoint
  change Iso
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Lc Y) Td)
      (S1878Underlying D).map)
    (S1878Underlying C).map
  exact
    (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp Lc Y) Td
      (S1878Underlying D).map).trans
    ((S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp Lc Y)
      (Pseudofunctor.StrongTrans.vcomp Td (S1878Underlying D).map)
      (Pseudofunctor.StrongTrans.vcomp Pd B)
      ((S1743BaseChange (S1878Underlying D)).commutes)).trans
    ((S1756AssociatorIso Lc Y (Pseudofunctor.StrongTrans.vcomp Pd B)).trans
    ((S1756WhiskerLeftIso Lc
      (Pseudofunctor.StrongTrans.vcomp Y (Pseudofunctor.StrongTrans.vcomp Pd B))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Y Pd) B)
      ((S1756AssociatorIso Y Pd B).symm)).trans
    ((S1756AssociatorIso Lc (Pseudofunctor.StrongTrans.vcomp Y Pd) B).symm.trans
    ((S1756WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp Lc (Pseudofunctor.StrongTrans.vcomp Y Pd))
      (Pseudofunctor.StrongTrans.vcomp Lc Pc) B
      (S1756WhiskerLeftIso Lc (Pseudofunctor.StrongTrans.vcomp Y Pd) Pc
        (S1878YonedaProjectionIso C D g))).trans
    ((S1756WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp Lc Pc)
      (S1878Underlying C).map B
      (S1816LiftProjection (S1878Underlying C))).trans
    (S1756RightUnitorIso (S1878Underlying C).map)))))))


noncomputable def S1878CoverMap (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    S1728CoverMap (S1878Underlying C) (S1878Underlying D) where
  map := S1878MapTrans C D g
  commutes := S1878Commutes C D g

set_option maxHeartbeats 4000000 in
noncomputable def S1878EtaIso (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    Iso (S1816Eta (S1878Underlying C) (S1878Underlying D)
        (S1878CoverMap C D g))
      (S1742StrongTransOfHom (F := S1726K) (S1878ModelOverHom C D g)) := by
  let Lc := S1743Lift (S1878Underlying C)
  let Ld := S1743Lift (S1878Underlying D)
  let Tc := S1756ToSource (S1878Underlying C)
  let Td := S1756ToSource (S1878Underlying D)
  let Y := S1742StrongTransOfHom (F := S1726K) (S1878ModelOverHom C D g)
  let M := Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.StrongTrans.vcomp Lc Y) Td
  have hUc : Iso (Pseudofunctor.StrongTrans.vcomp Tc Lc)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack (S1878Underlying C))) :=
    (C.unit).some
  have hUd : Iso (Pseudofunctor.StrongTrans.vcomp Td Ld)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack (S1878Underlying D))) :=
    (D.unit).some
  change Iso
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp Tc M) Ld) Y
  exact
    (S1756AssociatorIso Tc M Ld).trans
    ((S1756WhiskerLeftIso Tc
      (Pseudofunctor.StrongTrans.vcomp M Ld)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Lc Y)
        (Pseudofunctor.StrongTrans.vcomp Td Ld))
      (S1756AssociatorIso (Pseudofunctor.StrongTrans.vcomp Lc Y) Td Ld)).trans
    ((S1756WhiskerLeftIso Tc
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Lc Y)
        (Pseudofunctor.StrongTrans.vcomp Td Ld))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Lc Y)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack (S1878Underlying D))))
      (S1756WhiskerLeftIso (Pseudofunctor.StrongTrans.vcomp Lc Y)
        (Pseudofunctor.StrongTrans.vcomp Td Ld)
        (Pseudofunctor.StrongTrans.id _) hUd)).trans
    ((S1756WhiskerLeftIso Tc
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp Lc Y)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack (S1878Underlying D))))
      (Pseudofunctor.StrongTrans.vcomp Lc Y)
      (S1756RightUnitorIso (Pseudofunctor.StrongTrans.vcomp Lc Y))).trans
    ((S1756AssociatorIso Tc Lc Y).symm.trans
    ((S1756WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp Tc Lc)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack (S1878Underlying C))) Y hUc).trans
    (S1756LeftUnitorIso Y))))))

theorem S1878ModelMap_eq (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    S1816ModelMap (S1878Underlying C) (S1878Underlying D)
        (S1878CoverMap C D g) =
      S1878ModelOverHom C D g := by
  have h := S1743YonedaEval_congr_iso
    (S1733Model (S1878Underlying C)) (S1733Model (S1878Underlying D))
    (S1878EtaIso C D g)
  rw [S1816ModelMap_eq_eval, h, S1743YonedaEval_eq_S1742,
    S1742HomOfStrongTrans_strongTransOfHom]

theorem S1878MapOfCoverMap_eq (C D : S1878CoherentCategory)
    (g : S1878Obj C ⟶ S1878Obj D) :
    S1816MapOfCoverMap (S1878Underlying C) (S1878Underlying D)
        (S1878CoverMap C D g) = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rw [S1816MapOfCoverMap_hom_left, S1878ModelMap_eq, S1878ModelOverHom_left]

theorem S1878Full_proof : S1878Full := by
  intro C D g
  refine ⟨InducedCategory.homMk (Quot.mk _ (S1878CoverMap C D g)), ?_⟩
  change S1816Map (S1878Underlying C) (S1878Underlying D)
    (Quot.mk _ (S1878CoverMap C D g)) = g
  rw [S1816Map_mk, S1878MapOfCoverMap_eq]


/-- The canonical functor is an equivalence iff it is full and essentially
surjective.  Faithfulness is unconditional. -/
theorem S1878Functor_isEquivalence_iff :
    S1878Functor.IsEquivalence ↔ S1878Functor.Full ∧ S1878EssSurj := by
  constructor
  · intro hE
    exact ⟨hE.full, S1878Functor_essSurj_iff.mp hE.essSurj⟩
  · rintro ⟨hfull, hess⟩
    exact ⟨inferInstance, hfull, S1878Functor_essSurj_iff.mpr hess⟩

/-- The exact named criterion for the canonical functor to be an equivalence. -/
theorem S1878Functor_isEquivalence_iff_full_essSurj :
    S1878Functor.IsEquivalence ↔ S1878Full ∧ S1878EssSurj :=
  S1878Functor_isEquivalence_iff.trans
    (and_congr S1878Functor_full_iff (Iff.rfl))

/-- Fullness is unconditional on coherent covers. -/
theorem S1878Functor_full : S1878Functor.Full :=
  S1878Functor_full_iff.mpr S1878Full_proof

/-- The canonical functor is fully faithful. -/
noncomputable def S1878Functor_fullyFaithful : S1878Functor.FullyFaithful := by
  letI : S1878Functor.Full := S1878Functor_full
  exact Functor.FullyFaithful.ofFullyFaithful S1878Functor

/-- The canonical functor is an equivalence exactly when it is essentially
surjective: fullness and faithfulness are unconditional. -/
theorem S1878Functor_isEquivalence_iff_essSurj :
    S1878Functor.IsEquivalence ↔ S1878EssSurj := by
  rw [S1878Functor_isEquivalence_iff, S1878Functor_full_iff]
  exact ⟨fun h => h.2, fun h => ⟨S1878Full_proof, h⟩⟩

/-! ## 3. The bridge to the affine finite-etale slice S1733Slice -/

/-- The composite canonical functor to the affine slice S1733Slice, using
S1814's unconditional equivalence S1733Slice ≌ FiniteEtaleCover (Spec R'). -/
noncomputable def S1878FunctorToSlice : S1878CoherentCategory ⥤ S1733Slice :=
  S1878Functor ⋙ S1814SliceEquiv.inverse

/-- The composite functor is faithful. -/
instance S1878FunctorToSlice_faithful : S1878FunctorToSlice.Faithful := by
  dsimp [S1878FunctorToSlice]
  infer_instance

/-- The composite with S1814's equivalence is an equivalence iff the canonical
functor to FiniteEtaleCover (Spec R') is. -/
theorem S1878FunctorToSlice_isEquivalence_iff :
    S1878FunctorToSlice.IsEquivalence ↔ S1878Functor.IsEquivalence := by
  constructor
  · intro h
    dsimp [S1878FunctorToSlice] at h
    letI : (S1878Functor ⋙ S1814SliceEquiv.inverse).IsEquivalence := h
    exact Functor.isEquivalence_of_comp_right S1878Functor S1814SliceEquiv.inverse
  · intro h
    letI : S1878Functor.IsEquivalence := h
    show (S1878Functor ⋙ S1814SliceEquiv.inverse).IsEquivalence
    infer_instance

/-- **The exact answer for the affine slice**: the composite canonical functor
to S1733Slice is an equivalence iff the single remaining gap -- essential
surjectivity -- is closed. -/
theorem S1878FunctorToSlice_isEquivalence_iff_essSurj :
    S1878FunctorToSlice.IsEquivalence ↔ S1878EssSurj :=
  S1878FunctorToSlice_isEquivalence_iff.trans
    S1878Functor_isEquivalence_iff_essSurj

/-- The coherent covers do not exhaust the recorded covers: if every recorded
cover were coherent, S1756's first missing statement would hold, contradicting
S1850.  The equivalence sought below is therefore not the identity on objects. -/
theorem S1878NotEveryCoverCoherent :
    ¬ ∀ A : S1728Cover, ∃ C : CoherentCover, C.cover = A :=
  fun h => S1850_not_firstMissing (S1852FirstMissing_of_coherentAll h)

/-- The remaining coherent essential-surjectivity statement implies S1816's
essential surjectivity: forget the coherence of the witness. -/
theorem S1816EssSurj_of_S1878EssSurj (h : S1878EssSurj) : S1816EssSurj := by
  intro C
  obtain ⟨A, hA⟩ := h C
  exact ⟨S1878Underlying A, hA⟩

/-! ## 4. The weak-cover obstruction to S1816/S1841 -/

/-- The canonical S1816 object and morphism maps fail the functor identity law
on the recorded weak-cover type.  This is exactly S1756's source
representability, which S1850 refutes; hence no functor on all weak covers can
have precisely these maps.  This is the precise reason the coherent
strengthening is used. -/
theorem S1878CanonicalWeakIdentityLawFalse :
    ¬ ∀ A : S1728Cover, S1816Map A A (𝟙 A) = 𝟙 (S1816Obj A) :=
  fun h => S1850_not_firstMissing ((S1816FunctorLaw_iff_firstMissing).mp h)

/-! ## 5. Checks and axiom footprint -/

#check S1878CoherentCategory
#check S1878Obj
#check S1878Functor
#check S1878Functor_faithful
#check S1878Full
#check S1878EssSurj
#check S1878ModelOverHom
#check S1878YonedaProjectionIso
#check S1878CoverMap
#check S1878EtaIso
#check S1878ModelMap_eq
#check S1878MapOfCoverMap_eq
#check S1878Full_proof
#check S1878Functor_full
#check S1878Functor_fullyFaithful
#check S1878Functor_isEquivalence_iff_essSurj
#check S1878FunctorToSlice
#check S1878FunctorToSlice_isEquivalence_iff_essSurj
#check S1878NotEveryCoverCoherent
#check S1816EssSurj_of_S1878EssSurj
#check S1878CanonicalWeakIdentityLawFalse

#print axioms S1878Functor
#print axioms S1878Functor_faithful
#print axioms S1878Functor_full_iff
#print axioms S1878Functor_essSurj_iff
#print axioms S1878ModelOverHom
#print axioms S1878YonedaProjectionIso
#print axioms S1878CoverMap
#print axioms S1878EtaIso
#print axioms S1878ModelMap_eq
#print axioms S1878MapOfCoverMap_eq
#print axioms S1878Full_proof
#print axioms S1878Functor_full
#print axioms S1878Functor_fullyFaithful
#print axioms S1878Functor_isEquivalence_iff_essSurj
#print axioms S1878FunctorToSlice
#print axioms S1878FunctorToSlice_isEquivalence_iff_essSurj
#print axioms S1878NotEveryCoverCoherent
#print axioms S1816EssSurj_of_S1878EssSurj
#print axioms S1878CanonicalWeakIdentityLawFalse

end LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual