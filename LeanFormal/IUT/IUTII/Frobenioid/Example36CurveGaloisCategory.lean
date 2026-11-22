import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveConnectedness
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Galois.Basic
import LeanFormal.IUT.Foundations.Geometry.ClopenFiniteComplement
import Mathlib.Tactic

/-!
# Foundation F3d: basic Galois-category structure of finite etale curve covers

Source anchor: IUT I/II, the D6 curve-Pi input; foundation item F3d.  This file
proves the actual terminal-object fact for the finite etale cover category of
the ONCE-punctured source affine curve curveScheme K = E \ {O} and of the
TWO-punctured extra curveTwoPuncturedScheme K = E \ {O,P} (task-83/task-87
constructions; the extra object is not the source), records the actual
connectedness facts imported from
Example36CurveConnectedness.lean, and freezes only the exact missing
PreGaloisCategory fields as a precise card.  No fake Galois category and no
curve pi-1 identification claim.

## What is proved

* finiteEtaleCover_terminalCover_isTerminal: for any scheme S, the identity
  cover is an actual terminal object of FiniteEtaleCover S, proved from
  Mathlib's Over.mkIdTerminal and the full-subcategory hom extensionality.
* curveAffineTerminalCover_isTerminal / curveTwoPuncturedTerminalCover_isTerminal:
  the specializations to the once-punctured source curveScheme K and to the
  two-punctured extra curveTwoPuncturedScheme K.
* curveAffineEtaleCovers_hasTerminal / curveTwoPuncturedEtaleCovers_hasTerminal:
  the corresponding HasTerminal instances, hence the terminal-object part (G1)
  of a PreGaloisCategory is proved for the once-punctured source category and
  for the two-punctured extra category.
* The actual connectedness facts: the once-punctured source E \ {O} is connected
  and irreducible (curveAffine_connected/curveOncePunctured_connected) and the
  two-punctured extra E \ {O,P} is connected and irreducible
  (curveTwoPunctured_connected).
* Actual fiber products and HasPullbacks: for a cospan f : X ⟶ Z and
  g : Y ⟶ Z of finite etale covers, the file constructs the concrete fiber
  product cover finiteEtaleCoverPullbackCover (the scheme pullback
  f.left g.left with finite etale structure map pullback.fst ≫ X.hom), its
  two projections and the categorical pullback cone
  finiteEtaleCoverPullbackConeInCover, and proves the cone is a limit by
  PullbackCone.IsLimit.mk (finiteEtaleCoverPullbackIsLimitInCover).  This
  yields the actual theorem finiteEtaleCoverHasPullbacks (S) :
  Limits.HasPullbacks (FiniteEtaleCover S), and concrete HasPullbacks
  instances for the once-punctured source cover category, the two-punctured
  extra category, and the affine curve category.  The earlier Over-level
  limit construction finiteEtaleCoverPullbackOverCone/_isLimit is retained as
  the underlying limit-in-Over proof; the full-subcategory pullback no longer
  needs the (non-definitional) diagram identification.
* Actual finite coproducts: the file constructs the binary coproduct cover
  binaryCoproductCover X Y (scheme coproduct with structure map
  coprod.desc X.structureMap Y.structureMap), its two coproduct injections,
  the explicit coproduct descent map, and proves the BinaryCofan is a colimit
  (binaryCoproductIsColimit) via BinaryCofan.IsColimit.mk.  It also constructs
  the initial cover initialCover from the initial scheme and proves it is
  initial (initialCoverIsInitial).  This yields the actual instances
  finiteEtaleCover_hasBinaryCoproduct, finiteEtaleCover_hasBinaryCoproducts,
  finiteEtaleCover_hasInitial, and finiteEtaleCover_hasFiniteCoproducts
  (via hasFiniteCoproducts_of_has_binary_and_initial), hence the finite
  coproduct field (G2) is proved for every finite etale cover category.
* The direct-summand property (G3) is proved: every monomorphism of finite
  etale covers has a clopen complement, the complement is an actual finite
  etale cover, and the monomorphism with the complement inclusion is a binary
  coproduct cofan with an actual IsColimit
  (finiteEtaleCover_monoInducesIsoOnDirectSummand).
* The remaining PreGaloisCategory field is frozen in
  CurvePreGaloisCategoryRemainingFields: quotients by finite groups (G2).  No
  inhabitant is constructed and no theorem consumes the card.  The terminal
  field (G1), pullback field (G1), finite coproduct field (G2) and
  direct-summand field (G3) are removed because they are actually proved.

No fake cover category, no fake fiber functor and no false GaloisCategory
instance are introduced.  No theta / q-pilot / Tate claim is made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open EtaleCoverFoundations

universe u

/-! ## 1. The terminal cover is actually terminal -/

/-- The identity cover of a scheme S is an actual terminal object of the
category of finite etale covers of S.  The proof uses Mathlib's
Over.mkIdTerminal for the underlying over-category and full-subcategory hom
extensionality. -/
noncomputable def finiteEtaleCover_terminalCover_isTerminal (S : Scheme) :
    Limits.IsTerminal (terminalCover S) := by
  have hterm : Limits.IsTerminal (Over.mk (𝟙 S)) := Over.mkIdTerminal (X := S)
  haveI : ∀ X : FiniteEtaleCover S, Unique (X ⟶ terminalCover S) := by
    intro X
    refine ⟨⟨ObjectProperty.homMk (hterm.from X.obj)⟩, fun a => ?_⟩
    apply ObjectProperty.hom_ext
    exact hterm.hom_ext a.hom (hterm.from X.obj)
  exact Limits.IsTerminal.ofUnique _

/-- The identity cover of the affine curve scheme is terminal. -/
noncomputable def curveAffineTerminalCover_isTerminal (K : Type u) [Field K] :
    Limits.IsTerminal (curveAffineTerminalCover K) :=
  finiteEtaleCover_terminalCover_isTerminal (curveScheme K)

/-- The identity cover of the punctured curve scheme is terminal. -/
noncomputable def curveTwoPuncturedTerminalCover_isTerminal (K : Type u) [Field K] :
    Limits.IsTerminal (curveTwoPuncturedTerminalCover K) :=
  finiteEtaleCover_terminalCover_isTerminal (curveTwoPuncturedScheme K)

/-- The affine cover category has a terminal object (the terminal field of
PreGaloisCategory, G1). -/
noncomputable instance curveAffineEtaleCovers_hasTerminal (K : Type u) [Field K] :
    Limits.HasTerminal (curveAffineEtaleCovers K) :=
  (curveAffineTerminalCover_isTerminal K).hasTerminal

/-- The punctured cover category has a terminal object (the terminal field of
PreGaloisCategory, G1). -/
noncomputable instance curveTwoPuncturedEtaleCovers_hasTerminal (K : Type u) [Field K] :
    Limits.HasTerminal (curveTwoPuncturedEtaleCovers K) :=
  (curveTwoPuncturedTerminalCover_isTerminal K).hasTerminal

/-! ## 2. Partial actual fiber products of covers (Over-level construction) -/

section
variable {S : Scheme}

/-- A morphism of finite etale covers has etale underlying scheme morphism. -/
theorem finiteEtaleCover_hom_etale {X Y : FiniteEtaleCover S} (f : X ⟶ Y) : Etale f.hom.left := by
  haveI hEtY : Etale Y.obj.hom := FiniteEtaleCover.etale_structureMap Y
  haveI hFinY : IsFinite Y.obj.hom := FiniteEtaleCover.finite_structureMap Y
  have hw : f.hom.left ≫ Y.obj.hom = X.obj.hom := Over.w f.hom
  have hcomp : Etale (f.hom.left ≫ Y.obj.hom) := by rw [hw]; exact FiniteEtaleCover.etale_structureMap X
  haveI : Etale (f.hom.left ≫ Y.obj.hom) := hcomp
  exact Etale.of_comp f.hom.left Y.obj.hom

theorem finiteEtaleCover_hom_finite {X Y : FiniteEtaleCover S} (f : X ⟶ Y) : IsFinite f.hom.left := by
  haveI hEtY : Etale Y.obj.hom := FiniteEtaleCover.etale_structureMap Y
  haveI hFinY : IsFinite Y.obj.hom := FiniteEtaleCover.finite_structureMap Y
  have hw : f.hom.left ≫ Y.obj.hom = X.obj.hom := Over.w f.hom
  have hcomp : IsFinite (f.hom.left ≫ Y.obj.hom) := by rw [hw]; exact FiniteEtaleCover.finite_structureMap X
  haveI : IsFinite (f.hom.left ≫ Y.obj.hom) := hcomp
  exact IsFinite.of_comp f.hom.left Y.obj.hom

variable {X Y Z : FiniteEtaleCover S} (f : X ⟶ Z) (g : Y ⟶ Z)

abbrev finiteEtaleCoverPullbackDiagram : WalkingCospan ⥤ Scheme := cospan f.hom.left g.hom.left

def finiteEtaleCoverPullbackNat : finiteEtaleCoverPullbackDiagram f g ⟶ (Functor.const WalkingCospan).obj S where
  app := fun j =>
    match j with
    | none => Z.obj.hom
    | some WalkingPair.left => X.obj.hom
    | some WalkingPair.right => Y.obj.hom
  naturality := by
    intro j j' φ
    cases φ with
    | id => rfl
    | term j =>
        cases j with
        | left =>
            simp
            erw [Category.comp_id]
        | right =>
            simp
            erw [Category.comp_id]

def finiteEtaleCoverPullbackCone : Cone (finiteEtaleCoverPullbackDiagram f g) :=
  PullbackCone.mk (pullback.fst f.hom.left g.hom.left)
    (pullback.snd f.hom.left g.hom.left) pullback.condition

def finiteEtaleCoverPullbackMap : (finiteEtaleCoverPullbackCone f g).pt ⟶ S :=
  pullback.fst f.hom.left g.hom.left ≫ X.obj.hom

def finiteEtaleCoverPullbackCover : FiniteEtaleCover S :=
  FiniteEtaleCover.mk (finiteEtaleCoverPullbackMap f g)
    (by
      rw [finiteEtaleCoverPullbackMap]
      haveI hg : Etale g.hom.left := finiteEtaleCover_hom_etale g
      haveI hX : Etale X.obj.hom := FiniteEtaleCover.etale_structureMap X
      haveI hfst : Etale (pullback.fst f.hom.left g.hom.left) := inferInstance
      exact Etale.etale_comp (f := pullback.fst f.hom.left g.hom.left) (g := X.obj.hom))
    (by
      rw [finiteEtaleCoverPullbackMap]
      haveI hg : IsFinite g.hom.left := finiteEtaleCover_hom_finite g
      haveI hX : IsFinite X.obj.hom := FiniteEtaleCover.finite_structureMap X
      haveI hfst : IsFinite (pullback.fst f.hom.left g.hom.left) := inferInstance
      exact MorphismProperty.comp_mem @IsFinite
        (pullback.fst f.hom.left g.hom.left) X.obj.hom ‹_› ‹_›)

theorem finiteEtaleCoverPullbackCone_condition (j : WalkingCospan) :
    (finiteEtaleCoverPullbackCone f g).π.app j ≫ (finiteEtaleCoverPullbackNat f g).app j = finiteEtaleCoverPullbackMap f g := by
  cases j with
  | none =>
      change (pullback.fst f.hom.left g.hom.left ≫ f.hom.left) ≫ Z.obj.hom =
        pullback.fst f.hom.left g.hom.left ≫ X.obj.hom
      rw [Category.assoc, Over.w f.hom]
  | some j =>
      cases j with
      | left => rfl
      | right =>
          change pullback.snd f.hom.left g.hom.left ≫ Y.obj.hom =
            pullback.fst f.hom.left g.hom.left ≫ X.obj.hom
          rw [← Over.w f.hom, ← Over.w g.hom]
          rw [← Category.assoc, ← Category.assoc, pullback.condition]

def finiteEtaleCoverPullbackCone_isLimit : IsLimit (finiteEtaleCoverPullbackCone f g) :=
  pullbackIsPullback f.hom.left g.hom.left

def finiteEtaleCoverPullbackOverCone : Cone (Over.lift (finiteEtaleCoverPullbackDiagram f g) (finiteEtaleCoverPullbackNat f g)) :=
  Over.liftCone (finiteEtaleCoverPullbackDiagram f g) (finiteEtaleCoverPullbackNat f g) (finiteEtaleCoverPullbackCone f g) (finiteEtaleCoverPullbackMap f g) (finiteEtaleCoverPullbackCone_condition f g)

def finiteEtaleCoverPullbackOverCone_isLimit : IsLimit (finiteEtaleCoverPullbackOverCone f g) :=
  Over.isLimitLiftCone (finiteEtaleCoverPullbackDiagram f g) (finiteEtaleCoverPullbackNat f g) (finiteEtaleCoverPullbackCone f g) (finiteEtaleCoverPullbackMap f g)
    (finiteEtaleCoverPullbackCone_condition f g) (finiteEtaleCoverPullbackCone_isLimit f g)

/-- Reuse the existing actual pullback object; lift its projections directly. -/
def finiteEtaleCoverPullbackFirst : finiteEtaleCoverPullbackCover f g ⟶ X :=
  ⟨Over.homMk (pullback.fst f.hom.left g.hom.left) rfl⟩

def finiteEtaleCoverPullbackSecond : finiteEtaleCoverPullbackCover f g ⟶ Y :=
  ⟨Over.homMk (pullback.snd f.hom.left g.hom.left) (by
    change pullback.snd f.hom.left g.hom.left ≫ Y.obj.hom =
      pullback.fst f.hom.left g.hom.left ≫ X.obj.hom
    rw [← Over.w f.hom, ← Over.w g.hom]
    rw [← Category.assoc, ← Category.assoc, pullback.condition])⟩

theorem finiteEtaleCoverPullbackCondition :
    finiteEtaleCoverPullbackFirst f g ≫ f = finiteEtaleCoverPullbackSecond f g ≫ g := by
  ext1
  apply Over.OverMorphism.ext
  exact pullback.condition

def finiteEtaleCoverPullbackConeInCover : PullbackCone f g :=
  PullbackCone.mk (finiteEtaleCoverPullbackFirst f g) (finiteEtaleCoverPullbackSecond f g)
    (finiteEtaleCoverPullbackCondition f g)

def finiteEtaleCoverPullbackLift (s : PullbackCone f g) :
    s.pt ⟶ finiteEtaleCoverPullbackCover f g :=
  ⟨Over.homMk (pullback.lift s.fst.hom.left s.snd.hom.left
    (congrArg (fun k => k.hom.left) s.condition)) (by
      change (pullback.lift _ _ _) ≫
        (pullback.fst f.hom.left g.hom.left ≫ X.obj.hom) = s.pt.obj.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w s.fst.hom)⟩

def finiteEtaleCoverPullbackIsLimitInCover : IsLimit (finiteEtaleCoverPullbackConeInCover f g) := by
  apply PullbackCone.IsLimit.mk (finiteEtaleCoverPullbackCondition f g) (finiteEtaleCoverPullbackLift f g)
  · intro s
    ext1
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  · intro s
    ext1
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  · intro s m hfirst hsecond
    ext1
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have h := congrArg (fun k => k.hom.left) hfirst
      simpa [finiteEtaleCoverPullbackLift, finiteEtaleCoverPullbackFirst, pullback.lift_fst] using! h
    · have h := congrArg (fun k => k.hom.left) hsecond
      simpa [finiteEtaleCoverPullbackLift, finiteEtaleCoverPullbackSecond, pullback.lift_snd] using! h

theorem finiteEtaleCoverHasPullbacks (S : Scheme.{u}) : HasPullbacks (FiniteEtaleCover S) := by
  haveI : ∀ {X Y Z : FiniteEtaleCover S} {f : X ⟶ Z} {g : Y ⟶ Z},
      HasLimit (cospan f g) := fun {X Y Z f g} =>
        ⟨⟨finiteEtaleCoverPullbackConeInCover f g, finiteEtaleCoverPullbackIsLimitInCover f g⟩⟩
  exact hasPullbacks_of_hasLimit_cospan (FiniteEtaleCover S)

/-- The once-punctured source affine curve cover category has pullbacks. -/
noncomputable instance curveAffineEtaleCovers_hasPullbacks (K : Type u) [Field K] :
    Limits.HasPullbacks (curveAffineEtaleCovers K) :=
  finiteEtaleCoverHasPullbacks (curveScheme K)

/-- The affine curve cover category (alias of the once-punctured source) has
pullbacks. -/
noncomputable instance curveOncePuncturedEtaleCovers_hasPullbacks (K : Type u) [Field K] :
    Limits.HasPullbacks (curveOncePuncturedEtaleCovers K) :=
  finiteEtaleCoverHasPullbacks (curveScheme K)

/-- The two-punctured extra curve cover category has pullbacks. -/
noncomputable instance curveTwoPuncturedEtaleCovers_hasPullbacks (K : Type u) [Field K] :
    Limits.HasPullbacks (curveTwoPuncturedEtaleCovers K) :=
  finiteEtaleCoverHasPullbacks (curveTwoPuncturedScheme K)


/-! ## 3. Actual connectedness facts of the curves -/

/-- The affine curve scheme is connected. -/
theorem curveAffine_connected (K : Type u) [Field K] :
    ConnectedSpace (curveScheme K) :=
  inferInstance

/-- The affine curve scheme is irreducible. -/
theorem curveAffine_irreducible (K : Type u) [Field K] :
    IrreducibleSpace (curveScheme K) :=
  inferInstance

/-- The two-punctured EXTRA curve scheme is connected (not the source). -/
theorem curveTwoPunctured_connected (K : Type u) [Field K] :
    ConnectedSpace (curveTwoPuncturedScheme K) :=
  inferInstance

/-- The two-punctured EXTRA curve scheme is irreducible (not the source). -/
theorem curveTwoPunctured_irreducible (K : Type u) [Field K] :
    IrreducibleSpace (curveTwoPuncturedScheme K) :=
  inferInstance

/-! ## 4. The exact remaining PreGaloisCategory fields -/

/-- Frozen card: the exact remaining PreGaloisCategory field (G2) for
the finite etale cover category of a scheme S.  The terminal field (G1), the
pullback field (G1), the finite coproduct field (G2) and the direct-summand
field (G3) are proved in this file and are not listed.  This is
DATA: no inhabitant is constructed here and no theorem consumes it. -/
structure CurvePreGaloisCategoryRemainingFields (S : Scheme.{u}) where
  /-- Finite étale covers have quotients by finite groups (G2). -/
  hasQuotientsByFiniteGroups : ∀ (G : Type u) [Group G] [Finite G],
    Limits.HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)

/-- The remaining-fields card for the affine curve. -/
abbrev curveAffinePreGaloisRemainingFields (K : Type u) [Field K] : Prop :=
  CurvePreGaloisCategoryRemainingFields (curveScheme K)

/-- The remaining-fields card for the TWO-punctured EXTRA curve E \ {O,P}. -/
abbrev curveTwoPuncturedPreGaloisRemainingFields (K : Type u) [Field K] : Prop :=
  CurvePreGaloisCategoryRemainingFields (curveTwoPuncturedScheme K)

/-- The remaining-fields card is realized.  Frozen source obligation: not
proved here and no consumer. -/
def CurvePreGaloisCategoryRemainingFieldsRealized (S : Scheme.{u}) : Prop :=
  CurvePreGaloisCategoryRemainingFields S

/-- The realized proposition for the punctured curve cover category. -/
def curveTwoPuncturedPreGaloisRemainingFieldsRealized (K : Type u) [Field K] : Prop :=
  CurvePreGaloisCategoryRemainingFieldsRealized (curveTwoPuncturedScheme K)

/-! ## Once-punctured source vs two-punctured extra -/

/-- The terminal cover of the ONCE-punctured source affine curve E \\ {O} is
terminal. -/
noncomputable def curveOncePuncturedTerminalCover_isTerminal (K : Type u) [Field K] :
    Limits.IsTerminal (curveOncePuncturedTerminalCover K) :=
  curveAffineTerminalCover_isTerminal K

/-- The once-punctured source cover category has a terminal object. -/
noncomputable instance curveOncePuncturedEtaleCovers_hasTerminal (K : Type u) [Field K] :
    Limits.HasTerminal (curveOncePuncturedEtaleCovers K) :=
  curveAffineEtaleCovers_hasTerminal K

/-- The once-punctured source affine curve E \\ {O} is connected. -/
theorem curveOncePunctured_connected (K : Type u) [Field K] :
    ConnectedSpace (curveScheme K) :=
  curveAffine_connected K

/-- The once-punctured source affine curve E \\ {O} is irreducible. -/
theorem curveOncePunctured_irreducible (K : Type u) [Field K] :
    IrreducibleSpace (curveScheme K) :=
  curveAffine_irreducible K

end

/-! ## 5. Actual finite coproducts of covers -/

section
variable {S : Scheme.{u}}
variable (X Y : FiniteEtaleCover S)

def binaryCoproductCover : FiniteEtaleCover S :=
  FiniteEtaleCover.mk
    (Limits.coprod.desc (FiniteEtaleCover.structureMap X) (FiniteEtaleCover.structureMap Y))
    (by
      refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale)
        (𝒰 := coprodOpenCover.{u, 0} X.carrier Y.carrier)).mpr ?_
      intro i
      cases i with
      | inl u =>
          obtain rfl : u = PUnit.unit := Subsingleton.elim _ _
          change Etale (Limits.coprod.inl ≫ Limits.coprod.desc
            (FiniteEtaleCover.structureMap X) (FiniteEtaleCover.structureMap Y))
          rw [Limits.coprod.inl_desc]
          exact FiniteEtaleCover.etale_structureMap X
      | inr u =>
          obtain rfl : u = PUnit.unit := Subsingleton.elim _ _
          change Etale (Limits.coprod.inr ≫ Limits.coprod.desc
            (FiniteEtaleCover.structureMap X) (FiniteEtaleCover.structureMap Y))
          rw [Limits.coprod.inr_desc]
          exact FiniteEtaleCover.etale_structureMap Y)
    (by
      haveI hX : IsFinite (FiniteEtaleCover.structureMap X) :=
        FiniteEtaleCover.finite_structureMap X
      haveI hY : IsFinite (FiniteEtaleCover.structureMap Y) :=
        FiniteEtaleCover.finite_structureMap Y
      infer_instance)

def binaryCoproductInl : X ⟶ binaryCoproductCover X Y :=
  ⟨Over.homMk (show X.obj.left ⟶ (binaryCoproductCover X Y).obj.left from Limits.coprod.inl) (by
    change Limits.coprod.inl ≫ Limits.coprod.desc (FiniteEtaleCover.structureMap X)
      (FiniteEtaleCover.structureMap Y) = FiniteEtaleCover.structureMap X
    rw [Limits.coprod.inl_desc])⟩

def binaryCoproductInr : Y ⟶ binaryCoproductCover X Y :=
  ⟨Over.homMk (show Y.obj.left ⟶ (binaryCoproductCover X Y).obj.left from Limits.coprod.inr) (by
    change Limits.coprod.inr ≫ Limits.coprod.desc (FiniteEtaleCover.structureMap X)
      (FiniteEtaleCover.structureMap Y) = FiniteEtaleCover.structureMap Y
    rw [Limits.coprod.inr_desc])⟩

def binaryCoproductCocone : BinaryCofan X Y :=
  BinaryCofan.mk (binaryCoproductInl X Y) (binaryCoproductInr X Y)

def binaryCoproductDescHom {T : FiniteEtaleCover S}
    (f : X ⟶ T) (g : Y ⟶ T) : binaryCoproductCover X Y ⟶ T :=
  ⟨Over.homMk (Limits.coprod.desc f.hom.left g.hom.left) (by
    change Limits.coprod.desc f.hom.left g.hom.left ≫ T.obj.hom =
      Limits.coprod.desc (FiniteEtaleCover.structureMap X) (FiniteEtaleCover.structureMap Y)
    apply Limits.coprod.hom_ext
    · rw [← Category.assoc, Limits.coprod.inl_desc]
      simp only [FiniteEtaleCover.structureMap]
      erw [Limits.coprod.inl_desc]
      exact Over.w f.hom
    · rw [← Category.assoc, Limits.coprod.inr_desc]
      simp only [FiniteEtaleCover.structureMap]
      erw [Limits.coprod.inr_desc]
      exact Over.w g.hom)⟩


def binaryCoproductIsColimit : IsColimit (binaryCoproductCocone X Y) :=
  BinaryCofan.IsColimit.mk (binaryCoproductCocone X Y)
    (fun {T} f g => binaryCoproductDescHom X Y f g)
    (by
      intro T f g
      ext1
      apply Over.OverMorphism.ext
      exact Limits.coprod.inl_desc _ _)
    (by
      intro T f g
      ext1
      apply Over.OverMorphism.ext
      exact Limits.coprod.inr_desc _ _)
    (by
      intro T f g m hm1 hm2
      ext1
      apply Over.OverMorphism.ext
      apply Limits.coprod.hom_ext
      · have h := congrArg (fun k => k.hom.left) hm1
        simp only [binaryCoproductCocone, binaryCoproductInl, BinaryCofan.mk_inl,
          Over.homMk_left, binaryCoproductDescHom, FiniteEtaleCover.carrier,
          Limits.coprod.inl_desc] at h ⊢
        exact h
      · have h := congrArg (fun k => k.hom.left) hm2
        simp only [binaryCoproductCocone, binaryCoproductInr, BinaryCofan.mk_inr,
          Over.homMk_left, binaryCoproductDescHom, FiniteEtaleCover.carrier,
          Limits.coprod.inr_desc] at h ⊢
        exact h)



noncomputable instance finiteEtaleCover_hasBinaryCoproduct (X Y : FiniteEtaleCover S) :
    HasBinaryCoproduct X Y :=
  ⟨⟨binaryCoproductCocone X Y, binaryCoproductIsColimit X Y⟩⟩

noncomputable instance finiteEtaleCover_hasBinaryCoproducts :
    HasBinaryCoproducts (FiniteEtaleCover S) := by
  haveI : ∀ {X Y : FiniteEtaleCover S}, HasColimit (pair X Y) :=
    fun {X Y} => finiteEtaleCover_hasBinaryCoproduct X Y
  exact hasBinaryCoproducts_of_hasColimit_pair (FiniteEtaleCover S)

def initialCover : FiniteEtaleCover S :=
  FiniteEtaleCover.mk (initial.to S) inferInstance inferInstance

noncomputable def initialCoverIsInitial : IsInitial (initialCover (S := S)) := by
  haveI : ∀ X : FiniteEtaleCover S, Unique (initialCover (S := S) ⟶ X) := by
    intro X
    refine ⟨⟨ObjectProperty.homMk (Over.homMk (initial.to X.obj.left) ?_)⟩, ?_⟩
    · exact initial.hom_ext _ _
    · intro a
      apply ObjectProperty.hom_ext
      apply CommaMorphism.ext
      · exact initial.hom_ext _ _
      · exact Subsingleton.elim _ _
  exact IsInitial.ofUnique _

noncomputable instance finiteEtaleCover_hasInitial : HasInitial (FiniteEtaleCover S) :=
  initialCoverIsInitial.hasInitial

noncomputable instance finiteEtaleCover_hasFiniteCoproducts :
    HasFiniteCoproducts (FiniteEtaleCover S) :=
  hasFiniteCoproducts_of_has_binary_and_initial


end

/-! ## 6. Actual monomorphism lifting and clopen image for cover monomorphisms -/

section
variable {S : Scheme.{u}} {X Y : FiniteEtaleCover S}

/-- Actual mono lifting via the pullback diagonal criterion: a monomorphism of
finite etale covers has a monomorphic underlying scheme morphism. -/
theorem finiteEtaleCover_mono_hom_left_of_mono (i : X ⟶ Y) [Mono i] : Mono i.hom.left := by
  haveI hc : IsIso (finiteEtaleCoverPullbackConeInCover i i).fst :=
    (mono_iff_isIso_fst (finiteEtaleCoverPullbackIsLimitInCover i i)).mp inferInstance
  haveI hmap : IsIso ((Over.forget S).map
      ((FiniteEtaleCover.forgetOver S).map (finiteEtaleCoverPullbackConeInCover i i).fst)) :=
    inferInstance
  haveI hiso : IsIso (pullback.fst i.hom.left i.hom.left) := by
    have heq : ((Over.forget S).map
        ((FiniteEtaleCover.forgetOver S).map (finiteEtaleCoverPullbackConeInCover i i).fst)) =
        pullback.fst i.hom.left i.hom.left := rfl
    rw [heq] at hmap
    exact hmap
  exact (mono_iff_isIso_fst (pullback.isLimit i.hom.left i.hom.left)).mpr hiso

/-- Actual mono lifting to the underlying over-morphism. -/
theorem finiteEtaleCover_mono_hom_of_mono (i : X ⟶ Y) [Mono i] : Mono i.hom := by
  haveI : Mono i.hom.left := finiteEtaleCover_mono_hom_left_of_mono i
  exact Over.mono_of_mono_left i.hom

/-- A monomorphism of finite etale covers is an open immersion on underlying schemes. -/
theorem finiteEtaleCover_mono_hom_left_isOpenImmersion_of_mono (i : X ⟶ Y) [Mono i] :
    IsOpenImmersion i.hom.left := by
  haveI : Mono i.hom.left := finiteEtaleCover_mono_hom_left_of_mono i
  haveI : Etale i.hom.left := finiteEtaleCover_hom_etale i
  exact IsOpenImmersion.of_flat_of_mono i.hom.left

/-- The image of a cover monomorphism on underlying schemes is clopen. -/
theorem finiteEtaleCover_mono_hom_left_range_isClopen_of_mono (i : X ⟶ Y) [Mono i] :
    IsClopen (Set.range i.hom.left.base) := by
  haveI : Mono i.hom.left := finiteEtaleCover_mono_hom_left_of_mono i
  haveI : Etale i.hom.left := finiteEtaleCover_hom_etale i
  haveI hopen : IsOpenImmersion i.hom.left :=
    finiteEtaleCover_mono_hom_left_isOpenImmersion_of_mono i
  haveI hfin : IsFinite i.hom.left := finiteEtaleCover_hom_finite i
  haveI hprop : IsProper i.hom.left := inferInstance
  exact ⟨(Scheme.Hom.isClosedMap i.hom.left).isClosed_range, hopen.isOpen_range⟩

end

/-! ## 7. Clopen complement open subscheme of a cover monomorphism -/

section
variable {S : Scheme.{u}} {X Y : FiniteEtaleCover S} (i : X ⟶ Y) [Mono i]

/-- The image open subscheme of a cover monomorphism. -/
def finiteEtaleCoverMonoImageOpens : (Y.carrier).Opens :=
  ⟨Set.range i.hom.left.base,
    (finiteEtaleCover_mono_hom_left_isOpenImmersion_of_mono i).isOpen_range⟩

/-- The clopen complement open subscheme of the image of a cover monomorphism. -/
def finiteEtaleCoverMonoComplementOpens : (Y.carrier).Opens :=
  ⟨(finiteEtaleCoverMonoImageOpens i : Set (Y.carrier))ᶜ,
    ((finiteEtaleCover_mono_hom_left_range_isClopen_of_mono i).isClosed).isOpen_compl⟩

/-- The complement as an actual scheme. -/
abbrev finiteEtaleCoverMonoComplementScheme : Scheme :=
  (finiteEtaleCoverMonoComplementOpens i).toScheme

/-- The structure morphism of the complement to the base S. -/
def finiteEtaleCoverMonoComplementStructureMap :
    finiteEtaleCoverMonoComplementScheme i ⟶ S :=
  (finiteEtaleCoverMonoComplementOpens i).ι ≫ FiniteEtaleCover.structureMap Y

/-- The complement open subscheme has etale structure morphism to S. -/
theorem finiteEtaleCoverMonoComplementStructureMap_etale :
    Etale (finiteEtaleCoverMonoComplementStructureMap i) := by
  haveI : Etale ((finiteEtaleCoverMonoComplementOpens i).ι) := inferInstance
  haveI : Etale (FiniteEtaleCover.structureMap Y) :=
    FiniteEtaleCover.etale_structureMap Y
  exact Etale.etale_comp (f := (finiteEtaleCoverMonoComplementOpens i).ι)
    (g := FiniteEtaleCover.structureMap Y)

end

/-! ## 8. The clopen complement is an actual finite etale cover -/

section
variable {S : Scheme.{u}} {X Y : FiniteEtaleCover S} (i : X ⟶ Y) [Mono i]

/-- The structure morphism of the clopen complement is finite: the complement open
subscheme is clopen in Y and Y is finite over S. -/
theorem finiteEtaleCoverMonoComplementStructureMap_isFinite :
    IsFinite (finiteEtaleCoverMonoComplementStructureMap i) := by
  have himg : IsClopen (finiteEtaleCoverMonoImageOpens i : Set (Y.carrier)) :=
    finiteEtaleCover_mono_hom_left_range_isClopen_of_mono i
  have hcompl : IsClopen (finiteEtaleCoverMonoComplementOpens i : Set (Y.carrier)) :=
    ⟨himg.isOpen.isClosed_compl, himg.isClosed.isOpen_compl⟩
  exact @LeanFormal.IUT.Foundations.Geometry.ClopenFiniteComplement.isFinite_opens_ι_comp_of_isClopen
    _ _ (FiniteEtaleCover.structureMap Y) (FiniteEtaleCover.finite_structureMap Y)
    (finiteEtaleCoverMonoComplementOpens i) hcompl

/-- The clopen complement as an actual finite etale cover of S. -/
def finiteEtaleCoverMonoComplementCover : FiniteEtaleCover S :=
  FiniteEtaleCover.mk (finiteEtaleCoverMonoComplementStructureMap i)
    (finiteEtaleCoverMonoComplementStructureMap_etale i)
    (finiteEtaleCoverMonoComplementStructureMap_isFinite i)

/-- The canonical inclusion of the clopen complement cover into Y. -/
def finiteEtaleCoverMonoComplementInclusion :
    finiteEtaleCoverMonoComplementCover i ⟶ Y :=
  ⟨Over.homMk (finiteEtaleCoverMonoComplementOpens i).ι (by
    change (finiteEtaleCoverMonoComplementOpens i).ι ≫
      FiniteEtaleCover.structureMap Y =
      finiteEtaleCoverMonoComplementStructureMap i
    rfl)⟩

end

/-! ## 9. The clopen complement gives the direct-summand coproduct decomposition -/

section
variable {S : Scheme.{u}} {X Y : FiniteEtaleCover S} (i : X ⟶ Y) [Mono i]

theorem finiteEtaleCoverMonoComplement_isCompl :
    IsCompl (show Y.obj.left.Opens from finiteEtaleCoverMonoImageOpens i)
      (show Y.obj.left.Opens from finiteEtaleCoverMonoComplementOpens i) := by
  let V : Y.obj.left.Opens := finiteEtaleCoverMonoImageOpens i
  let U : Y.obj.left.Opens := finiteEtaleCoverMonoComplementOpens i
  change IsCompl V U
  constructor
  · rw [disjoint_iff]
    ext x
    constructor
    · intro hx
      exact hx.2 hx.1
    · intro hx
      exact absurd hx (by simp)
  · rw [codisjoint_iff]
    ext x
    change (x ∈ (V : Set Y.obj.left) ∨ x ∈ (U : Set Y.obj.left)) ↔
      x ∈ (Set.univ : Set Y.obj.left)
    simp only [Set.mem_univ, iff_true]
    rcases em (x ∈ (V : Set Y.obj.left)) with hx | hx
    · exact Or.inl hx
    · refine Or.inr ?_
      show x ∈ (U : Set Y.obj.left)
      change x ∈ ((V : Set Y.obj.left)ᶜ)
      exact hx

theorem finiteEtaleCoverMonoComplement_schemeCofan_isColimit :
    Nonempty (IsColimit (BinaryCofan.mk i.hom.left
      (finiteEtaleCoverMonoComplementOpens i).ι)) := by
  let f := i.hom.left
  let g : (finiteEtaleCoverMonoComplementOpens i).toScheme ⟶ Y.obj.left :=
    (finiteEtaleCoverMonoComplementOpens i).ι
  haveI hf : IsOpenImmersion f :=
    finiteEtaleCover_mono_hom_left_isOpenImmersion_of_mono i
  haveI hg : IsOpenImmersion g := by
    change IsOpenImmersion (finiteEtaleCoverMonoComplementOpens i).ι
    exact Scheme.Opens.instIsOpenImmersionι (finiteEtaleCoverMonoComplementOpens i)
  let V : Y.obj.left.Opens := finiteEtaleCoverMonoImageOpens i
  let U : Y.obj.left.Opens := finiteEtaleCoverMonoComplementOpens i
  have h1 : @Scheme.Hom.opensRange _ _ f hf = V := TopologicalSpace.Opens.ext rfl
  have h2 : @Scheme.Hom.opensRange _ _ g hg = U := by
    apply TopologicalSpace.Opens.ext
    exact Scheme.Opens.range_ι (finiteEtaleCoverMonoComplementOpens i)
  have hcompl : IsCompl (@Scheme.Hom.opensRange _ _ f hf)
      (@Scheme.Hom.opensRange _ _ g hg) := by
    change IsCompl V (@Scheme.Hom.opensRange _ _ g hg)
    rw [h2]
    simpa [V, U] using finiteEtaleCoverMonoComplement_isCompl i
  exact @nonempty_isColimit_binaryCofanMk_of_isCompl _ _ _ f g hf hg hcompl

def finiteEtaleCoverMonoComplementBinaryCofan :
    BinaryCofan X (finiteEtaleCoverMonoComplementCover i) :=
  BinaryCofan.mk i (finiteEtaleCoverMonoComplementInclusion i)

noncomputable def finiteEtaleCoverMonoComplement_binaryCofan_isColimit :
    IsColimit (finiteEtaleCoverMonoComplementBinaryCofan i) := by
  let hcScheme := Classical.choice (finiteEtaleCoverMonoComplement_schemeCofan_isColimit i)
  let gmap : (finiteEtaleCoverMonoComplementCover i).obj.left ⟶ Y.obj.left :=
    (finiteEtaleCoverMonoComplementInclusion i).hom.left
  let desc : ∀ {T : FiniteEtaleCover S},
      (X ⟶ T) → (finiteEtaleCoverMonoComplementCover i ⟶ T) → (Y ⟶ T) :=
    fun {T} f g => by
      let d : Y.obj.left ⟶ T.obj.left :=
        BinaryCofan.IsColimit.desc hcScheme f.hom.left g.hom.left
      have hcomp : d ≫ T.obj.hom = Y.obj.hom := by
        apply hcScheme.hom_ext
        intro j
        rcases j with ⟨j⟩
        cases j with
        | left =>
            change i.hom.left ≫ (d ≫ T.obj.hom) = i.hom.left ≫ Y.obj.hom
            have hfac : i.hom.left ≫ d = f.hom.left := by
              dsimp only [d]
              have h := BinaryCofan.IsColimit.inl_desc hcScheme f.hom.left g.hom.left
              rw [BinaryCofan.mk_inl] at h
              exact h
            rw [← Category.assoc, hfac]
            exact (Over.w f.hom).trans (Over.w i.hom).symm
        | right =>
            change gmap ≫ (d ≫ T.obj.hom) = gmap ≫ Y.obj.hom
            have hfac : gmap ≫ d = g.hom.left := by
              dsimp only [d, gmap]
              have h := BinaryCofan.IsColimit.inr_desc hcScheme f.hom.left g.hom.left
              rw [BinaryCofan.mk_inr] at h
              exact h
            rw [← Category.assoc, hfac]
            exact (Over.w g.hom).trans (by rfl)
      exact ⟨Over.homMk d hcomp⟩
  refine BinaryCofan.IsColimit.mk (finiteEtaleCoverMonoComplementBinaryCofan i)
    desc ?_ ?_ ?_
  · intro T f g
    ext1
    apply Over.OverMorphism.ext
    change i.hom.left ≫ (desc f g).hom.left = f.hom.left
    exact BinaryCofan.IsColimit.inl_desc hcScheme f.hom.left g.hom.left
  · intro T f g
    ext1
    apply Over.OverMorphism.ext
    change gmap ≫ (desc f g).hom.left = g.hom.left
    exact BinaryCofan.IsColimit.inr_desc hcScheme f.hom.left g.hom.left
  · intro T f g m hm1 hm2
    ext1
    apply Over.OverMorphism.ext
    apply BinaryCofan.IsColimit.hom_ext hcScheme
    · have hbinl : (finiteEtaleCoverMonoComplementBinaryCofan i).inl = i := rfl
      have hm1' : i.hom.left ≫ Over.Hom.left m.hom = f.hom.left := by
        have h := congrArg (fun k => Over.Hom.left k.hom) hm1
        rw [hbinl] at h
        exact h
      have h := hcScheme.fac (BinaryCofan.mk f.hom.left g.hom.left)
        (Discrete.mk WalkingPair.left)
      change (BinaryCofan.mk (Over.Hom.left i.hom)
          (finiteEtaleCoverMonoComplementOpens i).ι).inl ≫
          hcScheme.desc (BinaryCofan.mk f.hom.left g.hom.left) =
        (BinaryCofan.mk f.hom.left g.hom.left).inl at h
      rw [BinaryCofan.mk_inl, BinaryCofan.mk_inl] at h
      dsimp [BinaryCofan.mk] at h
      exact hm1'.trans (by
        change Over.Hom.left f.hom = Over.Hom.left i.hom ≫
          hcScheme.desc (BinaryCofan.mk f.hom.left g.hom.left)
        exact h.symm)
    · have hbinr : (finiteEtaleCoverMonoComplementBinaryCofan i).inr =
          finiteEtaleCoverMonoComplementInclusion i := rfl
      have hm2' : gmap ≫ Over.Hom.left m.hom = g.hom.left := by
        have h := congrArg (fun k => Over.Hom.left k.hom) hm2
        rw [hbinr] at h
        exact h
      have h := hcScheme.fac (BinaryCofan.mk f.hom.left g.hom.left)
        (Discrete.mk WalkingPair.right)
      change (BinaryCofan.mk (Over.Hom.left i.hom)
          (finiteEtaleCoverMonoComplementOpens i).ι).inr ≫
          hcScheme.desc (BinaryCofan.mk f.hom.left g.hom.left) =
        (BinaryCofan.mk f.hom.left g.hom.left).inr at h
      rw [BinaryCofan.mk_inr, BinaryCofan.mk_inr] at h
      dsimp [BinaryCofan.mk] at h
      exact hm2'.trans (by
        change Over.Hom.left g.hom = (finiteEtaleCoverMonoComplementOpens i).ι ≫
          hcScheme.desc (BinaryCofan.mk f.hom.left g.hom.left)
        exact h.symm)


/-- Every monomorphism of finite etale covers induces an isomorphism on a direct
summand: Y is the binary coproduct of X and the clopen complement of the image. -/
theorem finiteEtaleCover_monoInducesIsoOnDirectSummand
    (i : X ⟶ Y) [Mono i] :
    ∃ (Z : FiniteEtaleCover S) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u)) :=
  ⟨finiteEtaleCoverMonoComplementCover i,
    finiteEtaleCoverMonoComplementInclusion i,
    ⟨by
      simpa [finiteEtaleCoverMonoComplementBinaryCofan] using
        finiteEtaleCoverMonoComplement_binaryCofan_isColimit i⟩⟩

end

end Example36
end LeanFormal.IUT.IUTII.Frobenioid