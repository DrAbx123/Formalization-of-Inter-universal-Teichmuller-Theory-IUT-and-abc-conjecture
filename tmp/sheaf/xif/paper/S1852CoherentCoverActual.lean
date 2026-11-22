/-
# S1852: the coherent (strong) cover datum, and S1756FirstMissing on it

## The question

S1850 proved `¬ S1756FirstMissing` for the *recorded* cover type `S1728Cover`:
the weak base-change datum of `EtaleStackRepresentableMorphismProperty` allows a
`doubled` presentation (`S1850Doubled`) of the identity map, whose identity-point
self-endomorphism `S1756End` is `fold ; inl`, not the identity.  The diagnosis of
S1850 is that the recorded datum is too weak: `EtalePseudofunctorSquare.TwoPullbackWitness`
records a lift, the two comparison 2-cells, the action on cone morphisms and
2-cell extensionality, but not the *full* 2-universal property of a bicategorical
pullback.  S1827/S1784 isolated the exact missing half: essential surjectivity of
the cone comparison `Hom(W, P) ⟶ Cone(W)` on 1-cells.

This file *strengthens the cover datum* without changing any recorded definition:
the existing `EtaleStackBaseChangePresentation`, `EtalePseudofunctorSquare`,
`TwoPullbackWitness`, `EtaleStackFiniteEtaleMorphism`, `S1728Cover`,`S1756End`,
`S1756Unit` and `S1756FirstMissing` are untouched; the strong versions are new
structures in this module.

## What is built here

1. `S1852WeakSquare`: the 2-commutative square attached to a weak presentation,
   definitionally equal to `S1743Square` at the identity point
   (`S1852WeakSquare_S1743`, by `rfl`).

2. `S1852ConeEssSurj P`: **the full 2-universal property** of a base-change
   presentation `P`, stated for arbitrary test points as cone-comparison
   essential surjectivity: a 1-cell into the pullback whose two projections are
   2-isomorphic to a cone's projections is 2-isomorphic to the cone's lift.
   At the identity point this is *exactly* S1784/S1827's missing half
   (`S1852ConeEssSurj_iff_S1784`, by `rfl`), hence exactly the missing unit
   (`S1852ConeEssSurj_iff_unit`, `S1852ConeEssSurj_iff_end`).

3. `StrongEtaleStackBaseChangePresentation`: the weak presentation together with
   `S1852ConeEssSurj`; and `StrongEtaleStackFiniteEtaleMorphism`, the strong
   analogue of `EtaleStackFiniteEtaleMorphism`, whose forgetful map
   `StrongEtaleStackFiniteEtaleMorphism.toWeak` lands in the recorded weak
   structure (definitionally, on each base change).

4. `StrongCover` and the **coherent cover datum** `CoherentCover`: a cover whose
   structure map carries a strong finite-etale structure and whose identity-point
   presentation carries the S1756 unit 2-cell.  The unit is *not* an assumption:
   `CoherentCover.ofStrong` derives it from the full 2-universal property
   (`S1852Unit_of_strong`).

5. **The identity/terminal cover is strong**: `S1852IdStrongBc` proves the full
   2-universal property of the canonical identity-point square of
   `𝟙 X.stack` at *every* test scheme and point (the lift is the cone's second
   leg, so the comparison is immediate), `S1852IdStrong` makes the identity map
   strongly finite etale, and `S1852TerminalStrong`/`S1852TerminalCoherent` are
   the coherent terminal cover.  Its model is `Spec R'` by `rfl`
   (`S1852TerminalModel`) and its self-endomorphism is the identity
   (`S1852TerminalEnd`).

6. **S1756FirstMissing on the coherent covers**
   (`S1852FirstMissingOnCoherent`): for every coherent cover,
   `S1756End A = 𝟙 (S1733Model A)`.  The proof goes through the full
   2-universal property, not through the unit field: `S1852End_eq_one_of_strong`
   applies S1784's `S1784End_eq_one_of_liftEssSurj` to the identity-point
   presentation of the strong structure.

7. **The exact first missing** (`S1852FirstMissing`): every cover's identity-point
   presentation satisfies the full 2-universal property.  It is equivalent to
   `S1756FirstMissing` (`S1852FirstMissing_iff_S1756`), hence false on the
   recorded cover type (`S1852NotFirstMissing`, from S1850) — the strong datum is
   strictly stronger than the recorded one.

8. **The strengthening excludes the counterexample**
   (`S1852Doubled_not_coneEssSurj`): the doubled presentation of S1850 fails the
   full 2-universal property.  The cone `(q, 𝟙)` over the doubled square has both
   `inl` and `inr` as lifts; essential surjectivity would make them 2-isomorphic,
   and 2-Yoneda evaluation would force `inl = inr`, contradicting the disjointness
   of the coproduct inclusions over the nonempty base.  Consequently no strong
   finite-etale structure forgets to S1850's doubled one
   (`S1852Doubled_not_strong`) and the doubled cover is not coherent
   (`S1852DoubledCover_not_coherent`).

## Honest boundary

* No existing definition is modified.  The recorded `S1728Cover` still satisfies
  `¬ S1756FirstMissing`; the coherent covers form a strictly smaller datum.
* `S1852FirstMissing_of_coherentAll` records the only implication proved:
  coherence of every cover would give `S1756FirstMissing`.  The converse
  (constructing strong presentations at all test points from the identity-point
  unit) is not proved here, and is not claimed.
* The coherent datum is *not* shown to exhaust the covers: the exact first
  missing is `S1852FirstMissing`, which is refuted on `S1728Cover` and satisfied
  on the coherent covers.  What this file proves is that the failure of S1756 is
  exactly the failure of the full 2-universal property, and that adding it is
  consistent: the terminal cover is coherent and all coherent covers satisfy
  S1756.
* No category structure on the coherent covers is constructed (the recorded
  `Category` on `S1728Cover` is a 2-isomorphism quotient built in S1728/S1736);
  the coherent covers are a structure type with a forgetful map to `S1728Cover`.
* No sorry, no axiom, no fake 2-cell.  Only `propext`, `Classical.choice` and
  `Quot.sound`; see the audit block.
-/

import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S1762CoverLimitsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1845AlgEndActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual

universe u

/-! ## 1. The square of a base-change presentation -/

/-- The 2-commutative square attached to a weak base-change presentation.  Its
four objects are the representable stack of the pullback scheme, the cover
source, the representable stack of the test scheme and the target stack. -/
noncomputable def S1852WeakSquare
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F}
    {map : source.Hom target}
    {testScheme : SchemeOverField F}
    {point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F testScheme) target.fiber}
    (P : EtaleStackBaseChangePresentation map testScheme point) :
    EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor F P.pullbackScheme)
      source.fiber (schemeRepresentableEtalePseudofunctor F testScheme) target.fiber :=
  EtalePseudofunctorSquare.mk P.toSource P.projectionMap.transformation map point P.commutes

/-- At the identity point of a cover this square is literally S1743's square. -/
theorem S1852WeakSquare_S1743 (A : S1728Cover) :
    S1852WeakSquare (S1743BaseChange A) = S1743Square A := rfl

/-! ## 2. The full 2-universal property -/

/-- **The full 2-universal property of a base-change presentation.**

For every cone `c` over the square and every 1-cell `f` into the pullback whose
two projections are 2-isomorphic to the cone's projections, `f` is 2-isomorphic
to the cone's lift.  Together with the recorded `TwoPullbackWitness` (which
supplies the lift, the two comparison 2-cells, the action on cone morphisms and
2-cell extensionality) this is the bicategorical pullback property: the cone
comparison `Hom(W, P) ⟶ Cone(W)` is essentially surjective on 1-cells. -/
def S1852ConeEssSurj
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F}
    {map : source.Hom target}
    {testScheme : SchemeOverField F}
    {point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F testScheme) target.fiber}
    (P : EtaleStackBaseChangePresentation map testScheme point) : Prop :=
  ∀ (W : EtaleStackPseudofunctor F) (c : (S1852WeakSquare P).Cone W)
    (f : Pseudofunctor.StrongTrans W
      (schemeRepresentableEtalePseudofunctor F P.pullbackScheme)),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f (S1852WeakSquare P).toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f (S1852WeakSquare P).toY) c.toY) →
        Nonempty (Iso f (P.isPullback.lift W c))

/-- At the identity point the full 2-universal property is literally S1784/S1827's
missing half of the universal property. -/
theorem S1852ConeEssSurj_iff_S1784 (A : S1728Cover) :
    S1852ConeEssSurj (S1743BaseChange A) ↔ S1784LiftEssSurj A := Iff.rfl

/-- The full 2-universal property gives the missing unit 2-cell. -/
theorem S1852Unit_of_coneEssSurj (A : S1728Cover)
    (h : S1852ConeEssSurj (S1743BaseChange A)) : S1756Unit A := by
  refine (S1804LiftEssSurj_iff_unit A).mp ?_
  exact h

/-- The full 2-universal property gives the identity self-endomorphism of the
affine model, i.e. S1756's first missing statement for that cover. -/
theorem S1852End_eq_one_of_coneEssSurj (A : S1728Cover)
    (h : S1852ConeEssSurj (S1743BaseChange A)) : S1756End A = 𝟙 (S1733Model A) :=
  S1784End_eq_one_of_liftEssSurj A h

/-- The exact first missing statement for the *strong* route: every cover's
identity-point presentation satisfies the full 2-universal property. -/
def S1852FirstMissing : Prop := ∀ A : S1728Cover, S1852ConeEssSurj (S1743BaseChange A)

/-- Said statement is exactly S1756's first missing statement. -/
theorem S1852FirstMissing_iff_S1756 : S1852FirstMissing ↔ S1756FirstMissing := by
  constructor
  · intro h A
    exact S1852End_eq_one_of_coneEssSurj A (h A)
  · intro h A
    exact (S1804LiftEssSurj_iff_unit A).mpr ((S1756Unit_iff_end A).mpr (h A))

/-- Consequently the strong route's first missing statement is false on the
recorded cover type: S1850's doubled presentation refutes it. -/
theorem S1852NotFirstMissing : ¬ S1852FirstMissing :=
  fun h => S1850_not_firstMissing (S1852FirstMissing_iff_S1756.mp h)

/-! ## 3. Strong presentations and strong finite-etale morphisms -/

/-- **A strong base-change presentation**: the recorded weak presentation together
with the full 2-universal property of its square.  The recorded structure
`EtaleStackBaseChangePresentation` is not modified; it is a field. -/
structure StrongEtaleStackBaseChangePresentation
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F}
    (map : source.Hom target)
    (testScheme : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F testScheme) target.fiber) where
  /-- The underlying recorded weak presentation. -/
  toWeak : EtaleStackBaseChangePresentation map testScheme point
  /-- **The full 2-universal property**: the cone comparison is essentially
  surjective on 1-cells. -/
  coneEssSurj : S1852ConeEssSurj toWeak

/-- **A strong finite-etale morphism of etale stacks**: every base change carries
a strong presentation and the projection is finite and etale.  This is the strong
analogue of `EtaleStackFiniteEtaleMorphism`, which is a field of the recorded
cover type and is left untouched. -/
structure StrongEtaleStackFiniteEtaleMorphism
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F} (map : source.Hom target) where
  /-- A strong presentation at every test scheme and point. -/
  baseChange : ∀ (testScheme : SchemeOverField F)
      (point : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F testScheme) target.fiber),
    StrongEtaleStackBaseChangePresentation map testScheme point
  /-- The projection is finite and etale. -/
  hasProperty : ∀ (testScheme : SchemeOverField F)
      (point : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F testScheme) target.fiber),
    IsFinite ((baseChange testScheme point).toWeak.projection.left) ∧
      Etale ((baseChange testScheme point).toWeak.projection.left)

/-- Forget the full 2-universal property: every strong structure has an underlying
recorded finite-etale structure, with *the same* base-change presentations. -/
noncomputable def StrongEtaleStackFiniteEtaleMorphism.toWeak
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F} {map : source.Hom target}
    (M : StrongEtaleStackFiniteEtaleMorphism map) :
    EtaleStackFiniteEtaleMorphism map where
  baseChange testScheme point := (M.baseChange testScheme point).toWeak
  hasProperty testScheme point := M.hasProperty testScheme point

@[simp] theorem StrongEtaleStackFiniteEtaleMorphism.toWeak_baseChange
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F} {map : source.Hom target}
    (M : StrongEtaleStackFiniteEtaleMorphism map)
    (testScheme : SchemeOverField F)
    (point : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F testScheme) target.fiber) :
    (M.toWeak.baseChange testScheme point : EtaleStackBaseChangePresentation
        map testScheme point) =
      (M.baseChange testScheme point).toWeak := rfl

/-! ## 4. Strong and coherent covers -/

/-- A cover together with a strong finite-etale structure on its structure map. -/
structure StrongCover {F : Type u} [Field F] (X : HyperbolicOrbicurve F) where
  /-- The source stack of the cover. -/
  source : EtaleStackOverField F
  /-- The structure map to the orbicurve. -/
  map : source.Hom X.stack
  /-- Its strong finite-etale structure. -/
  finiteEtale : StrongEtaleStackFiniteEtaleMorphism map

/-- The recorded (weak) cover underlying a strong cover.  Its finite-etale
structure is the forgetful image, so its identity-point presentation is the same
`EtaleStackBaseChangePresentation` term. -/
noncomputable def StrongCover.cover {F : Type u} [Field F]
    {X : HyperbolicOrbicurve F} (A : StrongCover X) :
    OrbicurveFiniteEtaleCover X where
  source := A.source
  map := A.map
  finiteEtale := A.finiteEtale.toWeak

/-- A strong cover satisfies S1756's first missing statement: the full
2-universal property at the identity point forces the self-endomorphism of the
affine model to be the identity. -/
theorem S1852End_eq_one_of_strong (A : StrongCover S1726Orbicurve) :
    S1756End A.cover = 𝟙 (S1733Model A.cover) :=
  S1852End_eq_one_of_coneEssSurj A.cover
    (A.finiteEtale.baseChange S1726AffineOver S1733BasePoint).coneEssSurj

/-- Consequently a strong cover carries the missing unit 2-cell. -/
theorem S1852Unit_of_strong (A : StrongCover S1726Orbicurve) :
    S1756Unit A.cover :=
  (S1756Unit_iff_end A.cover).mpr (S1852End_eq_one_of_strong A)

/-- **The coherent cover datum.**  A cover whose structure map carries a strong
finite-etale structure, together with the S1756 unit 2-cell at the identity
point.  The unit is a *field* so that S1756's first missing statement holds on
this datum by construction, but it is not an extra assumption: every strong cover
is coherent, with the unit derived from the full 2-universal property
(`CoherentCover.ofStrong`). -/
structure CoherentCover extends StrongCover S1726Orbicurve where
  /-- The missing unit 2-cell `toSource ≫ lift ≅ 𝟙`. -/
  unit : S1756Unit (StrongCover.cover toStrongCover)

/-- Every strong cover is coherent: the unit 2-cell is a consequence of the full
2-universal property, not an assumption. -/
noncomputable def CoherentCover.ofStrong (A : StrongCover S1726Orbicurve) :
    CoherentCover where
  toStrongCover := A
  unit := S1852Unit_of_strong A

/-- The recorded cover underlying a coherent cover. -/
noncomputable def CoherentCover.cover (A : CoherentCover) : S1728Cover :=
  StrongCover.cover A.toStrongCover

/-- **S1756FirstMissing holds on the coherent cover datum**: for every coherent
cover, the identity-point self-endomorphism of its affine model is the identity. -/
theorem S1852FirstMissingOnCoherent (A : CoherentCover) :
    S1756End A.cover = 𝟙 (S1733Model A.cover) :=
  (S1756Unit_iff_end A.cover).mp A.unit

/-- The same statement proved from the full 2-universal property alone, without
using the unit field of the coherent datum. -/
theorem S1852FirstMissingOnCoherent_viaStrong (A : CoherentCover) :
    S1756End A.cover = 𝟙 (S1733Model A.cover) :=
  S1852End_eq_one_of_strong A.toStrongCover

/-- The restricted first missing statement, as a proposition. -/
def S1852CoherentFirstMissing : Prop := ∀ A : CoherentCover, S1756End A.cover = 𝟙 (S1733Model A.cover)

/-- S1756's first missing statement holds on the coherent covers. -/
theorem S1852CoherentFirstMissing_proof : S1852CoherentFirstMissing :=
  S1852FirstMissingOnCoherent

/-- Every coherent cover's underlying recorded cover satisfies the strong
identity-point property, i.e. the exact first missing statement for that cover. -/
theorem S1852ConeEssSurj_of_coherent (A : CoherentCover) :
    S1852ConeEssSurj (S1743BaseChange A.cover) :=
  (A.toStrongCover.finiteEtale.baseChange S1726AffineOver S1733BasePoint).coneEssSurj

/-- If every cover were coherent, S1756FirstMissing would hold. -/
theorem S1852FirstMissing_of_coherentAll
    (h : ∀ A : S1728Cover, ∃ C : CoherentCover, C.cover = A) : S1756FirstMissing := by
  intro A
  obtain ⟨C, rfl⟩ := h A
  exact S1852FirstMissingOnCoherent C

/-! ## 5. The identity (terminal) cover is coherent -/

/-- **The full 2-universal property of the canonical identity-point square.**

At a test scheme `T` and point `q`, the square of `S1762IdBaseChange` has
`toY = 𝟙`; the lift of a cone is its second leg, so any 1-cell satisfying the
second comparison is related to it by the right unitor.  Hence the doubled
presentation's failure (Section 7) is *not* an artefact of the weak witness being
unprovable for the identity: the canonical square satisfies the full property. -/
noncomputable def S1852IdStrongBc (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    StrongEtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.id S1850X.fiber) T q where
  toWeak := S1762IdBaseChange T q
  coneEssSurj := by
    intro W c f _ hY
    obtain ⟨e⟩ := hY
    exact ⟨(S1756RightUnitorIso f).symm.trans e⟩

/-- The identity map of the orbicurve stack is strongly finite etale. -/
noncomputable def S1852IdStrong :
    StrongEtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id S1850X.fiber) where
  baseChange T q := S1852IdStrongBc T q
  hasProperty T q := by
    change IsFinite (Over.Hom.left (𝟙 T)) ∧ Etale (Over.Hom.left (𝟙 T))
    exact ⟨inferInstance, inferInstance⟩

/-- The strong terminal cover. -/
noncomputable def S1852TerminalStrong : StrongCover S1726Orbicurve where
  source := S1726Orbicurve.stack
  map := Pseudofunctor.StrongTrans.id S1726Orbicurve.stack.fiber
  finiteEtale := S1852IdStrong

/-- The coherent terminal cover. -/
noncomputable def S1852TerminalCoherent : CoherentCover :=
  CoherentCover.ofStrong S1852TerminalStrong

/-- The model of the coherent terminal cover is the affine base itself. -/
theorem S1852TerminalModel :
    S1733Model S1852TerminalCoherent.cover = S1726AffineOver := rfl

/-- The self-endomorphism of the coherent terminal cover is the identity. -/
theorem S1852TerminalEnd :
    S1756End S1852TerminalCoherent.cover = 𝟙 (S1733Model S1852TerminalCoherent.cover) :=
  S1852FirstMissingOnCoherent S1852TerminalCoherent

/-- The coherent covers are inhabited. -/
theorem S1852CoherentNonempty : Nonempty CoherentCover := ⟨S1852TerminalCoherent⟩


/-! ### Per-cover characterisations of the exact first missing -/

/-- Per-cover exact characterisation: the full 2-universal property at the
identity point is exactly the missing unit 2-cell. -/
theorem S1852ConeEssSurj_iff_unit (A : S1728Cover) :
    S1852ConeEssSurj (S1743BaseChange A) ↔ S1756Unit A :=
  (S1852ConeEssSurj_iff_S1784 A).trans (S1804LiftEssSurj_iff_unit A)

/-- Per-cover exact characterisation in terms of the self-endomorphism. -/
theorem S1852ConeEssSurj_iff_end (A : S1728Cover) :
    S1852ConeEssSurj (S1743BaseChange A) ↔ S1756End A = 𝟙 (S1733Model A) :=
  (S1852ConeEssSurj_iff_S1784 A).trans (S1804LiftEssSurj_iff_end A)

/-! ## 6. The doubled cover is not coherent -/

/-- The second inclusion `T ⟶ T ⨿ T` as a strong transformation. -/
noncomputable abbrev S1852InrStrong (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y T) (S1743Y (S1850P T)) :=
  S1742StrongTransOfHom (F := S1726K) (S1850Inr T)

/-- The first inclusion `T ⟶ T ⨿ T` as a strong transformation. -/
noncomputable abbrev S1852InlStrong (T : SchemeOverField S1726K) :
    Pseudofunctor.StrongTrans (S1743Y T) (S1743Y (S1850P T)) :=
  S1742StrongTransOfHom (F := S1726K) (S1850Inl T)

theorem S1852Eval_inl (T : SchemeOverField S1726K) :
    S1743YonedaEval T (S1850P T) (S1852InlStrong T) = S1850Inl T := by
  rw [S1743YonedaEval_eq_S1742, S1742HomOfStrongTrans_strongTransOfHom]

theorem S1852Eval_inr (T : SchemeOverField S1726K) :
    S1743YonedaEval T (S1850P T) (S1852InrStrong T) = S1850Inr T := by
  rw [S1743YonedaEval_eq_S1742, S1742HomOfStrongTrans_strongTransOfHom]

theorem S1852Eval_fold (T : SchemeOverField S1726K) :
    S1743YonedaEval (S1850P T) T (S1850FoldStrong T) = S1850Fold T := by
  rw [S1743YonedaEval_eq_S1742, S1742HomOfStrongTrans_strongTransOfHom]

/-- The second inclusion splits the fold. -/
theorem S1852InrFold (T : SchemeOverField S1726K) :
    S1850Inr T ≫ S1850Fold T = 𝟙 T := by
  apply Comma.hom_ext
  · show Limits.coprod.inr ≫ Limits.coprod.desc (𝟙 T.left) (𝟙 T.left) = 𝟙 T.left
    rw [Limits.coprod.inr_desc]
  · apply Subsingleton.elim

/-- **The cone over the doubled square whose legs are the point and the
identity.**  Its canonical lift is the first inclusion `inl`. -/
noncomputable def S1852DoubledCone (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    (S1850Square T q).Cone (S1743Y T) where
  toX := q
  toY := Pseudofunctor.StrongTrans.id (S1743Y T)
  commutes := (S1756RightUnitorIso q).trans (S1756LeftUnitorIso q).symm

/-- **The second inclusion is a lift of the doubled cone**: its two projections
are 2-isomorphic to the cone's projections. -/
theorem S1852DoubledCone_inr_liftX (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1852InrStrong T)
        (S1850Square T q).toX) (S1852DoubledCone T q).toX) := by
  have hY : Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp (S1852InrStrong T)
      (S1850FoldStrong T)) (Pseudofunctor.StrongTrans.id (S1743Y T))) := by
    refine S1756IsoOfEvalEq T T _ _ ?_
    rw [S1743YonedaEval_vcomp, S1852Eval_inr, S1852Eval_fold, S1852InrFold T]
    rw [show S1743YonedaEval T T (Pseudofunctor.StrongTrans.id (S1743Y T)) = 𝟙 T
      from S1756YonedaEval_id T]
  obtain ⟨e⟩ := hY
  exact ⟨(S1756AssociatorIso (S1852InrStrong T) (S1850FoldStrong T) q).symm.trans
    ((S1756WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp (S1852InrStrong T) (S1850FoldStrong T))
      (Pseudofunctor.StrongTrans.id (S1743Y T)) q e).trans
      (S1756LeftUnitorIso q))⟩

/-- The second inclusion is a lift of the doubled cone, second projection. -/
theorem S1852DoubledCone_inr_liftY (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1852InrStrong T)
        (S1850Square T q).toY) (S1852DoubledCone T q).toY) := by
  have h : S1743YonedaEval T T
      (Pseudofunctor.StrongTrans.vcomp (S1852InrStrong T) (S1850Square T q).toY) =
      S1743YonedaEval T T (S1852DoubledCone T q).toY := by
    rw [S1743YonedaEval_vcomp, S1852Eval_inr]
    show S1850Inr T ≫ S1743YonedaEval (S1850P T) T (S1850FoldStrong T) =
      S1743YonedaEval T T (S1852DoubledCone T q).toY
    rw [S1852Eval_fold, S1852InrFold T]
    exact (S1756YonedaEval_id T).symm
  exact S1756IsoOfEvalEq T T _ _ h

/-- The canonical lift of the doubled cone is the first inclusion. -/
theorem S1852DoubledCone_lift_eval (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    S1743YonedaEval T (S1850P T)
      ((S1850Witness T q).lift (S1743Y T) (S1852DoubledCone T q)) = S1850Inl T := by
  show S1743YonedaEval T (S1850P T)
    (Pseudofunctor.StrongTrans.vcomp (S1852DoubledCone T q).toY
      (S1852InlStrong T)) = S1850Inl T
  rw [S1743YonedaEval_vcomp, S1852Eval_inl]
  have hid : S1743YonedaEval T T (S1852DoubledCone T q).toY = 𝟙 T :=
    S1756YonedaEval_id T
  rw [hid, Category.id_comp]

/-- **Essential surjectivity of the doubled cone comparison forces `inl = inr`:**
2-Yoneda evaluation sends a 2-isomorphism of the two lifts to an equality of
scheme morphisms. -/
theorem S1852DoubledCone_inl_eq_inr (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber) :
    S1852ConeEssSurj (S1850Doubled T q) → S1850Inl T = S1850Inr T := by
  intro h
  obtain ⟨e⟩ := h (S1743Y T) (S1852DoubledCone T q) (S1852InrStrong T)
    (S1852DoubledCone_inr_liftX T q) (S1852DoubledCone_inr_liftY T q)
  have he := S1743YonedaEval_congr_iso T (S1850P T) e
  rw [S1852Eval_inr] at he
  rw [show (S1850Doubled T q).isPullback.lift = (S1850Witness T q).lift from rfl] at he
  rw [S1852DoubledCone_lift_eval T q] at he
  exact he.symm

/-- Over a nonempty test scheme the two coproduct inclusions are different. -/
theorem S1852Inl_ne_inr (T : SchemeOverField S1726K) (hT : Nonempty T.left) :
    S1850Inl T ≠ S1850Inr T := by
  intro h
  have hleft : Over.Hom.left (S1850Inl T) = Over.Hom.left (S1850Inr T) :=
    congrArg Over.Hom.left h
  rw [S1850Inl_left, S1850Inr_left] at hleft
  obtain ⟨x⟩ := hT
  exact (AlgebraicGeometry.inl_ne_inr (X := T.left) (Y := T.left) x x)
    (congrArg (fun f => f x) hleft)

/-- **The doubled presentation of S1850 does not have the full 2-universal
property.** -/
theorem S1852Doubled_not_coneEssSurj (T : SchemeOverField S1726K)
    (q : Pseudofunctor.StrongTrans (S1743Y T) S1850X.fiber)
    (hT : Nonempty T.left) :
    ¬ S1852ConeEssSurj (S1850Doubled T q) :=
  fun h => S1852Inl_ne_inr T hT (S1852DoubledCone_inl_eq_inr T q h)

/-- Instantiated at the affine base: the doubled presentation of the identity
map at the identity point is not strong.  This is exactly the identity-point
presentation used by S1850 to refute `S1756FirstMissing`. -/
theorem S1852DoubledIdentity_not_coneEssSurj :
    ¬ S1852ConeEssSurj (S1850Doubled S1850T S1733BasePoint) := by
  haveI : Nontrivial S1726CoordinateRing := S1844nontrivialRingInst
  have hne : Nonempty (Spec (CommRingCat.of S1726CoordinateRing)) := inferInstance
  exact S1852Doubled_not_coneEssSurj S1850T S1733BasePoint hne

/-- **No strong finite-etale structure forgets to S1850's doubled structure**:
the strengthening of the cover datum excludes the counterexample. -/
theorem S1852Doubled_not_strong :
    ¬ ∃ M : StrongEtaleStackFiniteEtaleMorphism
        (Pseudofunctor.StrongTrans.id S1850X.fiber),
      M.toWeak = S1850DoubledFiniteEtale := by
  rintro ⟨M, hM⟩
  have h : S1852ConeEssSurj (M.baseChange S1850T S1733BasePoint).toWeak :=
    (M.baseChange S1850T S1733BasePoint).coneEssSurj
  have h' : S1852ConeEssSurj (M.toWeak.baseChange S1850T S1733BasePoint) := h
  rw [hM] at h'
  exact S1852DoubledIdentity_not_coneEssSurj h'

/-- **S1850's doubled cover is not coherent**: it is not the underlying recorded
cover of any coherent cover. -/
theorem S1852DoubledCover_not_coherent (C : CoherentCover)
    (hC : C.cover = S1850DoubledCover) : False := by
  have hunit : S1756Unit C.cover := C.unit
  rw [hC] at hunit
  exact S1850NoUnit hunit

/-! ## 7. Checks -/

#check S1852WeakSquare
#check S1852ConeEssSurj
#check S1852ConeEssSurj_iff_S1784
#check S1852ConeEssSurj_iff_unit
#check S1852ConeEssSurj_iff_end
#check S1852Unit_of_coneEssSurj
#check S1852End_eq_one_of_coneEssSurj
#check StrongEtaleStackBaseChangePresentation
#check StrongEtaleStackFiniteEtaleMorphism
#check StrongEtaleStackFiniteEtaleMorphism.toWeak
#check StrongCover
#check StrongCover.cover
#check S1852End_eq_one_of_strong
#check S1852Unit_of_strong
#check CoherentCover
#check CoherentCover.ofStrong
#check CoherentCover.cover
#check S1852FirstMissingOnCoherent
#check S1852FirstMissingOnCoherent_viaStrong
#check S1852CoherentFirstMissing_proof
#check S1852ConeEssSurj_of_coherent
#check S1852FirstMissing_of_coherentAll
#check S1852IdStrongBc
#check S1852IdStrong
#check S1852TerminalStrong
#check S1852TerminalCoherent
#check S1852TerminalModel
#check S1852TerminalEnd
#check S1852CoherentNonempty
#check S1852FirstMissing
#check S1852FirstMissing_iff_S1756
#check S1852NotFirstMissing
#check S1852InrStrong
#check S1852InrFold
#check S1852DoubledCone
#check S1852DoubledCone_lift_eval
#check S1852DoubledCone_inl_eq_inr
#check S1852Inl_ne_inr
#check S1852Doubled_not_coneEssSurj
#check S1852DoubledIdentity_not_coneEssSurj
#check S1852Doubled_not_strong
#check S1852DoubledCover_not_coherent

/-! ## 8. Axiom audit -/

#print axioms S1852WeakSquare
#print axioms S1852ConeEssSurj_iff_S1784
#print axioms S1852Unit_of_coneEssSurj
#print axioms S1852End_eq_one_of_coneEssSurj
#print axioms StrongEtaleStackFiniteEtaleMorphism.toWeak
#print axioms StrongCover.cover
#print axioms S1852End_eq_one_of_strong
#print axioms S1852Unit_of_strong
#print axioms CoherentCover.ofStrong
#print axioms S1852FirstMissingOnCoherent
#print axioms S1852FirstMissingOnCoherent_viaStrong
#print axioms S1852ConeEssSurj_of_coherent
#print axioms S1852FirstMissing_of_coherentAll
#print axioms S1852IdStrongBc
#print axioms S1852IdStrong
#print axioms S1852TerminalStrong
#print axioms S1852TerminalCoherent
#print axioms S1852TerminalModel
#print axioms S1852TerminalEnd
#print axioms S1852FirstMissing_iff_S1756
#print axioms S1852NotFirstMissing
#print axioms S1852InrFold
#print axioms S1852DoubledCone_lift_eval
#print axioms S1852DoubledCone_inl_eq_inr
#print axioms S1852Doubled_not_coneEssSurj
#print axioms S1852DoubledIdentity_not_coneEssSurj
#print axioms S1852Doubled_not_strong
#print axioms S1852DoubledCover_not_coherent

end LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual