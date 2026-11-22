/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1825
-/
import tmp.sheaf.xif.paper.S1809SmallCarrierCategoryActual
import tmp.sheaf.xif.paper.S1819G3IntegratedActual
import tmp.sheaf.xif.paper.S1778Category01ViaAlgebrasActual
import tmp.sheaf.xif.paper.S1753OrbicurveEtalePiAssemblyActual
import tmp.sheaf.xif.paper.S1779CorrectFiniteEtaleTargetActual
import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual

/-!
# S1825: the Galois structure on the *actual* small cover category `S1809CoverCategory01`

S1809 constructs, unconditionally, a genuine `Category.{0,1}`

  `S1809CoverCategory01 : Category.{0, 1} S1728Cover`

on the actual S1726 finite-etale cover type.  Its homs are literally the Type-0
`S1766QuotSmallCarrier` of 2-isomorphism classes, its composition is the
transported bicategorical composition, and it is equivalent to the actual
2-isomorphism-quotient category `S1728ActualCategory11`
(`S1809ComparisonFunctor_isEquivalence`).  This file *takes that category as
given*; it is never redefined and no `Shrink`/`ULift`/`PUnit` appears.

## Why the S1809 category is the right landing spot

`S1809CoverCategory01` has hom universe `0` and object universe `1`, which is
exactly the universe pair of `(CommAlgCat.FiniteEtale.{0} R')ᵒᵖ`
(`R' = S1726CoordinateRing`).  S1753's kernel-checked transport
(`S1753PreGaloisCategory`, `S1753FiberFunctorTransport`,
`S1753GaloisCategoryOfFiber`) and the S1778/S1779 route therefore apply
*verbatim* to this concrete category.  It is the first `Category.{0,1}` in the
tree on the actual cover type whose homs are the actual 2-isomorphism classes
(not an `InducedCategory` transport), so it is the honest cover category at the
target universe.

## What this file proves (all unconditional except for the stated inputs)

Given `e : S1809CoverCategory01 ≌ (FiniteEtale R')ᵒᵖ` (type `S1825AffineEquiv`):

* `S1825HasTerminal`, `S1825HasPullbacks`, `S1825HasFiniteCoproducts`: three of
  the five pre-Galois fields hold *unconditionally*, because the algebra side
  has them unconditionally (S1779: `R'` itself is terminal, tensor/pullback and
  `Pi`-closure are S1779's `FiniteEtaleClosure`).
* `S1825HasQuotientsByFiniteGroups`: the (G2) field from S1779's G2 over `R'`.
* `S1825PreGaloisCategory_of_affineEquiv`: `PreGaloisCategory` from an
  algebra-side `PreGaloisCategory`, by `S1753PreGaloisCategory`.
* `S1825PreGaloisCategory_of_missing`: hence from exactly S1779's `G2 ∧ G3`
  over `R'` (S1779's `S1779AlgPreGaloisMissing`).
* `S1825FiberFunctorTransport`, `S1825GaloisCategory_of_affineEquiv`,
  `S1825GaloisCategoryOfAlgGaloisData`, `S1825GaloisCategory_of_inputs`: the
  fibre functor and the `GaloisCategory` structure from a fibre functor and its
  six (G4)--(G6) fields.
* `S1825GaloisCategory_iff`: **`GaloisCategory S1809CoverCategory01` holds iff
  `GaloisCategory (FiniteEtale R')ᵒᵖ` holds.**  This is the sharpest
  unconditional reduction: once the affine equivalence is in hand, the Galois
  property of the *actual small cover category* is exactly the Galois property
  of the algebra side.  The proof is pure transport in both directions.
* `S1819` integration at the function field: `S1825PreGaloisCategory_functionField`
  (`(FiniteEtale K(E'))ᵒᵖ` is a pre-Galois category, unconditionally, all five
  fields being S1819's actual theorem), and the transport of that field-level
  structure to `S1809CoverCategory01` along an equivalence
  (`S1825PreGaloisCategory_of_functionFieldEquiv`,
  `S1825GaloisCategory_of_functionFieldEquiv`).  This is *not* the `R'` route:
  S1750/S1779 record that the generic-fibre category is not equivalent to all
  covers, and no inhabitant of that equivalence is claimed here.

## Exact missing data

* `S1825AffineEquivalenceMissing`: the affine equivalence at
  `S1809CoverCategory01`.  `S1825AffineEquivalenceMissing_iff_S1778` proves it is
  **exactly** `S1778AffineEquivalenceMissing` (S1777's affine equivalence
  `S1728Cover ≌ (FiniteEtale R')ᵒᵖ`), via the S1809 comparison equivalence.  No
  new missing input appears.
* `S1825FiniteEtaleCoverMissing`: the same datum in the honest scheme form
  `S1809CoverCategory01 ≌ FiniteEtaleCover (Spec R')`; proven equivalent to the
  previous one using S1799's affine comparison.
* `S1825AlgPreGaloisMissing` = S1779's `G2 ∧ G3` over the coordinate ring `R'`.
  S1819 supplies the field-level (G3) (and the five pre-Galois fields) for a
  *field*, and `R'` is a coordinate ring, not a field; this is S1779's named
  residual, not a new hypothesis.
* `S1825FiberFunctorMissing`: the six (G4)--(G6) fields of the geometric fibre
  functor `S1779GeometricFiber`.  This is missing even over a field: S1767 and
  S1793 carry it only as a hypothesis (`FiberFunctorField`).
* `S1825GaloisMissing`: the conjunction of the above, and
  `S1825GaloisCategory_of_missing` derives `GaloisCategory S1809CoverCategory01`
  from it.

`S1766CoverMapDiscrete` (`S1809SmallRawCoverDataFirstMissing`, raw cover-map
discreteness) is **not** consumed anywhere in this file: `S1809CoverCategory01`
is already a `Category.{0,1}`, so raw smallness of cover maps is irrelevant to
its Galois structure.  The `S1825GaloisInputs` structure makes the hypothesis set
explicit.

## Verification (session S1825, 2026-11-01)

Compiled with

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1825GaloisOnSmallCategoryActual.olean
      tmp/sheaf/xif/paper/S1825GaloisOnSmallCategoryActual.lean

-> EXIT=0, no errors, no `sorryAx`.  Every `#print axioms` below prints only
`[propext, Classical.choice, Quot.sound]`.

## Honest boundary

`GaloisCategory S1809CoverCategory01` is **not** constructed unconditionally.
It is reduced, given `e`, to the algebra-side `GaloisCategory (FiniteEtale R')ᵒᵖ`
(iff), whose remaining content is exactly (i) `R'`-level G2/G3 and (ii) a fibre
functor with its six fields, plus the affine bridge itself.  No `sorry`, no
`admit`, no new axiom, no `Shrink`/`ULift`/`PUnit`; every axiom footprint is
checked at the end.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1825GaloisOnSmallCategoryActual

open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual
open LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual
open LeanFormal.IUT.XiFPaper.S1778Category01ViaAlgebrasActual
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-! ## 1. The concrete category, the algebra side and the exact input type -/

/-- The actual small cover category at the target universe: literally S1809's
S1809CoverCategory01, whose homs are the Type-0 S1766QuotSmallCarrier.  This is
a name for that category, not a new category structure. -/
abbrev S1825Cover : Category.{0, 1} S1728Cover := S1809CoverCategory01

/- The category instance used by every statement below is S1809's actual
Category.{0,1} on the S1726 cover type. -/
attribute [local instance] S1809CoverCategory01

/-- The corrected algebra side (CommAlgCat.FiniteEtale.{0} R')ᵒᵖ,
definitionally S1779's S1779AlgR. -/
abbrev S1825AlgR : Type 1 := S1779AlgR

/-- The field-level algebra side (CommAlgCat.FiniteEtale.{0} K(E'))ᵒᵖ,
definitionally S1779's S1779AlgK. -/
abbrev S1825AlgK : Type 1 := S1779AlgK

/-- The exact input type of this file: an equivalence from the actual small
cover category to the corrected algebra side, i.e. S1777's affine equivalence
stated at S1809CoverCategory01. -/
abbrev S1825AffineEquiv : Type 1 :=
  @CategoryTheory.Equivalence S1728Cover S1779AlgR
    S1809CoverCategory01 S1779AlgR_category

/-- The small category is the actual quotient category: S1809's comparison
functor is an equivalence (small to 2-isomorphism quotient). -/
noncomputable def S1825ComparisonEquivalence :
    @CategoryTheory.Equivalence S1728Cover S1728Cover
      S1809CoverCategory01 S1728ActualCategory11 :=
  S1809ComparisonFunctor.asEquivalence

/-- The homs of the concrete category are the Type-0 small carrier: the
universe requirement that makes S1753 transport applicable.  This is S1809's
kernel-checked hom computation, re-exported. -/
theorem S1825Hom_type (A B : S1728Cover) :
    (@Quiver.Hom _ S1809CoverCategory01.toQuiver A B) = S1809SmallHom A B :=
  S1809CoverCategory01_hom A B

/-- The hom family is a Type 0 family: this is why the S1753 transport applies. -/
example (A B : S1728Cover) : Type := S1809SmallHom A B

/-! ## 2. Three of the five pre-Galois fields, unconditionally given the affine equivalence -/

/-- Given the affine equivalence, the actual small cover category has a
terminal object: the algebra side has one unconditionally (R' itself, S1779). -/
theorem S1825HasTerminal (e : S1825AffineEquiv) : HasTerminal S1728Cover :=
  (Equivalence.hasTerminal_iff e).mpr inferInstance

/-- Given the affine equivalence, the actual small cover category has
pullbacks: transported from the algebra side's tensor-product pullbacks
(S1779's FiniteEtaleClosure). -/
theorem S1825HasPullbacks (e : S1825AffineEquiv) : HasPullbacks S1728Cover :=
  Adjunction.hasLimitsOfShape_of_equivalence (J := WalkingCospan) e.functor

/-- Given the affine equivalence, the actual small cover category has finite
coproducts: transported from the algebra side's Pi-algebras. -/
theorem S1825HasFiniteCoproducts (e : S1825AffineEquiv) : HasFiniteCoproducts S1728Cover :=
  ⟨fun n => Adjunction.hasColimitsOfShape_of_equivalence (J := Discrete (Fin n)) e.functor⟩

/-- The (G2) field of the actual small cover category, from S1779's G2 over the
coordinate ring R' (quotients by finite group actions). -/
theorem S1825HasQuotientsByFiniteGroups (e : S1825AffineEquiv)
    (hQuot : S1779QuotientsMissing) :
    ∀ (G : Type) [Group G] [Finite G], HasColimitsOfShape (SingleObj G) S1728Cover := by
  intro G hG hFin
  letI : Group G := hG
  letI : Finite G := hFin
  letI : HasColimitsOfShape (SingleObj G) S1779AlgR := hQuot G
  exact Adjunction.hasColimitsOfShape_of_equivalence (J := SingleObj G) e.functor

/-! ## 3. Pre-Galois structure: transport along the affine equivalence -/

/-- **Pre-Galois structure on the actual small cover category**, from the affine
equivalence and an algebra-side PreGaloisCategory.  The proof is S1753's
kernel-checked transport S1753PreGaloisCategory, applied at the concrete
category S1809CoverCategory01; no field is reproved or assumed. -/
theorem S1825PreGaloisCategory_of_affineEquiv (e : S1825AffineEquiv)
    (P : PreGaloisCategory S1779AlgR) : PreGaloisCategory S1728Cover := by
  letI : PreGaloisCategory S1779AlgR := P
  exact S1753PreGaloisCategory e

/-- The same, from exactly S1779's G2/G3 over R': no other algebra-side input
is used. -/
theorem S1825PreGaloisCategory_of_missing (e : S1825AffineEquiv)
    (h : S1779AlgPreGaloisMissing) : PreGaloisCategory S1728Cover :=
  S1825PreGaloisCategory_of_affineEquiv e (S1779PreGaloisCategory h.1 h.2)

/-! ## 4. Fibre functor and Galois structure -/

/-- Transport of a fibre functor: if F is a fibre functor on the algebra side,
then e.functor ⋙ F is a fibre functor on the actual small cover category. -/
theorem S1825FiberFunctorTransport (e : S1825AffineEquiv)
    (P : PreGaloisCategory S1779AlgR)
    (F : S1779AlgR ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1779AlgR S1779AlgR_category P F) :
    @PreGaloisCategory.FiberFunctor S1728Cover S1809CoverCategory01
      (S1825PreGaloisCategory_of_affineEquiv e P) (e.functor ⋙ F) := by
  letI : PreGaloisCategory S1779AlgR := P
  letI : PreGaloisCategory.FiberFunctor F := hF
  exact S1753FiberFunctorTransport e F

/-- **Galois structure on the actual small cover category**, from the affine
equivalence, an algebra-side pre-Galois structure and an algebra-side fibre
functor with its six (G4)--(G6) fields. -/
theorem S1825GaloisCategory_of_affineEquiv (e : S1825AffineEquiv)
    (P : PreGaloisCategory S1779AlgR)
    (F : S1779AlgR ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1779AlgR S1779AlgR_category P F) :
    GaloisCategory S1728Cover := by
  letI : PreGaloisCategory S1779AlgR := P
  letI : PreGaloisCategory.FiberFunctor F := hF
  exact S1753GaloisCategoryOfFiber e F

/-- The Galois structure from S1779's packaged algebra-side Galois data
(S1779AlgGaloisData) and the affine equivalence. -/
theorem S1825GaloisCategoryOfAlgGaloisData (e : S1825AffineEquiv)
    (D : S1779AlgGaloisData) : GaloisCategory S1728Cover :=
  S1825GaloisCategory_of_affineEquiv e D.preGalois D.fiber D.fiberFunctor

/-- **The full hypothesis set of the Galois construction on the actual small
category**: the affine equivalence and the algebra-side Galois data.  There is
no hypothesis on raw cover maps (no S1766CoverMapDiscrete, no
S1809SmallRawCoverDataFirstMissing), and no smallness hypothesis of any kind. -/
structure S1825GaloisInputs where
  /-- The affine equivalence S1809CoverCategory01 to (FiniteEtale R')ᵒᵖ. -/
  equivalence : S1825AffineEquiv
  /-- The algebra-side pre-Galois structure, fibre functor and its six fields. -/
  algData : S1779AlgGaloisData

/-- From the explicit hypothesis set: the actual small cover category is a
Galois category. -/
theorem S1825GaloisCategory_of_inputs (h : S1825GaloisInputs) :
    GaloisCategory S1728Cover :=
  S1825GaloisCategoryOfAlgGaloisData h.equivalence h.algData

/-! ## 5. The sharp reduction: Galois iff Galois on the algebra side -/

/-- **GaloisCategory S1809CoverCategory01 holds iff GaloisCategory
(FiniteEtale R')ᵒᵖ holds**, given the affine equivalence.  Both directions are
pure transport across e (S1753), so the Galois problem for the actual small
cover category is *exactly* the Galois problem for the algebra side. -/
theorem S1825GaloisCategory_iff (e : S1825AffineEquiv) :
    GaloisCategory S1728Cover ↔ GaloisCategory S1779AlgR := by
  constructor
  · intro hC
    letI : GaloisCategory S1728Cover := hC
    exact S1753GaloisCategory e.symm
  · intro hD
    letI : GaloisCategory S1779AlgR := hD
    exact S1753GaloisCategory e

/-! ## 6. The exact missing data -/

/-- **The exact missing input**: an equivalence from the actual small cover
category to the corrected algebra side.  This is S1777's affine equivalence. -/
def S1825AffineEquivalenceMissing : Prop :=
  Nonempty
    (@CategoryTheory.Equivalence S1728Cover S1779AlgR
      S1809CoverCategory01 S1779AlgR_category)

/-- The missing input really is an equivalence of the actual small category to
the actual quotient category, and conversely: the S1809 comparison equivalence
identifies the two formulations. -/
theorem S1825AffineEquivalenceMissing_iff_quotient :
    S1825AffineEquivalenceMissing ↔
      Nonempty
        (@CategoryTheory.Equivalence S1728Cover S1779AlgR
          S1728ActualCategory11 S1779AlgR_category) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨S1825ComparisonEquivalence.symm.trans e⟩
  · rintro ⟨e⟩
    exact ⟨S1825ComparisonEquivalence.trans e⟩

/-- **The S1825 missing input is exactly S1778's (S1777's) missing affine
equivalence.**  No new missing input is introduced by working with the concrete
small category S1809CoverCategory01. -/
theorem S1825AffineEquivalenceMissing_iff_S1778 :
    S1825AffineEquivalenceMissing ↔ S1778AffineEquivalenceMissing :=
  S1825AffineEquivalenceMissing_iff_quotient

/-- S1799's affine comparison at the coordinate ring R':
(FiniteEtale R')ᵒᵖ is equivalent to FiniteEtaleCover (Spec R'). -/
noncomputable def S1825AlgCoverEquivalence :
    S1779AlgR ≌ FiniteEtaleCover (specBase S1779R) :=
  affineFiniteEtaleEquivalence (R := S1779R)

/-- The same missing input in the honest scheme form: an equivalence from the
actual small cover category to FiniteEtaleCover (Spec R'). -/
def S1825FiniteEtaleCoverMissing : Prop :=
  Nonempty
    (@CategoryTheory.Equivalence S1728Cover (FiniteEtaleCover (specBase S1779R))
      S1809CoverCategory01
      (inferInstance : Category.{0, 1} (FiniteEtaleCover (specBase S1779R))))

/-- S1799 moves between the two formulations of the missing bridge, so the
scheme form is neither weaker nor stronger than the algebra form. -/
theorem S1825FiniteEtaleCoverMissing_iff :
    S1825AffineEquivalenceMissing ↔ S1825FiniteEtaleCoverMissing := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans S1825AlgCoverEquivalence⟩
  · rintro ⟨e⟩
    exact ⟨e.trans S1825AlgCoverEquivalence.symm⟩

/-- The algebra-side pre-Galois residual over the coordinate ring R': S1779's
exact G2/G3 pair.  S1819 proves the G3 field only over a field, and R' is a
coordinate ring; this is S1779's named residual, not a new hypothesis. -/
def S1825AlgPreGaloisMissing : Prop := S1779AlgPreGaloisMissing

/-- The missing (G4)--(G6) content: the six fields of the geometric fibre
functor at the point (0,0).  Missing even over a field (S1767/S1793 carry it
only as a hypothesis). -/
def S1825FiberFunctorMissing (hPre : PreGaloisCategory S1779AlgR) : Prop :=
  S1779FiberFunctorMissing hPre

/-- The complete missing content for GaloisCategory S1809CoverCategory01:
the affine bridge, the R'-level pre-Galois residual, and the fibre-functor
fields. -/
def S1825GaloisMissing : Prop :=
  S1825AffineEquivalenceMissing ∧
    ∃ h : S1825AlgPreGaloisMissing,
      S1825FiberFunctorMissing (S1779PreGaloisCategory h.1 h.2)

/-- **From exactly the missing content, the Galois structure on the actual small
cover category.**  The term uses the genuine geometric fibre functor
S1779GeometricFiber; nothing is postulated. -/
theorem S1825GaloisCategory_of_missing (h : S1825GaloisMissing) :
    GaloisCategory S1728Cover := by
  obtain ⟨hAff, hPre, hFiber⟩ := h
  obtain ⟨e⟩ := hAff
  exact S1825GaloisCategory_of_affineEquiv e
    (S1779PreGaloisCategory hPre.1 hPre.2) S1779GeometricFiber hFiber

/-- **The conclusion is literally S1809's recorded target field**
`S1809GaloisCategoryRequired : Prop`, which is
`@GaloisCategory.{1, 0} S1728Cover S1809CoverCategory01` by definition. -/
theorem S1825GaloisCategoryRequired_of_missing (h : S1825GaloisMissing) :
    S1809GaloisCategoryRequired :=
  S1825GaloisCategory_of_missing h

/-! ## 7. S1819 at the function field, and the field-level variant -/

/-- **S1819 integrated.**  (FiniteEtale K(E'))ᵒᵖ is a pre-Galois category with
all five fields actual: this is S1819's preGaloisCategory (S1810 + S1771 +
S1786 + S1793), which is available over any field and hence at the function
field K(E'). -/
theorem S1825PreGaloisCategory_functionField :
    @PreGaloisCategory.{1, 0} S1779AlgK S1779AlgK_category :=
  S1819.preGaloisCategory (K := S1779FunctionField)

/-- Transport of S1819's field-level pre-Galois structure to the actual small
cover category, along an equivalence to (FiniteEtale K(E'))ᵒᵖ.

This is the field-level variant, recorded because it is the only place where a
fully unconditional pre-Galois structure is transported to S1809CoverCategory01.
It is **not** the R' route: S1750/S1779 record that the generic-fibre category is
not equivalent to all covers, so no inhabitant of the displayed equivalence is
asserted here. -/
theorem S1825PreGaloisCategory_of_functionFieldEquiv
    (e : @CategoryTheory.Equivalence S1728Cover S1779AlgK
      S1809CoverCategory01 S1779AlgK_category) :
    PreGaloisCategory S1728Cover := by
  haveI : PreGaloisCategory S1779AlgK := S1825PreGaloisCategory_functionField
  exact S1753PreGaloisCategory e

/-- The Galois structure at the function field, from a fibre functor and its six
fields on the field-level algebra category. -/
theorem S1825GaloisCategory_of_functionFieldEquiv
    (e : @CategoryTheory.Equivalence S1728Cover S1779AlgK
      S1809CoverCategory01 S1779AlgK_category)
    (F : S1779AlgK ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1779AlgK S1779AlgK_category
      S1825PreGaloisCategory_functionField F) :
    GaloisCategory S1728Cover := by
  haveI : PreGaloisCategory S1779AlgK := S1825PreGaloisCategory_functionField
  letI : PreGaloisCategory.FiberFunctor F := hF
  exact S1753GaloisCategoryOfFiber e F

/-- The algebra-side Galois data over the function field. -/
structure S1825AlgKGaloisData where
  /-- The pre-Galois structure (S1819, unconditional). -/
  preGalois : PreGaloisCategory S1779AlgK
  /-- The fibre functor. -/
  fiber : S1779AlgK ⥤ FintypeCat.{0}
  /-- Its six (G4)--(G6) fields. -/
  fiberFunctor : @PreGaloisCategory.FiberFunctor S1779AlgK S1779AlgK_category preGalois fiber

/-! ## 8. Checks and axiom audit -/

#check S1825Cover
#check S1825AlgR
#check S1825AffineEquiv
#check S1825ComparisonEquivalence
#check S1825Hom_type
#check S1825HasTerminal
#check S1825HasPullbacks
#check S1825HasFiniteCoproducts
#check S1825HasQuotientsByFiniteGroups
#check S1825PreGaloisCategory_of_affineEquiv
#check S1825PreGaloisCategory_of_missing
#check S1825FiberFunctorTransport
#check S1825GaloisCategory_of_affineEquiv
#check S1825GaloisCategoryOfAlgGaloisData
#check S1825GaloisInputs
#check S1825GaloisCategory_of_inputs
#check S1825GaloisCategory_iff
#check S1825AffineEquivalenceMissing
#check S1825AffineEquivalenceMissing_iff_quotient
#check S1825AffineEquivalenceMissing_iff_S1778
#check S1825AlgCoverEquivalence
#check S1825FiniteEtaleCoverMissing
#check S1825FiniteEtaleCoverMissing_iff
#check S1825AlgPreGaloisMissing
#check S1825FiberFunctorMissing
#check S1825GaloisMissing
#check S1825GaloisCategory_of_missing
#check S1825GaloisCategoryRequired_of_missing
#check S1825PreGaloisCategory_functionField
#check S1825PreGaloisCategory_of_functionFieldEquiv
#check S1825GaloisCategory_of_functionFieldEquiv

#print axioms S1825ComparisonEquivalence
#print axioms S1825Hom_type
#print axioms S1825HasTerminal
#print axioms S1825HasPullbacks
#print axioms S1825HasFiniteCoproducts
#print axioms S1825HasQuotientsByFiniteGroups
#print axioms S1825PreGaloisCategory_of_affineEquiv
#print axioms S1825PreGaloisCategory_of_missing
#print axioms S1825FiberFunctorTransport
#print axioms S1825GaloisCategory_of_affineEquiv
#print axioms S1825GaloisCategoryOfAlgGaloisData
#print axioms S1825GaloisCategory_of_inputs
#print axioms S1825GaloisCategory_iff
#print axioms S1825AffineEquivalenceMissing_iff_quotient
#print axioms S1825AffineEquivalenceMissing_iff_S1778
#print axioms S1825AlgCoverEquivalence
#print axioms S1825FiniteEtaleCoverMissing_iff
#print axioms S1825GaloisCategory_of_missing
#print axioms S1825GaloisCategoryRequired_of_missing
#print axioms S1825PreGaloisCategory_functionField
#print axioms S1825PreGaloisCategory_of_functionFieldEquiv
#print axioms S1825GaloisCategory_of_functionFieldEquiv

end LeanFormal.IUT.XiFPaper.S1825GaloisOnSmallCategoryActual
