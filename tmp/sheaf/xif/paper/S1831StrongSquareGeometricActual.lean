/-
# S1831: the strong 2-universal property of the actual finite etale base-change
square, by the geometric / affine route

## Setting

For a cover `A : S1728Cover` the identity-point square of `A.map` is

    P = Y(S_A) --toSource--> X = A.source
       |                        |
      toY                      A.map
       v                        v
    Y = Y(Spec R') --id-----> Z = Y(Spec R') = X.stack

where `P = S1743ModelStack A = Y(S1733Model A)` and `S_A = S1733Model A` is the
affine finite-etale model of the cover, i.e. the actual finite etale base change
of `A.map` along the identity point of the representable base; it is the actual
finite etale cover `S1816Obj A : FiniteEtaleCover (Spec R')` (S1816), with
`FiniteEtaleCover.carrier (S1816Obj A) = S_A` and structure morphism `S1733ModelOver A`.

S1827 proved that the missing half of the 2-dimensional universal property of this
square is exactly `S1827ConeEssSurj A` (S1784's `S1784LiftEssSurj A`), and that
it is equivalent to

* `S1756Unit A`: the unit 2-cell `toSource ; lift ≅ 1`,
* `S1756End A = 1`: the identity-point self-endomorphism of `S_A` is the identity,
* `S1827ComparisonQuasiEquiv A`: the canonical comparison `toSource` with the
  actual 2-pullback of `(A.map, id)` (apex `X = A.source`, S1804) is a quasi-equivalence,
* `S1804RecordedActual A` and S1784's counit data `S1784CounitData A`.

S1827 also proved that the recorded `TwoPullbackWitness` (lift, the two projection
2-cells, the action on cone morphisms and 2-cell extensionality) does not imply
it as a matter of 2-categorical algebra (S1801).

This file keeps the recorded definitions unchanged (in particular
`TwoPullbackWitness` is *not* modified), introduces no axiom and fakes no
2-cell.  It pushes the geometric / affine route as far as it goes and reports the
exact first missing statement.

## What is proved here (unconditional)

1. **Target lock** `S1831StrongSquare` = `S1827ConeEssSurj`, with the exact
   characterisations above and the closure of the S1743/S1756/S1758/S1804
   targets.

2. **Apex reduction** `S1831ApexRigid`: the strong property is equivalent to
   1-cell uniqueness *at the apex alone* - every endomorphism `f` of the
   representable stack `P = Y(S_A)` whose two projections agree with the
   square's own projections is 2-isomorphic to the identity.  No quantification
   over arbitrary test stacks is needed: the whole missing input lives over the
   affine model.

3. **The missing 2-cells in scheme form.**  The lift `S1784Counit A` of the
   square's own cone is a 1-cell `P ⟶ P`; its 2-Yoneda evaluation
   `S1831OwnConeEval A : S_A ⟶ S_A` is proved to be a morphism over `Spec R'`
   (`S1831OwnConeEval_projection`).  The two 2-cells of `S1784CounitData` are
   *exactly* the two scheme equations

       S1831OwnConeEval A = 1        and        S1831OwnConeEval A = S1756End A,

   so that the strong 2-universal property becomes the conjunction

       S1827ConeEssSurj A  ↔  S1831OwnConeEval A = 1 ∧ S1756End A = 1.

4. **Affine / finite-etale-algebra form (S1781 + S1799).**  The target is
   equivalent to the identity of the explicit endomorphism

       S1831AlgEnd A : S1781Obj A ⟶ S1781Obj A

   of the finite etale `R'`-algebra `Gamma(S_A)` (S1781), and, through S1799's
   actual equivalence `(FiniteEtale R')^op ≌ FiniteEtaleCover (Spec R')`, to the
   identity of the corresponding endomorphism of the actual finite etale cover of
   `Spec R'`.  Geometrically: the target says that the identity-point finite
   etale base change of the cover source *is* the cover `S_A ⟶ Spec R'`, not a
   proper retract of it.  The affine carrier bridge between the cover `S1816Obj A`
   and `Spec Gamma(S_A)` is recorded as `S1831CoverCarrier_iso`.

5. **Positive instances** (unconditional): the comparison `toSource` is a
   retraction of `lift` with an explicit section (S1784), the own-cone lift is a
   morphism over the base, and the target holds whenever the structure morphism
   `S_A ⟶ Spec R'` is a monomorphism.

## The honest boundary: the exact first missing statement

What is **not** proved, and cannot be proved from the recorded fields, is

    S1831FirstMissing : for every cover A, S1831ApexRigid A

equivalently `S1827ConeEssSurj A` for every cover, equivalently
`S1831AlgEnd A = 1` for every cover.  In concrete terms the first missing input
is the *1-cell uniqueness* of the recorded identity-point square at its own apex:
the lift `S1784Counit A` of the square's own cone must satisfy
`S1831OwnConeEval A = 1` (and consequently `S1756End A = 1`).  The seven
recorded fields give the lift and 2-cell extensionality but never compare two
*1-cells*.

Two limitations are stated exactly.  (a) S1801's degenerate square satisfies all
seven recorded fields and its cone comparison is not essentially surjective, so the
missing coherence is not a consequence of the recorded fields *as 2-categorical
algebra*; S1827 notes that S1801's model has a constant apex whereas the apex here
is the representable stack `Y(S_A)`, so the question whether the geometric cover
data forces the coherence is not settled by that refutation, and it is not settled
here either.  (b) Closing the target needs either the definition change of
`TwoPullbackWitness` to the full 2-universal property (not done here: the user
requires the object to stay unchanged) or an independent geometric theorem that the
identity-point presentation square is a genuine 2-pullback - equivalently, that the
representably finite etale stack `A.source` is represented by its identity-point
model `S_A` and not merely a retract of it.  No such theorem exists in the tree.

## Next step

The sharpest remaining subproblem is the apex equation
`S1831OwnConeEval A = 1` together with `S1756End A = 1`; by
`S1831StrongSquare_iff_eval_pair` they are jointly equivalent to the target.
A proof of either equation must use the cover datum beyond the seven recorded
fields (e.g. the base-change presentations at the other scheme points, or the
stack condition `A.source.isStack`), or a genuine counterexample cover must be
constructed to refute the target for the unchanged definition.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the `#print axioms`
block at the end.  No `sorry`, no new axiom, no `Shrink`, `ULift` or `PUnit`.
-/

import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S1816OrbicurveCoversToAffineActual
import tmp.sheaf.xif.paper.S1781AffineCoverAlgebrasSecondActual
import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1831StrongSquareGeometricActual

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
open LeanFormal.IUT.XiFPaper.S1758SourceRetractionActual
open LeanFormal.IUT.XiFPaper.S1781AffineCoverAlgebrasSecondActual
open LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual

/-! ## 1. The target: the strong 2-universal property of the actual square -/

/-- **The target.**  The strong 2-universal property of the actual identity-point
finite etale base-change square: the missing half of its 2-dimensional universal
property, in the exact form fixed by S1827 and S1784 (essential surjectivity of
the cone comparison `Hom(W, P) ⟶ Cone(W)`). -/
def S1831StrongSquare (A : S1728Cover) : Prop := S1827ConeEssSurj A

/-- The target is definitionally S1827's essential surjectivity statement. -/
theorem S1831StrongSquare_iff_coneEssSurj (A : S1728Cover) :
    S1831StrongSquare A ↔ S1827ConeEssSurj A :=
  Iff.rfl

/-- The target is definitionally S1784's essential surjectivity statement. -/
theorem S1831StrongSquare_iff_liftEssSurj (A : S1728Cover) :
    S1831StrongSquare A ↔ S1784LiftEssSurj A :=
  S1827ConeEssSurj_iff_liftEssSurj A

/-- The target is exactly the existence of the unit 2-cell `toSource ; lift ≅ 1`. -/
theorem S1831StrongSquare_iff_unit (A : S1728Cover) :
    S1831StrongSquare A ↔ S1756Unit A :=
  (S1827ConeEssSurj_iff_liftEssSurj A).trans (S1804LiftEssSurj_iff_unit A)

/-- The target is exactly the identity of the self-endomorphism `S1756End A` of the
affine model `S_A`. -/
theorem S1831StrongSquare_iff_end (A : S1728Cover) :
    S1831StrongSquare A ↔ S1756End A = 𝟙 (S1733Model A) :=
  (S1831StrongSquare_iff_unit A).trans (S1756Unit_iff_end A)

/-- The target is exactly the quasi-equivalence of the canonical comparison
`toSource` with the actual 2-pullback of `(A.map, id)` (apex `A.source`, S1804). -/
theorem S1831StrongSquare_iff_comparison (A : S1728Cover) :
    S1831StrongSquare A ↔ S1827ComparisonQuasiEquiv A :=
  (S1831StrongSquare_iff_unit A).trans (S1827ComparisonQuasiEquiv_iff_unit A).symm

/-- The target is exactly S1804's recorded-actual statement. -/
theorem S1831StrongSquare_iff_recordedActual (A : S1728Cover) :
    S1831StrongSquare A ↔ S1804RecordedActual A :=
  (S1831StrongSquare_iff_unit A).trans (S1804RecordedActual_iff_unit A).symm

/-- **The target is exactly S1784's counit data**: the lift of the square's own cone
is 2-isomorphic to the identity and to `toSource ; lift`.  This is the sharpest
form of the missing input: two 2-cells at the square's own cone. -/
theorem S1831StrongSquare_iff_counitData (A : S1728Cover) :
    S1831StrongSquare A ↔ S1784CounitData A :=
  (S1831StrongSquare_iff_liftEssSurj A).trans (S1804RecordedActual_iff_counitData A)

/-- **The first missing statement.**  For every cover, the actual identity-point
finite etale base-change square has the strong 2-universal property. -/
def S1831FirstMissing : Prop := ∀ A : S1728Cover, S1831StrongSquare A

/-- The first missing statement is exactly S1827's. -/
theorem S1831FirstMissing_iff_S1827 : S1831FirstMissing ↔ S1827FirstMissing :=
  Iff.rfl

/-- The first missing statement is exactly S1804's. -/
theorem S1831FirstMissing_iff_S1804 : S1831FirstMissing ↔ S1804FirstMissing :=
  S1827FirstMissing_iff_S1804

/-- The first missing statement is exactly S1756's endomorphism equation. -/
theorem S1831FirstMissing_iff_S1756 : S1831FirstMissing ↔ S1756FirstMissing :=
  S1827FirstMissing_iff_S1756

/-- The first missing statement is exactly S1743's source retraction. -/
theorem S1831FirstMissing_iff_sourceRetraction :
    S1831FirstMissing ↔ S1743SourceRetraction :=
  S1827FirstMissing_iff_sourceRetraction

/-- The first missing statement is exactly S1758's statement. -/
theorem S1831FirstMissing_iff_S1758 : S1831FirstMissing ↔ S1758FirstMissing :=
  S1827FirstMissing_iff_S1758

/-- The first missing statement is exactly "every canonical comparison is an
equivalence". -/
theorem S1831FirstMissing_iff_comparisonEquiv :
    S1831FirstMissing ↔ ∀ A : S1728Cover, S1827ComparisonQuasiEquiv A :=
  S1827FirstMissing_iff_comparisonEquiv

/-- The first missing statement gives S1784's counit data for every cover. -/
theorem S1831FirstMissing_to_counitData (h : S1831FirstMissing) :
    ∀ A : S1728Cover, S1784CounitData A :=
  fun A => (S1831StrongSquare_iff_counitData A).mp (h A)

/-- **Closure of the targets** from the single strong 2-universal property. -/
theorem S1831FirstMissing_closure (h : S1831FirstMissing) :
    S1804FirstMissing ∧ S1756FirstMissing ∧ S1758FirstMissing ∧
      S1743SourceRetraction ∧ S1756SourceRepresentableAll :=
  S1827FirstMissing_closure (S1831FirstMissing_iff_S1827.mp h)

/-! ## 2. The apex reduction: the missing input lives over the affine model -/

/-- **The apex form of the missing 1-cell uniqueness.**  Every endomorphism `f` of
the representable stack `P = Y(S_A)` whose two projections agree with the
square's own projections is 2-isomorphic to the identity.

By `S1831StrongSquare_iff_apexRigid` this is the same statement as
`S1827ConeEssSurj`, with the quantification over arbitrary test stacks removed:
only the apex `P` is tested. -/
def S1831ApexRigid (A : S1728Cover) : Prop :=
  ∀ f : Pseudofunctor.StrongTrans (S1743ModelStack A) (S1743ModelStack A),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f (S1743Square A).toX)
      (S1743Square A).toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp f (S1743Square A).toY)
        (S1743Square A).toY) →
        Nonempty (Iso f (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))

/-- The strong 2-universal property implies apex rigidity: apply the cone comparison
to the square's own cone, for `f` and for `1`, and compose. -/
theorem S1831ApexRigid_of_strongSquare (A : S1728Cover) (h : S1831StrongSquare A) :
    S1831ApexRigid A := by
  intro f hX hY
  obtain ⟨e⟩ := h (S1743ModelStack A) (S1784PullbackCone A) f hX hY
  obtain ⟨e₀⟩ := h (S1743ModelStack A) (S1784PullbackCone A)
    (Pseudofunctor.StrongTrans.id (S1743ModelStack A))
    ⟨S1756LeftUnitorIso (S1756ToSource A)⟩
    ⟨S1756LeftUnitorIso (S1756ProjectionMap A)⟩
  exact ⟨e.trans e₀.symm⟩

/-- Apex rigidity implies the identity of the self-endomorphism `S1756End A`: apply it
to `S1784EndTrans A`, whose two projection comparisons are available unconditionally
(S1784), and use 2-Yoneda. -/
theorem S1831End_eq_one_of_apexRigid (A : S1728Cover) (h : S1831ApexRigid A) :
    S1756End A = 𝟙 (S1733Model A) := by
  obtain ⟨e⟩ := h (S1784EndTrans A) (S1784EndTrans_toSource A)
    (S1784EndTrans_projection A)
  have h1 := S1743YonedaEval_congr_iso (S1733Model A) (S1733Model A) e
  rwa [S1784EndTrans_eval, S1756YonedaEval_id] at h1

/-- Apex rigidity implies the strong 2-universal property: through the identity of
`S1756End A` and S1827's characterisation. -/
theorem S1831StrongSquare_of_apexRigid (A : S1728Cover) (h : S1831ApexRigid A) :
    S1831StrongSquare A :=
  (S1831StrongSquare_iff_end A).mpr (S1831End_eq_one_of_apexRigid A h)

/-- **The apex reduction.**  The strong 2-universal property of the actual square is
equivalent to 1-cell uniqueness at the square's own apex. -/
theorem S1831StrongSquare_iff_apexRigid (A : S1728Cover) :
    S1831StrongSquare A ↔ S1831ApexRigid A :=
  ⟨S1831ApexRigid_of_strongSquare A, S1831StrongSquare_of_apexRigid A⟩

/-- The first missing statement, in apex form. -/
def S1831ApexFirstMissing : Prop := ∀ A : S1728Cover, S1831ApexRigid A

/-- The first missing statement is exactly the apex form. -/
theorem S1831FirstMissing_iff_apexFirstMissing :
    S1831FirstMissing ↔ S1831ApexFirstMissing := by
  constructor
  · intro h A
    exact S1831ApexRigid_of_strongSquare A (h A)
  · intro h A
    exact S1831StrongSquare_of_apexRigid A (h A)

/-! ## 3. The missing 2-cells as equations on the affine model -/

/-- The 2-Yoneda evaluation of the lift of the square's own cone: the candidate
self-morphism `S_A ⟶ S_A` of the affine model supplied by the weak 2-universal
property.  Its being the identity is the first missing 2-cell
(`S1831OwnConeLift_iff_eval`). -/
noncomputable def S1831OwnConeEval (A : S1728Cover) :
    S1733Model A ⟶ S1733Model A :=
  S1743YonedaEval (S1733Model A) (S1733Model A) (S1784Counit A)

/-- **Unconditional**: the own-cone lift is a morphism over the base `Spec R'`.
This is the own-cone analogue of S1756's `S1756End_projection`, and it is the only
constraint on `S1831OwnConeEval A` that the recorded witness supplies. -/
theorem S1831OwnConeEval_projection (A : S1728Cover) :
    S1831OwnConeEval A ≫ S1756Projection A = S1756Projection A := by
  have hcomp := S1743YonedaEval_vcomp (S1733Model A) (S1733Model A) S1726AffineOver
    (S1784Counit A) (S1756ProjectionMap A)
  have hiso : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1784Counit A) (S1756ProjectionMap A))
      (S1756ProjectionMap A) :=
    (S1743BaseChange A).isPullback.liftToY (S1743ModelStack A) (S1784PullbackCone A)
  have heq : S1743YonedaEval (S1733Model A) S1726AffineOver
      (Pseudofunctor.StrongTrans.vcomp (S1784Counit A) (S1756ProjectionMap A))
      = S1743YonedaEval (S1733Model A) S1726AffineOver (S1756ProjectionMap A) :=
    S1743YonedaEval_congr_iso (S1733Model A) S1726AffineOver hiso
  rw [S1831OwnConeEval, ← S1756YonedaEval_projectionMap A, ← hcomp, heq]

/-- **Unconditional**: if the structure morphism of the affine model is a monomorphism
then the own-cone lift is the identity.  (Under this hypothesis the whole target is
available, S1827's monomorphism criterion; the point of the statement is that the
first missing 2-cell is discharged.) -/
theorem S1831OwnConeEval_eq_one_of_mono (A : S1728Cover)
    (hmono : Mono (S1756Projection A)) : S1831OwnConeEval A = 𝟙 (S1733Model A) := by
  haveI := hmono
  refine (cancel_mono (S1756Projection A)).mp ?_
  rw [Category.id_comp]
  exact S1831OwnConeEval_projection A

/-- The first missing 2-cell, in 2-Yoneda form: the own-cone lift is 2-isomorphic to
the identity exactly when its evaluation is the identity of `S_A`. -/
theorem S1831OwnConeLift_iff_eval (A : S1728Cover) :
    Nonempty (Iso (S1784Counit A)
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) ↔
      S1831OwnConeEval A = 𝟙 (S1733Model A) := by
  have h := S1756IsoIffEval (S1733Model A) (S1733Model A) (S1784Counit A)
    (Pseudofunctor.StrongTrans.id (S1743ModelStack A))
  rw [S1756YonedaEval_id] at h
  exact h

/-- The second missing 2-cell, in 2-Yoneda form: the own-cone lift is 2-isomorphic to
`toSource ; lift` exactly when its evaluation is `S1756End A`. -/
theorem S1831OwnConeLift_iff_end (A : S1728Cover) :
    Nonempty (Iso (S1784Counit A) (S1784EndTrans A)) ↔
      S1831OwnConeEval A = S1756End A := by
  have h := S1756IsoIffEval (S1733Model A) (S1733Model A) (S1784Counit A)
    (S1784EndTrans A)
  rwa [S1784EndTrans_eval] at h

/-- **The strong 2-universal property in scheme form.**  It is exactly the pair of
equations saying that the own-cone lift of the affine model is the identity and
equals the identity-point self-endomorphism `S1756End A`. -/
theorem S1831StrongSquare_iff_ownConeEval (A : S1728Cover) :
    S1831StrongSquare A ↔
      (S1831OwnConeEval A = 𝟙 (S1733Model A) ∧ S1831OwnConeEval A = S1756End A) := by
  rw [S1831StrongSquare_iff_counitData]
  unfold S1784CounitData
  rw [S1831OwnConeLift_iff_eval, S1831OwnConeLift_iff_end]

/-- **The strong 2-universal property in the symmetric scheme form**: both the
own-cone lift and the identity-point self-endomorphism of `S_A` are the identity. -/
theorem S1831StrongSquare_iff_eval_pair (A : S1728Cover) :
    S1831StrongSquare A ↔
      (S1831OwnConeEval A = 𝟙 (S1733Model A) ∧ S1756End A = 𝟙 (S1733Model A)) := by
  rw [S1831StrongSquare_iff_ownConeEval]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂.symm.trans h₁⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₁.trans h₂.symm⟩

/-! ## 4. The affine and finite-etale-algebra forms (S1781, S1799, S1816) -/

/-- The affine carrier bridge: the actual finite etale cover `S1816Obj A` of `Spec R'`
is carried by `Spec Gamma(S_A)`, the spectrum of the finite etale `R'`-algebra
`S1781Obj A`.  This is the affine `Spec`-`Gamma` identification of S1743/S1781. -/
theorem S1831CoverCarrier_iso (A : S1728Cover) :
    Nonempty ((S1816Obj A).carrier ≅ Scheme.Spec.obj (S1743ModelRing A)) := by
  haveI : IsAffine (S1733Model A).left := S1743Model_isAffine A
  exact ⟨Scheme.isoSpec (S1733Model A).left⟩

/-- The endomorphism of the finite etale `R'`-algebra `Gamma(S_A)` induced by the
identity-point self-endomorphism `S1756End A` of the affine model, in the
contravariant direction (S1781). -/
noncomputable def S1831AlgEnd (A : S1728Cover) : S1781Obj A ⟶ S1781Obj A :=
  S1781HomOfModelMap A A (S1756End A) (S1756End_projection A)

/-- **The target in finite-etale-algebra form**: the identity-point self-endomorphism
of the affine model is the identity if and only if the induced endomorphism of the
finite etale `R'`-algebra of sections is the identity (S1781's `Gamma`-`Spec` faithfulness). -/
theorem S1831AlgEnd_eq_one_iff (A : S1728Cover) :
    S1756End A = 𝟙 (S1733Model A) ↔ S1831AlgEnd A = 𝟙 (S1781Obj A) := by
  constructor
  · intro h
    exact (S1781HomOfModelMap_congr A A (S1756End_projection A)
      (show (𝟙 (S1733Model A)) ≫ S1756Projection A = S1756Projection A by simp) h).trans
      (S1781HomOfModelMap_id A (by simp))
  · intro h
    refine S1781_modelMap_ext A A (S1756End_projection A) (by simp) ?_
    exact h.trans (S1781HomOfModelMap_id A (by simp)).symm

/-- **The strong 2-universal property in finite-etale-algebra form.** -/
theorem S1831StrongSquare_iff_algEnd (A : S1728Cover) :
    S1831StrongSquare A ↔ S1831AlgEnd A = 𝟙 (S1781Obj A) :=
  (S1831StrongSquare_iff_end A).trans (S1831AlgEnd_eq_one_iff A)

/-- The endomorphism of the finite etale cover of `Spec R'` obtained from
`S1831AlgEnd A` along S1799's actual equivalence
`(FiniteEtale R')^op ≌ FiniteEtaleCover (Spec R')`. -/
noncomputable def S1831CoverEnd (A : S1728Cover) :
    (algToCover S1726CoordinateRing).obj (Opposite.op (S1781Obj A)) ⟶
      (algToCover S1726CoordinateRing).obj (Opposite.op (S1781Obj A)) :=
  (algToCover S1726CoordinateRing).map (S1831AlgEnd A).op

/-- **The target in the finite-etale-cover form of S1799**: the algebra endomorphism is
the identity if and only if its image under S1799's equivalence is the identity of the
finite etale cover. -/
theorem S1831CoverEnd_eq_one_iff (A : S1728Cover) :
    S1831AlgEnd A = 𝟙 (S1781Obj A) ↔
      S1831CoverEnd A = 𝟙 ((algToCover S1726CoordinateRing).obj
        (Opposite.op (S1781Obj A))) := by
  constructor
  · intro h
    change (algToCover S1726CoordinateRing).map (S1831AlgEnd A).op = 𝟙 _
    rw [h]
    simp
  · intro h
    have h1 : (algToCover S1726CoordinateRing).map (S1831AlgEnd A).op =
        (algToCover S1726CoordinateRing).map (𝟙 (Opposite.op (S1781Obj A))) := by
      change S1831CoverEnd A = _
      rw [h, (algToCover S1726CoordinateRing).map_id]
    have h2 := (algToCover S1726CoordinateRing).map_injective h1
    simpa using congrArg Quiver.Hom.unop h2

/-- **The strong 2-universal property as the identity of an endomorphism of the actual
finite etale cover of `Spec R'`** (through S1799). -/
theorem S1831StrongSquare_iff_coverEnd (A : S1728Cover) :
    S1831StrongSquare A ↔
      S1831CoverEnd A = 𝟙 ((algToCover S1726CoordinateRing).obj
        (Opposite.op (S1781Obj A))) :=
  (S1831StrongSquare_iff_algEnd A).trans (S1831CoverEnd_eq_one_iff A)

/-! ## 5. Positive instances and the boundary -/

/-- **Unconditional**: the comparison `toSource` has the recorded lift as an explicit
section on the source side, `lift ; toSource ≅ 1`.  Hence the recorded square is
a retraction square; the target asks for the other triangle. -/
theorem S1831Comparison_section (A : S1728Cover) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.id (S1743Source A))) :=
  ⟨S1784Section A⟩

/-- **Unconditional**: the comparison `toSource : Y(S_A) ⟶ A.source` is essentially
surjective on 1-cells: every point of the cover source is the composite of a point of
the affine model with `toSource`.  Hence the model covers the source, and the target
is exactly the question whether that cover is *injective* (1-cell uniqueness) rather
than whether it is surjective.  This is the retract picture of the recorded square. -/
theorem S1831Comparison_essSurj_objects (A : S1728Cover)
    (W : EtaleStackPseudofunctor S1726K)
    (x : Pseudofunctor.StrongTrans W (S1743Source A)) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) (S1756ToSource A)) x) := by
  refine ⟨?_⟩
  have h1 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp x (S1743Lift A)) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.vcomp x
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))) :=
    S1756AssociatorIso x (S1743Lift A) (S1756ToSource A)
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp x
        (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A)))
      (Pseudofunctor.StrongTrans.vcomp x
        (Pseudofunctor.StrongTrans.id (S1743Source A))) :=
    S1756WhiskerLeftIso x _ _ (S1784Section A)
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp x (Pseudofunctor.StrongTrans.id (S1743Source A)))
      x :=
    S1756RightUnitorIso x
  exact h1.trans (h2.trans h3)

/-- **A non-vacuous class**: whenever the structure morphism `S_A ⟶ Spec R'` is a
monomorphism, the actual square has the strong 2-universal property (S1827's
monomorphism criterion, re-exported in the locked form). -/
theorem S1831StrongSquare_of_mono (A : S1728Cover)
    (hmono : Mono (S1756Projection A)) : S1831StrongSquare A :=
  (S1831StrongSquare_iff_comparison A).mpr (S1827ComparisonQuasiEquiv_of_mono A hmono)

/-- The first missing statement in finite-etale-algebra form. -/
def S1831AlgFirstMissing : Prop := ∀ A : S1728Cover, S1831AlgEnd A = 𝟙 (S1781Obj A)

/-- The first missing statement is exactly its finite-etale-algebra form. -/
theorem S1831FirstMissing_iff_algFirstMissing :
    S1831FirstMissing ↔ S1831AlgFirstMissing := by
  constructor
  · intro h A
    exact (S1831StrongSquare_iff_algEnd A).mp (h A)
  · intro h A
    exact (S1831StrongSquare_iff_algEnd A).mpr (h A)

/-- The first missing statement is exactly the pair of scheme equations on the affine
model of every cover. -/
theorem S1831FirstMissing_iff_eval_pair :
    S1831FirstMissing ↔
      (∀ A : S1728Cover, S1831OwnConeEval A = 𝟙 (S1733Model A)) ∧
        (∀ A : S1728Cover, S1756End A = 𝟙 (S1733Model A)) := by
  constructor
  · intro h
    exact ⟨fun A => ((S1831StrongSquare_iff_eval_pair A).mp (h A)).1,
      fun A => ((S1831StrongSquare_iff_eval_pair A).mp (h A)).2⟩
  · rintro ⟨h1, h2⟩ A
    exact (S1831StrongSquare_iff_eval_pair A).mpr ⟨h1 A, h2 A⟩

/-- **The geometric input that would close the target**, named exactly: 1-cell
uniqueness of the actual identity-point finite etale base-change square at its own
apex.  By `S1831FirstMissing_iff_apexFirstMissing` it is exactly the target; it is
*not* a consequence of the recorded `TwoPullbackWitness` (S1801). -/
def S1831GeometricInput : Prop := S1831ApexFirstMissing

/-- The geometric input is exactly the first missing statement, hence exactly the
strong 2-universal property for every cover. -/
theorem S1831GeometricInput_iff_target :
    S1831GeometricInput ↔ S1831FirstMissing :=
  S1831FirstMissing_iff_apexFirstMissing.symm

/-- **The recorded witness does not imply the missing coherence** (S1801, re-exported):
there is a square satisfying all seven recorded fields whose cone comparison is not
essentially surjective.  This is why the first missing statement cannot be derived from
`TwoPullbackWitness` alone, without changing the recorded definition. -/
theorem S1831RecordedWitnessInsufficient :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor S1726K)
        (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness),
        S1827EssSurjOf sq w) :=
  S1827EssSurjNotFromWitness

/-- **The failure is the non-existence of a 2-cell**, not the incoherence of a chosen
one: in S1801's degenerate model no 2-cell from the identity to the constant lift exists
at all. -/
theorem S1831WitnessNotIso :
    ¬ Nonempty (Iso
      (Pseudofunctor.StrongTrans.id (S1801TwoStack S1726K))
      (S1801ConstZero S1726K (S1801TwoStack S1726K))) :=
  S1827WitnessNotIso

/-! ## 6. Checks -/

#check S1831StrongSquare
#check S1831StrongSquare_iff_unit
#check S1831StrongSquare_iff_end
#check S1831StrongSquare_iff_comparison
#check S1831StrongSquare_iff_recordedActual
#check S1831StrongSquare_iff_counitData
#check S1831FirstMissing
#check S1831FirstMissing_iff_S1827
#check S1831FirstMissing_iff_S1804
#check S1831FirstMissing_iff_S1756
#check S1831FirstMissing_iff_sourceRetraction
#check S1831FirstMissing_iff_S1758
#check S1831FirstMissing_iff_comparisonEquiv
#check S1831FirstMissing_to_counitData
#check S1831FirstMissing_closure
#check S1831ApexRigid
#check S1831ApexRigid_of_strongSquare
#check S1831End_eq_one_of_apexRigid
#check S1831StrongSquare_of_apexRigid
#check S1831StrongSquare_iff_apexRigid
#check S1831ApexFirstMissing
#check S1831FirstMissing_iff_apexFirstMissing
#check S1831OwnConeEval
#check S1831OwnConeEval_projection
#check S1831OwnConeEval_eq_one_of_mono
#check S1831OwnConeLift_iff_eval
#check S1831OwnConeLift_iff_end
#check S1831StrongSquare_iff_ownConeEval
#check S1831StrongSquare_iff_eval_pair
#check S1831CoverCarrier_iso
#check S1831AlgEnd
#check S1831AlgEnd_eq_one_iff
#check S1831StrongSquare_iff_algEnd
#check S1831CoverEnd
#check S1831CoverEnd_eq_one_iff
#check S1831StrongSquare_iff_coverEnd
#check S1831Comparison_section
#check S1831Comparison_essSurj_objects
#check S1831StrongSquare_of_mono
#check S1831AlgFirstMissing
#check S1831FirstMissing_iff_algFirstMissing
#check S1831FirstMissing_iff_eval_pair
#check S1831GeometricInput
#check S1831GeometricInput_iff_target
#check S1831RecordedWitnessInsufficient
#check S1831WitnessNotIso

#print axioms S1831StrongSquare_iff_unit
#print axioms S1831StrongSquare_iff_end
#print axioms S1831StrongSquare_iff_comparison
#print axioms S1831StrongSquare_iff_recordedActual
#print axioms S1831StrongSquare_iff_counitData
#print axioms S1831FirstMissing_iff_sourceRetraction
#print axioms S1831FirstMissing_closure
#print axioms S1831ApexRigid_of_strongSquare
#print axioms S1831End_eq_one_of_apexRigid
#print axioms S1831StrongSquare_of_apexRigid
#print axioms S1831StrongSquare_iff_apexRigid
#print axioms S1831FirstMissing_iff_apexFirstMissing
#print axioms S1831OwnConeEval_projection
#print axioms S1831OwnConeEval_eq_one_of_mono
#print axioms S1831OwnConeLift_iff_eval
#print axioms S1831OwnConeLift_iff_end
#print axioms S1831StrongSquare_iff_ownConeEval
#print axioms S1831StrongSquare_iff_eval_pair
#print axioms S1831CoverCarrier_iso
#print axioms S1831AlgEnd
#print axioms S1831AlgEnd_eq_one_iff
#print axioms S1831StrongSquare_iff_algEnd
#print axioms S1831CoverEnd
#print axioms S1831CoverEnd_eq_one_iff
#print axioms S1831StrongSquare_iff_coverEnd
#print axioms S1831FirstMissing_iff_algFirstMissing
#print axioms S1831FirstMissing_iff_eval_pair
#print axioms S1831Comparison_essSurj_objects
#print axioms S1831GeometricInput_iff_target
#print axioms S1831RecordedWitnessInsufficient
#print axioms S1831WitnessNotIso

end LeanFormal.IUT.XiFPaper.S1831StrongSquareGeometricActual
