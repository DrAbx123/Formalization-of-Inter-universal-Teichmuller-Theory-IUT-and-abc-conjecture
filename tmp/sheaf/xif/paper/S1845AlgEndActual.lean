import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import tmp.sheaf.xif.paper.S1839SliceFillingActual
import tmp.sheaf.xif.paper.S1841SourceRepresentabilityActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1845AlgEndActual

open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1781AffineCoverAlgebrasSecondActual
open LeanFormal.IUT.XiFPaper.S1831StrongSquareGeometricActual
open LeanFormal.IUT.XiFPaper.S1839SliceFillingActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual

/-!
# S1845: the identity-point self-endomorphism in finite-etale algebra form

## The target

For a cover `A : S1728Cover`, S1831 defines

    S1831AlgEnd A : S1781Obj A ⟶ S1781Obj A,

the endomorphism of the finite-etale `R'`-algebra `Γ(S_A)` induced by the
identity-point self-endomorphism `S1756End A` of the affine model.  The target
under investigation is

    S1845AlgEndTarget : ∀ A, S1831AlgEnd A = 𝟙 (S1781Obj A).

## What is established here (unconditional)

1. The target is exactly S1756's missing statement `S1756End A = 1`
   (`S1845AlgEndTarget_iff_S1756FirstMissing`), hence exactly
   `S1831AlgFirstMissing` and `S1841FirstMissing`.

2. **The S1839 terminal cover is a positive instance.**  Its affine model is
   `Spec R'` itself with identity structure morphism, so
   `S1756Projection = 𝟙`, and the projection equation forces
   `S1756End = 𝟙`; consequently `S1831AlgEnd = 𝟙`.

3. **The S1839 constant endomorphism is not a counterexample.**  It is an
   endomorphism of `Spec R'` over `Spec F'`, not over the base `Spec R'`.
   The projection equation for the terminal cover is `g ≫ 𝟙 = 𝟙`, i.e. `g = 𝟙`,
   so the non-identity constant endomorphism violates exactly the condition
   satisfied by `S1756End` (`S1845ConstEnd_not_projection`).

## The honest boundary

`S1845AlgEndTarget` is **not proved** here.  It is exactly the source
representability statement of S1756/S1831/S1841, which S1831, S1841, S1843 and
S1844 show is not a consequence of the recorded weak two-pullback witness.  In
particular S1844 constructs a square with representable apex and actual stack
objects whose recorded witness holds but whose cone comparison is not
essentially surjective; it does not construct a cover.  No fake cover, fake
2-cell or axiom is introduced below; the target is recorded as an open
proposition.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound`; see the audit block.
-/

/-! ## 1. The target in finite-etale-algebra form -/

/-- The target: every identity-point finite-etale-algebra endomorphism is the
identity. -/
def S1845AlgEndTarget : Prop :=
  ∀ A : S1728Cover, S1831AlgEnd A = 𝟙 (S1781Obj A)

/-- The algebra-form target is exactly the scheme-level S1756 missing
statement. -/
theorem S1845AlgEndTarget_iff_S1756FirstMissing :
    S1845AlgEndTarget ↔ S1756FirstMissing := by
  unfold S1845AlgEndTarget S1756FirstMissing
  exact forall_congr' fun A => (S1831AlgEnd_eq_one_iff A).symm

/-- The target is exactly S1831's algebra-form first missing statement. -/
theorem S1845AlgEndTarget_iff_S1831AlgFirstMissing :
    S1845AlgEndTarget ↔ S1831AlgFirstMissing :=
  Iff.rfl

/-- The target is exactly the source-representability statement of S1841. -/
theorem S1845AlgEndTarget_iff_S1841FirstMissing :
    S1845AlgEndTarget ↔ S1841FirstMissing := by
  rw [S1845AlgEndTarget_iff_S1756FirstMissing]
  exact (S1841FirstMissing_iff_S1756).symm

/-! ## 2. The terminal cover: a positive instance -/

/-- The S1839 terminal cover, whose affine model is `Spec R'` with identity
structure morphism. -/
abbrev S1845TerminalCover : S1728Cover := S1839TerminalCover

/-- The structure morphism of the terminal cover is the identity. -/
theorem S1845TerminalProjection :
    S1756Projection S1845TerminalCover =
      (𝟙 S1726AffineOver : S1733Model S1845TerminalCover ⟶ S1726AffineOver) := rfl

/-- The identity-point self-endomorphism of the terminal cover is the identity,
because the structure morphism is the identity. -/
theorem S1845TerminalEnd :
    S1756End S1845TerminalCover = 𝟙 (S1733Model S1845TerminalCover) := by
  haveI : Mono (S1756Projection S1845TerminalCover) := by
    rw [S1845TerminalProjection]
    change Mono (𝟙 (S1733Model S1845TerminalCover) :
      S1733Model S1845TerminalCover ⟶ S1733Model S1845TerminalCover)
    infer_instance
  refine (cancel_mono (S1756Projection S1845TerminalCover)).mp ?_
  simpa using S1756End_projection S1845TerminalCover

/-- **Positive instance of the target**: the terminal cover satisfies
`S1831AlgEnd = 1`. -/
theorem S1845TerminalAlgEnd :
    S1831AlgEnd S1845TerminalCover = 𝟙 (S1781Obj S1845TerminalCover) :=
  (S1831AlgEnd_eq_one_iff S1845TerminalCover).mp S1845TerminalEnd

/-- Consequently the terminal cover is not a counterexample to the target. -/
theorem S1845Terminal_not_counterexample :
    S1831AlgEnd S1845TerminalCover = 𝟙 (S1781Obj S1845TerminalCover) :=
  S1845TerminalAlgEnd

/-! ## 3. The S1839 constant endomorphism is not a model endomorphism -/

/-- The S1839 constant endomorphism violates the projection equation of the
terminal cover.  Since the terminal projection is `𝟙 (Spec R')`, the projection
equation is `g ≫ 𝟙 = 𝟙`, i.e. `g = 𝟙`, whereas `S1839ConstEnd ≠ 𝟙`.  Hence it
cannot be the endomorphism `S1756End` (nor the model endomorphism underlying
`S1831AlgEnd`) of the terminal cover. -/
theorem S1845ConstEnd_not_projection :
    S1839ConstEnd ≫ S1756Projection S1845TerminalCover ≠
      S1756Projection S1845TerminalCover := by
  rw [S1845TerminalProjection, Category.comp_id]
  exact S1839ConstEnd_ne_id

/-- The constant endomorphism is not the identity-point self-endomorphism of the
terminal cover. -/
theorem S1845ConstEnd_ne_terminalEnd :
    S1839ConstEnd ≠ S1756End S1845TerminalCover := by
  intro h
  rw [S1845TerminalEnd] at h
  exact S1839ConstEnd_ne_id h

/-- The constant endomorphism therefore cannot be the model endomorphism whose
finite-etale-algebra shadow is `S1831AlgEnd`: the latter is over the base and
the former is not. -/
theorem S1845ConstEnd_not_algEnd_shadow :
    ¬ (∃ (h : S1839ConstEnd ≫ S1756Projection S1845TerminalCover =
        S1756Projection S1845TerminalCover),
      S1831AlgEnd S1845TerminalCover = 𝟙 (S1781Obj S1845TerminalCover)) := by
  rintro ⟨h, -⟩
  exact S1845ConstEnd_not_projection h

/-! ## 4. The exact open statement -/

/-- The open statement of this file: the algebra-form identity-point
self-endomorphism is the identity for every cover.  It is definitionally
S1831's and S1841's first missing statement. -/
def S1845FirstMissing : Prop := S1845AlgEndTarget

/-- The open statement is exactly S1756's source representability. -/
theorem S1845FirstMissing_iff :
    S1845FirstMissing ↔ S1756FirstMissing :=
  S1845AlgEndTarget_iff_S1756FirstMissing

/-! ## 5. Checks and axiom audit -/

#check S1845AlgEndTarget
#check S1845AlgEndTarget_iff_S1756FirstMissing
#check S1845TerminalEnd
#check S1845TerminalAlgEnd
#check S1845ConstEnd_not_projection
#check S1845ConstEnd_ne_terminalEnd
#check S1845FirstMissing

#print axioms S1845AlgEndTarget_iff_S1756FirstMissing
#print axioms S1845AlgEndTarget_iff_S1841FirstMissing
#print axioms S1845TerminalEnd
#print axioms S1845TerminalAlgEnd
#print axioms S1845ConstEnd_not_projection
#print axioms S1845ConstEnd_ne_terminalEnd

end LeanFormal.IUT.XiFPaper.S1845AlgEndActual