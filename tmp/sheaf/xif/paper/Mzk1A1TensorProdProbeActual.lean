import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.Mzk1P3CanonicalEqualityObstructionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks

/-!
# A1 tensor/product probe: base-prime mismatch and dimension obstruction

The literal A1 equality-case target

  ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple
    ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b')

is **ill-typed** as a Lean statement.  For each bad place b',

  rootNormedExtension T b' : IntermediateField (rootBase T b') (rootNormedAmbient T b'),
  rootBase T b' = NormalizedCompletion (qVFamTensorPlace T b')
                = PadicScalarField (qVFamTensorPlace T b'),

and the only canonical algebra structure on rootNormedExtension T b' over a
p-adic base is the one produced by IntermediateField.algebra' from the
ambient Algebra (PadicScalarField (qVFamTensorPlace T b')) (rootNormedAmbient T b')
(sourceAlgebraicClosurePadicAlgebra + sourceAlgebraicClosureScalarTower), i.e.
over ℚ_[qVFamTensorP T b'], the rational prime of b' itself.  For b' ≠ b there
is no instance Algebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b'); the
typeclass search for

  Algebra ℚ_[qVFamTensorP T b] ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b')

therefore fails (checked by direct #synth / #check: both fail with "failed to
synthesize Algebra ℚ_[qVFamTensorP T b] ((b' : Bad ...) → rootNormedExtension T b')").
Consequently the exact ≃ₐ[ℚ_[qVFamTensorP T b]] statement is not even a
proposition.  This is a base-prime mismatch, not a missing proof.

Even after *imposing* per-factor ℚ_[qVFamTensorP T b]-algebra structures (the
hypotheses of the theorems below), the product statement is false as an
equality case: the existing canonical obstruction
(Mzk1P3CanonicalEqualityObstructionActual.canonical_card_lt_finrank) shows
that a product algebra equivalence with one nontrivial root factor forces
card Bad < finrank(block).  Instantiating at the qVFam one-factor block and
using qVFamTensorBlock_finrank, any such equivalence forces
card Bad < [rootBase T b : ℚ_[qVFamTensorP T b]].  Thus the A1 equality case
card Bad = finrank(block) forces every root factor to have ℚ_p-degree one
(qVFam_all_degree_one_of_card_eq_finrank); no equivalence can have both sides
of the same dimension once a root factor is nontrivial.

The genuinely true per-place pieces are:

* qVFamTensorBlock T b is the one-factor tensor of the **base** completion
  rootBase T b (same ℚ_[qVFamTensorP T b]-dimension; see
  qVFamTensorBlock_finrank);
* the root extension is a *separate* object, the one-factor tensor
  rootTensorBlock T b of rootNormedExtension T b, with dimension
  [rootNormedExtension T b : ℚ_[qVFamTensorP T b]] =
    [rootBase T b : ℚ_[qVFamTensorP T b]] * [rootNormedExtension T b : rootBase T b]
  (rootNormedExtension_finrank_tower).

There is no algebra equivalence between the base block and the root extension
unless the root extension is trivial (no_algEquiv_rootNormedExtension_of_one_lt_finrank).
The A1 consumer must therefore be re-routed to the per-place dimension /
log-volume relation (with the degree factor), not to an algebra equivalence.

No sorry, no axiom.
-/

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1A1TensorProdProbeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1P3CanonicalEqualityObstructionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The one-factor qVFam tensor block has the dimension of its base
completion rootBase T b over the matched prime qVFamTensorP T b.
This is the true dimension-content of the left-hand side of the A1 target. -/
theorem qVFamTensorBlock_finrank :
    Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b) =
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) := by
  change Module.finrank ℚ_[(qVFamTensorP T b)]
      (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple) =
    Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b)
  rw [finrank_arithmeticTensorTupleBlock]
  simp only [qVFamTensorV, qVFamTensorTuple, qVFamTensorPlaces, CommonPrimeCompletion,
    rootBase, PaperThetaRootObstructionActual.sourceRootField,
    Finset.univ_unique, Finset.prod_singleton]
  rfl

/-- The canonical algebra structure on the root extension is over the base
completion's prime qVFamTensorP T b (the IntermediateField.algebra' instance).
This is the per-factor matched-prime structure; it does **not** transport to a
different bad place b' with a different rational prime. -/
example : Algebra ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) := inferInstance

/-- Correct per-factor base prime: each root extension b' is a ℚ_[qVFamTensorP T b']-algebra
(not a ℚ_[qVFamTensorP T b]-algebra). -/
theorem rootNormedExtension_algebra_ownPrime (b' : Bad (nativePlaceSelection T)) :
    Nonempty (Algebra ℚ_[(qVFamTensorP T b')] (rootNormedExtension T b')) :=
  ⟨inferInstance⟩

/-- The correct per-rational-prime index set of the product side: the bad places
whose own base prime is p.  The whole product over Bad is not a single ℚ_[p]-algebra;
it splits into these fibers. -/
def badFiber (p : ℕ) : Type :=
  {b' : Bad (nativePlaceSelection T) // qVFamTensorP T b' = p}

/-- Tower-law dimension of the root extension over the matched prime. -/
theorem rootNormedExtension_finrank_tower :
    Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) =
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) *
        Module.finrank (rootBase T b) (rootNormedExtension T b) := by
  rw [Module.finrank_mul_finrank]

/-- The per-place, matched-prime A1 statement is false as soon as the root
extension is nontrivial: the base block has dimension [K_b:ℚ_p], while the
root extension has dimension [K_b:ℚ_p] * [L_b:K_b], and [L_b:K_b] > 1. -/
theorem no_algEquiv_rootNormedExtension_of_one_lt_finrank
    (h : 1 < Module.finrank (rootBase T b) (rootNormedExtension T b)) :
    ¬ Nonempty (qVFamTensorBlock T b ≃ₐ[ℚ_[(qVFamTensorP T b)]]
      rootNormedExtension T b) := by
  rintro ⟨e⟩
  have hfin := e.toLinearEquiv.finrank_eq
  rw [qVFamTensorBlock_finrank, rootNormedExtension_finrank_tower] at hfin
  have hpos : 0 < Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) := by
    rw [Module.finrank_pos_iff_of_free]
    infer_instance
  have hone : Module.finrank (rootBase T b) (rootNormedExtension T b) = 1 :=
    Nat.eq_of_mul_eq_mul_left hpos (by simpa using hfin.symm)
  omega

variable [Fintype (Bad (nativePlaceSelection T))]

/-- Conditional version of the exact A1 product statement with a common base
prime forced on every factor.  This definition only elaborates because the
per-factor algebra structures are supplied as hypotheses; without them the
common-base product is not even a ℚ_[qVFamTensorP T b]-algebra. -/
def A1ProductStatementWithCommonBase
    [∀ b', Algebra ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b')] : Prop :=
  Nonempty (qVFamTensorBlock T b ≃ₐ[ℚ_[(qVFamTensorP T b)]]
    ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b'))

/-- The existing canonical-equality obstruction, instantiated at the actual
qVFam one-factor block: an algebra equivalence to the product whose b0-factor
is nontrivial forces card Bad to be strictly smaller than the block dimension. -/
theorem qVFam_card_lt_finrank_of_algEquiv_pi
    [∀ b', Algebra ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b')]
    [∀ b', FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b')]
    (e : qVFamTensorBlock T b ≃ₐ[ℚ_[(qVFamTensorP T b)]]
      ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b'))
    (b0 : Bad (nativePlaceSelection T))
    (h0 : 1 < Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b0)) :
    Fintype.card (Bad (nativePlaceSelection T)) <
      Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b) := by
  have h := canonical_card_lt_finrank (l := l) T
    (K := T.arithmetic.F) (p := qVFamTensorP T b)
    (ι := qVFamTensorV) (V := fun _ => Unit)
    (qVFamTensorPlaces T b) (qVFamTensorTuple) e b0 h0
  simpa [qVFamTensorBlock] using h

/-- In particular, any such common-base A1 algebra equivalence forces
card Bad < [rootBase T b : ℚ_[qVFamTensorP T b]]. -/
theorem qVFam_card_lt_rootBase_finrank_of_algEquiv_pi
    [∀ b', Algebra ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b')]
    [∀ b', FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b')]
    (e : qVFamTensorBlock T b ≃ₐ[ℚ_[(qVFamTensorP T b)]]
      ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b'))
    (b0 : Bad (nativePlaceSelection T))
    (h0 : 1 < Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b0)) :
    Fintype.card (Bad (nativePlaceSelection T)) <
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) := by
  rw [← qVFamTensorBlock_finrank]
  exact qVFam_card_lt_finrank_of_algEquiv_pi T b e b0 h0

/-- Equality case: if a common-base A1 algebra equivalence exists and
card Bad = finrank(block), then every root-extension factor has ℚ_p-degree one.
This is the exact content of the A1 equality case for the actual qVFam data:
the product cannot meet the block at the same dimension unless the root
extension collapses to the base. -/
theorem qVFam_all_degree_one_of_card_eq_finrank
    [∀ b', Algebra ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b')]
    [∀ b', FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b')]
    (e : qVFamTensorBlock T b ≃ₐ[ℚ_[(qVFamTensorP T b)]]
      ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b'))
    (h : Fintype.card (Bad (nativePlaceSelection T)) =
      Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
    ∀ b', Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b') = 1 := by
  have h' : Fintype.card (Bad (nativePlaceSelection T)) =
      Module.finrank ℚ_[(qVFamTensorP T b)]
        (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple) := by
    simpa [qVFamTensorBlock] using h
  exact canonical_all_degree_one_of_card_eq_finrank (l := l) T
    (K := T.arithmetic.F) (p := qVFamTensorP T b)
    (ι := qVFamTensorV) (V := fun _ => Unit)
    (qVFamTensorPlaces T b) (qVFamTensorTuple) e h'

-- kernel / axiom audit of the probe (expected: no axioms beyond the standard three)
#print axioms qVFamTensorBlock_finrank
#print axioms rootNormedExtension_finrank_tower
#print axioms no_algEquiv_rootNormedExtension_of_one_lt_finrank
#print axioms qVFam_card_lt_finrank_of_algEquiv_pi
#print axioms qVFam_card_lt_rootBase_finrank_of_algEquiv_pi
#print axioms qVFam_all_degree_one_of_card_eq_finrank

end LeanFormal.IUT.XiFPaper.Mzk1A1TensorProdProbeActual
end
