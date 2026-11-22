import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual
import tmp.sheaf.xif.paper.S1311PaperInd1PermutationLiftActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S1321: the paper source contract with the capsule lift made explicit

S1311 proves that the current `OriginalInput` contract does not force the
source permutation to preserve the canonical capsule slice: for every supplied
source datum there is a legitimate `OriginalInput` (the row-shifted Haar
input) which has no `SourcePermutationCapsuleLift`.  The missing datum is not
a theorem about the fields of `OriginalInput`; it is an additional source
condition.

This file introduces a new paper source structure

  `PaperOriginalInput l V = OriginalInput l V + (forall n j, lift at n j)`

and leaves `OriginalInput` unchanged.  The lift is carried as data, not
constructed from `OriginalInput.family.permutation`: this is exactly the
missing source compatibility isolated in S1264/S1311.

The concrete Gaussian source is treated in two steps.

* For any actual `SourceDefinition31Data` we construct an actual inhabitant
  of `PaperOriginalInput` over the concrete source-Haar theater family.  Its
  family permutation is the identity, so the required lift is the actual
  identity lift.
* For the concrete Gaussian arithmetic `S1280Arithmetic l`, the source datum
  is the one assembled by S1280 from the actual D3/D4 data and the remaining
  D5-D9 clauses.  The first field of that datum which the tree does not
  determine is `torsion : SourceTorsionClause` (S1280).  Inside the torsion
  clause the first genuinely missing mathematical input recorded in S1298 is
  the Serre-style large-image statement, whose first component is a rank-two
  `ZMod l`-basis of the concrete `l`-torsion.

The file proves that the new structure adds no new obstruction beyond the
source datum: over the concrete Gaussian arithmetic, a `PaperOriginalInput`
exists if and only if a `SourceDefinition31Data` over that arithmetic exists.
Thus the only unresolved input is the concrete source contract itself, whose
first missing field is recorded exactly.

No `sorry`, new axiom, `PUnit`/ `True` gate, or fabricated lift is used.
The row-shifted counterexample is not imported as a field; the structure is
not claimed to be derivable from `OriginalInput` alone.
-/

namespace LeanFormal.IUT.XiFPaper.S1321PaperOriginalInputActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

universe ua uv upi umon ui

/-! ## 1. The new paper source contract -/

/-- The paper source input: the old `OriginalInput` together with the source
    compatibility that S1311 showed is not forced by the old fields.

    The field says that for every arithmetic-holomorphic index `n` and every
    capsule level `j`, the source family permutation has a capsule-level
    realization.  The realization is data: it is not a theorem about
    `OriginalInput`, and no such realization is constructed from
    `OriginalInput.family.permutation` in this file. -/
structure PaperOriginalInput (l : PrimeGeFive) (V : Type uv)
    extends OriginalInput.{ua, uv, upi, umon, ui} l V where
  sourcePermutationCapsuleLift :
    ∀ (n : Int) (j : Fin (capsuleLevels l)),
      SourcePermutationCapsuleLift toOriginalInput n j

namespace PaperOriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (P : PaperOriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The explicit lift at a fixed `n` and capsule level `j`. -/
def lift (n : Int) (j : Fin (capsuleLevels l)) :
    SourcePermutationCapsuleLift P.toOriginalInput n j :=
  P.sourcePermutationCapsuleLift n j

@[simp] theorem lift_apply (n : Int) (j : Fin (capsuleLevels l)) :
    P.lift n j = P.sourcePermutationCapsuleLift n j := rfl

/-- The exact index compatibility carried by the paper source field. -/
theorem lift_index_compat (n : Int) (j : Fin (capsuleLevels l))
    (i : Capsule j.val) :
    P.toOriginalInput.index_equiv
        (P.toOriginalInput.family.permutation
          (P.toOriginalInput.indexOf
            ((canonicalCapsuleTheaterAssignment P.toOriginalInput n).index j i).1
            ((canonicalCapsuleTheaterAssignment P.toOriginalInput n).index j i).2)) =
      (canonicalCapsuleTheaterAssignment P.toOriginalInput n).index j
        ((P.lift n j).perm i) :=
  (P.lift n j).index_compat i

/-- Every paper input gives a lift at every `n` and `j`. -/
theorem lift_nonempty (n : Int) (j : Fin (capsuleLevels l)) :
    Nonempty (SourcePermutationCapsuleLift P.toOriginalInput n j) :=
  ⟨P.lift n j⟩

end PaperOriginalInput

/-! ## 2. The identity lift for the concrete source-Haar family -/

/-- The actual identity lift for the concrete source-Haar input associated to
    any actual source datum.  The family permutation of
    `sourceHaarActualOriginalInput` is the identity, so the canonical slice is
    fixed and the capsule permutation is the identity. -/
noncomputable def sourceHaarActualCapsuleLift
    (S : SourceDefinition31Data.{ua} l) (n : Int)
    (j : Fin (capsuleLevels l)) :
    SourcePermutationCapsuleLift
      (sourceHaarActualOriginalInput (l := l) S) n j where
  perm := Equiv.refl (Capsule j.val)
  index_compat := by
    intro i
    simp [sourceHaarActualOriginalInput, sourceHaarActualFamily,
      canonicalCapsuleTheaterAssignment, OriginalInput.indexOf]
    rfl

/-- The actual inhabitant of `PaperOriginalInput` over the concrete
    source-Haar family, for any supplied actual source datum. -/
noncomputable def sourceHaarActualPaperOriginalInput
    (S : SourceDefinition31Data.{ua} l) :
    PaperOriginalInput.{ua, 0, 0, 0, 0} l Unit where
  toOriginalInput := sourceHaarActualOriginalInput (l := l) S
  sourcePermutationCapsuleLift := sourceHaarActualCapsuleLift (l := l) S

@[simp] theorem sourceHaarActualPaperOriginalInput_toOriginalInput
    (S : SourceDefinition31Data.{ua} l) :
    (sourceHaarActualPaperOriginalInput (l := l) S).toOriginalInput =
      sourceHaarActualOriginalInput (l := l) S := rfl

@[simp] theorem sourceHaarActualPaperOriginalInput_lift
    (S : SourceDefinition31Data.{ua} l) (n : Int)
    (j : Fin (capsuleLevels l)) :
    (sourceHaarActualPaperOriginalInput (l := l) S).sourcePermutationCapsuleLift
        n j =
      sourceHaarActualCapsuleLift (l := l) S n j := rfl

/-- The identity inhabitant has the explicit lift at every index. -/
theorem sourceHaarActualPaperOriginalInput_lift_nonempty
    (S : SourceDefinition31Data.{ua} l) (n : Int)
    (j : Fin (capsuleLevels l)) :
    Nonempty (SourcePermutationCapsuleLift
      (sourceHaarActualOriginalInput (l := l) S) n j) :=
  ⟨sourceHaarActualCapsuleLift (l := l) S n j⟩

/-! ## 3. The lift is not a consequence of the old source contract -/

/-- S1311's exact non-uniformity statement: there is no construction of the
    capsule lift from the `OriginalInput` fields alone.  For every supplied
    source datum, the row-shifted Haar input is a legitimate `OriginalInput`
    with no lift at `n = 0` on the capsule `{0,1}`. -/
theorem no_uniform_sourcePermutationCapsuleLift
    (S : SourceDefinition31Data.{ua} l) :
    ¬ ∀ (I : OriginalInput.{ua, 0, 0, 0, 0} l Unit)
        (n : Int) (j : Fin (capsuleLevels l)),
        Nonempty (SourcePermutationCapsuleLift I n j) :=
  LeanFormal.IUT.XiFPaper.S1311PaperInd1PermutationLiftActual.sourcePermutationCapsuleLift_not_uniform
    (l := l) S

/-- In particular, there is no uniform forgetful map from `OriginalInput` to
    `PaperOriginalInput`: such a map would produce the missing lift for every
    old input, contradicting S1311.  Hence the new field is a genuine
    strengthening, not a repackaging of `OriginalInput`. -/
theorem no_uniform_paperOriginalInput
    (S : SourceDefinition31Data.{ua} l) :
    ¬ ∀ (I : OriginalInput.{ua, 0, 0, 0, 0} l Unit),
        Nonempty {P : PaperOriginalInput.{ua, 0, 0, 0, 0} l Unit //
          P.toOriginalInput = I} := by
  intro h
  apply no_uniform_sourcePermutationCapsuleLift (l := l) S
  intro I n j
  rcases h I with ⟨P, hP⟩
  rw [← hP]
  exact ⟨P.sourcePermutationCapsuleLift n j⟩

/-! ## 4. The lift supplies the paper Ind1 capsule permutation -/

/-- The paper Ind1 candidate built from a `PaperOriginalInput`: its label
    permutation is the capsule permutation supplied by the source lift, and its
    components are the actual source prime-strip links. -/
noncomputable def paperInd1Candidate
    (P : PaperOriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    PrcAutomorphism (canonicalCapsuleTheaterAssignment P.toOriginalInput n) j :=
  PrcAutomorphism.ofPerm
    (canonicalCapsuleTheaterAssignment P.toOriginalInput n) j
    (P.sourcePermutationCapsuleLift n j).perm

@[simp] theorem paperInd1Candidate_perm
    (P : PaperOriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    (paperInd1Candidate P n j).perm =
      (P.sourcePermutationCapsuleLift n j).perm := rfl

/-- The component is the actual source link between the selected theater and
    its image under the capsule permutation. -/
@[simp] theorem paperInd1Candidate_component
    (P : PaperOriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    (paperInd1Candidate P n j).component i =
      PrcTransition (canonicalCapsuleTheaterAssignment P.toOriginalInput n) j i
        ((P.sourcePermutationCapsuleLift n j).perm i) := rfl

/-! ## 5. The concrete Gaussian source: conditional inhabitant -/

/-- The concrete Gaussian arithmetic input of S1280. -/
abbrev ConcreteGaussianArithmetic (l : PrimeGeFive) :=
  S1280Arithmetic l

/-- The concrete Gaussian `PaperOriginalInput` from the remaining actual source
    clauses.  The assumptions are exactly S1280's remaining D5-D9 data; no
    source clause is invented.  This is an inhabitant of the new structure for
    every supplied actual source datum over the concrete Gaussian arithmetic. -/
noncomputable def concreteGaussianPaperOriginalInput
    (l : PrimeGeFive) (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    PaperOriginalInput.{0, 0, 0, 0, 0} l Unit :=
  sourceHaarActualPaperOriginalInput (l := l)
    (S1280SourceData_of_remaining l R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat)

/-- The underlying arithmetic of the concrete Gaussian paper input is the
    actual concrete Gaussian arithmetic. -/
theorem concreteGaussianPaperOriginalInput_arithmetic
    (l : PrimeGeFive) (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (concreteGaussianPaperOriginalInput l R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat).toOriginalInput.initial.arithmetic =
        S1280Arithmetic l := by
  simp [concreteGaussianPaperOriginalInput, sourceHaarActualPaperOriginalInput,
    sourceHaarActualOriginalInput, S1280SourceData_of_remaining_arithmetic]

/-- The first field of the concrete Gaussian source consumed by the paper input
    is exactly the supplied torsion clause `R.torsion`.  Thus the conditional
    construction is explicitly indexed by the first missing field. -/
theorem concreteGaussianPaperOriginalInput_torsion
    (l : PrimeGeFive) (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (concreteGaussianPaperOriginalInput l R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat).toOriginalInput.initial.torsion =
        R.torsion := by
  simp [concreteGaussianPaperOriginalInput, sourceHaarActualPaperOriginalInput,
    sourceHaarActualOriginalInput, S1280SourceData_of_remaining_torsion]

/-- The conditional concrete Gaussian paper input carries its explicit lift. -/
theorem concreteGaussianPaperOriginalInput_lift_nonempty
    (l : PrimeGeFive) (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    Nonempty (SourcePermutationCapsuleLift
      (concreteGaussianPaperOriginalInput l R redCompat hredCompat
        torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
        cusCompat hcusCompat).toOriginalInput 0
      ⟨1, one_lt_capsuleLevels l⟩) :=
  ⟨(concreteGaussianPaperOriginalInput l R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat).sourcePermutationCapsuleLift 0
      ⟨1, one_lt_capsuleLevels l⟩⟩

/-! ## 6. The exact first field of the concrete Gaussian source -/

/-- The first field of `SourceDefinition31Data l` that the concrete Gaussian
    data of S1280 does not determine: the D5 torsion clause. -/
abbrev concreteGaussianFirstMissingField (l : PrimeGeFive) : Type 1 :=
  S1280FirstMissingField l

/-- The first missing field is literally the torsion clause. -/
theorem concreteGaussianFirstMissingField_eq_torsionClause
    (l : PrimeGeFive) :
    concreteGaussianFirstMissingField l = SourceTorsionClause.{0, 0, 0} l :=
  rfl

/-- Every actual source datum over the concrete Gaussian arithmetic already
    has the first missing field.  The field is therefore a genuine projection
    of the source contract, not an extra assumption of the paper input. -/
theorem concreteGaussianFirstMissingField_of_sourceData
    {l : PrimeGeFive} (S : SourceDefinition31Data.{0} l) :
    Nonempty (concreteGaussianFirstMissingField l) :=
  S1280FirstMissingField_of_sourceData S

/-- The first genuinely missing mathematical input recorded in S1298 inside
    that torsion clause: the Serre-style large-image statement for the concrete
    Gaussian curve. -/
abbrev concreteGaussianLargeImageField (l : PrimeGeFive) : Prop :=
  SerreStyleLargeImageStatement (S1280Arithmetic l).curve l

/-- The large-image statement begins with a rank-two `ZMod l`-basis of the
    concrete `l`-torsion.  This is the exact first component of the first
    missing source field. -/
theorem concreteGaussianLargeImageField_supplies_rankTwoBasis
    (l : PrimeGeFive) (h : concreteGaussianLargeImageField l) :
    Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      (S1280Arithmetic l).curve.LTorsion l) := by
  rcases h with ⟨basis, _⟩
  exact ⟨basis⟩

/-! ## 7. The new structure adds no obstruction beyond the source datum -/

/-- The paper input is over the concrete Gaussian arithmetic. -/
def HasConcreteGaussianArithmetic {l : PrimeGeFive}
    (P : PaperOriginalInput.{0, 0, 0, 0, 0} l Unit) : Prop :=
  P.toOriginalInput.initial.arithmetic = S1280Arithmetic l

/-- Over the concrete Gaussian arithmetic, a `PaperOriginalInput` exists
    exactly when a `SourceDefinition31Data` over that arithmetic exists.  Thus
    the lift field is the only new source condition, and it creates no
    additional obstruction once the source datum is supplied. -/
theorem concreteGaussianPaperOriginalInput_nonempty_iff_sourceData
    (l : PrimeGeFive) :
    Nonempty {P : PaperOriginalInput.{0, 0, 0, 0, 0} l Unit //
        HasConcreteGaussianArithmetic P} ↔
      Nonempty {S : SourceDefinition31Data.{0} l //
        S.arithmetic = S1280Arithmetic l} := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.toOriginalInput.initial, hP⟩
  · rintro ⟨S, hS⟩
    refine ⟨sourceHaarActualPaperOriginalInput (l := l) S, ?_⟩
    simpa [HasConcreteGaussianArithmetic, sourceHaarActualPaperOriginalInput,
      sourceHaarActualOriginalInput] using hS

/-- Consequently the only way the concrete Gaussian paper source can fail is
    failure of the concrete source datum itself; the lift is not a second
    independent obstruction. -/
theorem concreteGaussianPaperOriginalInput_no_sourceData
    (l : PrimeGeFive)
    (h : ¬ Nonempty {S : SourceDefinition31Data.{0} l //
      S.arithmetic = S1280Arithmetic l}) :
    ¬ Nonempty {P : PaperOriginalInput.{0, 0, 0, 0, 0} l Unit //
      HasConcreteGaussianArithmetic P} := by
  intro hP
  exact h (concreteGaussianPaperOriginalInput_nonempty_iff_sourceData l |>.mp hP)

/-! ## 8. Axiom probes -/

#print axioms sourceHaarActualCapsuleLift
#print axioms sourceHaarActualPaperOriginalInput
#print axioms sourceHaarActualPaperOriginalInput_lift_nonempty
#print axioms paperInd1Candidate
#print axioms no_uniform_sourcePermutationCapsuleLift
#print axioms no_uniform_paperOriginalInput
#print axioms concreteGaussianPaperOriginalInput
#print axioms concreteGaussianPaperOriginalInput_arithmetic
#print axioms concreteGaussianPaperOriginalInput_torsion
#print axioms concreteGaussianPaperOriginalInput_lift_nonempty
#print axioms concreteGaussianFirstMissingField_eq_torsionClause
#print axioms concreteGaussianLargeImageField_supplies_rankTwoBasis
#print axioms concreteGaussianPaperOriginalInput_nonempty_iff_sourceData
#print axioms concreteGaussianPaperOriginalInput_no_sourceData

end LeanFormal.IUT.XiFPaper.S1321PaperOriginalInputActual
