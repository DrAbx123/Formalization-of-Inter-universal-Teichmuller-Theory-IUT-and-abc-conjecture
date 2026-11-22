import tmp.sheaf.xif.paper.MultiradialProcessionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S1264: actual source capsule, log-shell contract, and Ind1 candidate

Source anchor: the capsule data layer of
`LeanFormal/IUT/IUTIII/Theorem311/SourceProcessionCapsuleData.lean` and
`SourceProcessionCapsuleOriginalInput.lean`, with the one-point `PUnit`
completion of the latter deliberately not used.

For every `I : OriginalInput l V` this file constructs:

* a `CapsuleTheaterAssignment` whose selected theaters are the actual source
  theaters `I.theaterAt (i,n)` (the canonical data-layer dictionary already
  isolated in `SourceProcessionCapsuleOriginalInput`; `OriginalInput` itself
  has no capsule-to-source index map);
* a `SourceProcessionCapsuleContract` over the actual coefficient field
  `ℚ_[l.value]`, the actual rational place type at `l`, the actual finite
  places of `I.initial.arithmetic.K` above `l`, and the actual common-prime
  completions at those places.  The log-shell carrier is therefore not the
  `PUnit`/`unitLogShellFamily` model; each shell is the actual local field
  `CommonPrimeCompletion v`, and the actual integral log-shell
  `integralLogShell` is recorded and proved equal to the source local datum.
* an actual Ind1 candidate at every capsule level: the label-reversal
  permutation `Fin.revPerm` together with the actual source prime-strip links
  `I.linkAt` between the selected theaters (`PrcAutomorphism.ofPerm`).

The paper's own Ind1 automorphism would have to come from
`I.family.permutation`.  The exact first source datum missing for that is
recorded as `SourcePermutationCapsuleLift.index_compat`: no source theorem
states that `family.permutation` preserves the canonical slice
`i |-> (i,n)`.  No inhabitant of that structure is asserted, and the actual
label-reversal candidate is not renamed into the paper's automorphism.

No `PUnit`, `True`, `Nonempty` gate, `sorry`, or new axiom is used.
-/

namespace LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-- The rational prime `l` is prime, as an instance for the local field
    constructions.  This is the actual prime carried by `l`, not an extra
    hypothesis. -/
local instance factPrimeOfPrimeGeFive (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. Actual places and actual log-shell carriers -/

/-- The actual rational finite place at the prime `l`.  This is the genuine
    `VQ` used by the arithmetic packet: the set of rational valuations at the
    fixed rational prime `l` (a one-element set, represented by its actual
    finite place, not by `PUnit`). -/
abbrev RationalPlaceAt (l : PrimeGeFive) : Type :=
  FinitePlaceAtPrime ℚ l.value

/-- The actual finite places of the source number field `K` above `l`. -/
abbrev ActualPlace (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Type _ :=
  FinitePlaceAtPrime I.initial.arithmetic.K l.value

/-- The actual log-shell carrier at every capsule label, rational place, and
    finite place `v`: the common-prime completion of `K` at `v`, with its
    actual `ℚ_[l.value]`-module structure. -/
noncomputable def actualLogShellFamily
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (j : Nat) :
    LogShellFamily ℚ_[l.value] (fun _ : RationalPlaceAt l => ActualPlace I) j where
  Shell := fun _ _ v => CommonPrimeCompletion v
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

/-- The carrier of the actual shell is exactly the common-prime completion of
    the actual finite place. -/
theorem actualLogShell_shell_eq_commonPrimeCompletion
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (j : Nat)
    (i : Capsule j) (vQ : RationalPlaceAt l) (v : ActualPlace I) :
    (actualLogShellFamily I j).Shell i vQ v = CommonPrimeCompletion v := rfl

/-- Each actual shell is a nontrivial local field: `0 ≠ 1`.  In particular the
    log-shell carrier is not `PUnit` and not the `unitLogShellFamily` model. -/
theorem actualLogShell_completion_zero_ne_one
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : ActualPlace I) :
    (0 : CommonPrimeCompletion v) ≠ 1 :=
  zero_ne_one

/-- The actual local log-shell datum at a finite place. -/
def actualLocalLogShell
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : ActualPlace I) : Set (CommonPrimeCompletion v) :=
  (sourceLocalLogShellDatum (p := l.value) v).logShell

/-- The local log-shell set is exactly the actual integral log-shell of the
    completion, by the source local log-shell theorem. -/
theorem actualLocalLogShell_eq_integralLogShell
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : ActualPlace I) :
    actualLocalLogShell I v =
      (integralLogShell (K := CommonPrimeCompletion v) (p := l.value) :
        Set (CommonPrimeCompletion v)) :=
  sourceLocalLogShellDatum_logShell_eq_integralLogShell (p := l.value) v

/-! ## 2. The actual contract built from the source theaters -/

/-- The actual label-reversal poly-isomorphism on the actual shell family.
    The label permutation is the genuine permutation `Fin.revPerm`; because the
    shell carrier is the same actual completion at every label, the shell
    equivalences are the canonical reflexive linear equivalences. -/
noncomputable def actualPolyIso
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (j : Nat) :
    PolyIsoAction (actualLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun i vQ v =>
    LinearEquiv.refl ℚ_[l.value] ((actualLogShellFamily I j).Shell i vQ v)

/-- The additional capsule data with actual theaters, actual places, actual
    completions as log-shells, and the actual label-reversal poly-isomorphism.
    The assignment is the canonical source-theater dictionary; the `n` index is
    the arithmetic-holomorphic index of the procession. -/
noncomputable def actualCapsuleData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    OriginalInputCapsuleData ℚ_[l.value] l V I where
  assignment := canonicalCapsuleTheaterAssignment I n
  n := n
  VQ := RationalPlaceAt l
  place := fun _ => ActualPlace I
  fintypePlace := fun _ => inferInstance
  logShell := fun j => actualLogShellFamily I j.val
  polyIso := fun j => actualPolyIso I j.val

/-- The actual source procession capsule contract for an arbitrary
    `I : OriginalInput l V`. -/
noncomputable def actualContract
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    SourceProcessionCapsuleContract ℚ_[l.value] l V I :=
  SourceProcessionCapsuleContract.ofOriginalInput ℚ_[l.value] I
    (actualCapsuleData I n)

@[simp] theorem actualContract_procession
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    (actualContract I n).procession =
      (canonicalCapsuleTheaterAssignment I n).toProcession n := rfl

@[simp] theorem actualContract_VQ
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    (actualContract I n).VQ = RationalPlaceAt l := rfl

@[simp] theorem actualContract_place
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    (actualContract I n).place = fun _ : RationalPlaceAt l => ActualPlace I := rfl

@[simp] theorem actualContract_logShell
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    (actualContract I n).logShell j = actualLogShellFamily I j.val := rfl

@[simp] theorem actualContract_polyIso
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    (actualContract I n).polyIso j = actualPolyIso I j.val := rfl

/-- The actual selected-source theaters of the canonical assignment are
    nonconstant. -/
theorem actualContract_theater_nontrivial
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((actualContract I n).procession).toPrimeStripOf.theater j i ≠
        ((actualContract I n).procession).toPrimeStripOf.theater j i' := by
  simpa [actualContract, actualCapsuleData] using
    canonicalCapsuleTheaterAssignment.theater_nontrivial I n

/-- The actual selected-source prime strips of the canonical assignment are
    nonconstant. -/
theorem actualContract_primeStrip_nontrivial
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    exists (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((actualContract I n).procession).toPrimeStripOf.primeStrip j i ≠
        ((actualContract I n).procession).toPrimeStripOf.primeStrip j i' := by
  simpa [actualContract, actualCapsuleData] using
    canonicalCapsuleTheaterAssignment.primeStrip_nontrivial I n

/-! ## 3. Actual Ind1 candidate: label reversal plus source strip links -/

/-- The actual Ind1 candidate at capsule level `j`: the label-reversal
    permutation `Fin.revPerm` together with the actual source links
    `I.linkAt` between the selected source theaters. -/
noncomputable def ind1Candidate
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    PrcAutomorphism (canonicalCapsuleTheaterAssignment I n) j :=
  PrcAutomorphism.ofPerm (canonicalCapsuleTheaterAssignment I n) j Fin.revPerm

/-- The permutation of the Ind1 candidate is the literal label reversal. -/
theorem ind1Candidate_perm
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    (ind1Candidate I n j).perm = Fin.revPerm := rfl

/-- The strip equivalence of the Ind1 candidate is the actual source
    prime-strip link between the selected theaters. -/
theorem ind1Candidate_component
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    (ind1Candidate I n j).component i =
      PrcTransition (canonicalCapsuleTheaterAssignment I n) j i (Fin.revPerm i) := rfl

/-- The Ind1 candidate acts on exactly the actual prime strips of the
    contract's procession. -/
theorem ind1Candidate_member_eq_contract
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    PrcMember (canonicalCapsuleTheaterAssignment I n) j i =
      ((actualContract I n).procession).toPrimeStripOf.primeStrip j i := rfl

/-- At level `1` the label reversal is the nontrivial swap `0 <-> 1`. -/
theorem finRevPerm_zero_two : (Fin.revPerm (0 : Fin 2)) = 1 := by
  norm_num [Fin.revPerm_apply, Fin.rev]

/-- The Ind1 candidate is a genuinely nontrivial label permutation already at
    capsule level `1`. -/
theorem ind1Candidate_perm_nontrivial
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    (ind1Candidate I n ⟨1, one_lt_capsuleLevels l⟩).perm ≠
      Equiv.refl (Capsule (1 : Nat)) := by
  intro h
  have h0 := congrArg
    (fun e : Capsule (1 : Nat) ≃ Capsule (1 : Nat) => e 0) h
  rw [ind1Candidate_perm] at h0
  simp [Fin.revPerm_apply, Fin.rev] at h0

/-- The contract's actual poly-isomorphism has the same nontrivial label
    reversal at level `1`. -/
theorem actualPolyIso_labelPerm_nontrivial
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    (actualPolyIso I 1).labelPerm ≠ Equiv.refl (Capsule (1 : Nat)) := by
  intro h
  have h0 := congrArg
    (fun e : Capsule (1 : Nat) ≃ Capsule (1 : Nat) => e 0) h
  simp [actualPolyIso, Fin.revPerm_apply, Fin.rev] at h0

/-! ## 4. Exact first missing source field for the paper's Ind1 -/

/-- Exact source datum missing to turn `I.family.permutation` into a capsule
    automorphism for the canonical assignment `(i,n)`.

    `OriginalInput` supplies only `family.permutation : Equiv.Perm family.index`.
    It does not supply a capsule permutation `perm` whose induced source-index
    permutation agrees with `family.permutation` on the canonical slice
    `i |-> (i,n)`.  The field `index_compat` is precisely that missing equation.
    No inhabitant of this structure is constructed in this file. -/
structure SourcePermutationCapsuleLift
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) where
  perm : Capsule j.val ≃ Capsule j.val
  index_compat : forall i : Capsule j.val,
    I.index_equiv (I.family.permutation
      (I.indexOf ((canonicalCapsuleTheaterAssignment I n).index j i).1
        ((canonicalCapsuleTheaterAssignment I n).index j i).2)) =
      (canonicalCapsuleTheaterAssignment I n).index j (perm i)

/-! ## 5. Axiom probes -/

#print axioms actualContract
#print axioms actualContract_theater_nontrivial
#print axioms actualContract_primeStrip_nontrivial
#print axioms actualLogShell_completion_zero_ne_one
#print axioms actualLocalLogShell_eq_integralLogShell
#print axioms ind1Candidate
#print axioms ind1Candidate_perm_nontrivial
#print axioms actualPolyIso_labelPerm_nontrivial

end LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual