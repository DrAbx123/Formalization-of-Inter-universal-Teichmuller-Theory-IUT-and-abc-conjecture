import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual
import tmp.sheaf.xif.paper.S1313IntegralLogShellContractActual
import tmp.sheaf.xif.paper.S1318IntegralCapsuleZpHomActual

/-!
# S1389: the actual poly-isomorphisms against the paper's Ind1 action

The actual capsule files S1264, S1313 and S1318 each contain a
`PolyIsoAction`.  This file isolates exactly how far that action agrees with
the paper's Ind1 poly-isomorphism.

The paper's Ind1 indeterminacy is the indeterminacy induced by automorphisms of
the procession of `D⊢`-prime-strips, i.e. a permutation of the capsule labels
together with the isomorphisms of the individual prime-strips
([IUTchIII, Introduction; Theorem 3.11, (i)]).  At the data layer the actual
source automorphism is `ind1Candidate` of S1264: its label permutation is
`Fin.revPerm` and its strip components are the actual source links
`I.linkAt`.

The first field of every actual `PolyIsoAction` is its `labelPerm`.  We prove
that this field is *literally* the source permutation `Fin.revPerm` in all
three files.  The second field is the shell equivalence.  In S1264 and S1313 it
is the canonical reflexive equivalence on the actual common-prime completion /
integral log-shell; those two actions are therefore exactly the source Ind1
action with the identity shell transport.  In S1318 the shell equivalence is
`-1`, an actual `ℤ_[p]`-linear automorphism, but the sign is not fixed by the
source prime-strip link.  The exact first missing source agreement is recorded
as `ActualZpShellAgreement`: the `-1` shell component has to be identified
with the log-shell transport induced by the source `FPrimeStripEquiv`.  Such a
transport is not part of the present source API (`FPrimeStripEquiv` carries
components only on `Pi`, `G` and `Mon`), so the agreement is not assumed and
no inhabitant is constructed.

No `sorry`, no new axiom, no arbitrary `Classical.choice`, and no renamed
copy of the source permutation is used.
-/

noncomputable section

open scoped TensorProduct
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1389PaperPolyIsoActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

local instance factPrimeOfPrimeGeFive (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. S1264: the actual common-prime-completion capsule -/

namespace S1264

open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual

/-- The label permutation of the actual S1264 poly-isomorphism is the label
permutation of the actual source Ind1 automorphism.  This is the first field,
and it agrees literally. -/
theorem labelPerm_eq_source (n : Int) (j : Fin (capsuleLevels l)) :
    (actualPolyIso I j.val).labelPerm =
      (ind1Candidate I n j).perm := rfl

/-- The first field is literally `Fin.revPerm`. -/
theorem labelPerm_eq_revPerm (j : Fin (capsuleLevels l)) :
    (actualPolyIso I j.val).labelPerm = Fin.revPerm := rfl

/-- The shell component of the S1264 action is the canonical reflexive
equivalence on the actual common-prime completion. -/
theorem shellEquiv_eq_refl (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : RationalPlaceAt l) (v : ActualPlace I) :
    (actualPolyIso I j.val).shellEquiv i vQ v =
      LinearEquiv.refl ℚ_[l.value] ((actualLogShellFamily I j.val).Shell i vQ v) := rfl

/-- The S1264 poly-isomorphism is exactly the source Ind1 label permutation
with the identity shell transport on the actual common-prime completion. -/
theorem actualContract_polyIso_eq_source (n : Int) (j : Fin (capsuleLevels l)) :
    (actualContract I n).polyIso j =
      { labelPerm := (ind1Candidate I n j).perm
        shellEquiv := fun i vQ v =>
          LinearEquiv.refl ℚ_[l.value]
            ((actualContract I n).logShell j |>.Shell i vQ v) } := rfl

end S1264

/-! ## 2. S1313: the actual integral log-shell capsule -/

namespace S1313

open LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual

/-- The label permutation of the actual S1313 poly-isomorphism is the label
permutation of the source Ind1 automorphism at the contract's selected
arithmetic-holomorphic index `0`. -/
theorem labelPerm_eq_source (j : Fin (capsuleLevels l)) :
    (integralLogShellPolyIso I j.val).labelPerm =
      (PrcAutomorphism.ofPerm (canonicalCapsuleTheaterAssignment I 0) j
        Fin.revPerm).perm := rfl

/-- The first field is literally `Fin.revPerm`. -/
theorem labelPerm_eq_revPerm (j : Fin (capsuleLevels l)) :
    (integralLogShellPolyIso I j.val).labelPerm = Fin.revPerm := rfl

/-- The shell component of the S1313 action is the canonical reflexive
equivalence on the actual integral log-shell. -/
theorem shellEquiv_eq_refl (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    (integralLogShellPolyIso I j.val).shellEquiv i vQ v =
      LinearEquiv.refl ℤ ((integralLogShellFamily I j.val).Shell i vQ v) := rfl

/-- The S1313 poly-isomorphism is exactly the source Ind1 label permutation
with the identity shell transport on the actual integral log-shell. -/
theorem actualIntegralCapsuleContract_polyIso_eq_source
    (j : Fin (capsuleLevels l)) :
    (actualIntegralCapsuleContract I).polyIso j =
      { labelPerm :=
          (PrcAutomorphism.ofPerm (canonicalCapsuleTheaterAssignment I 0) j
            Fin.revPerm).perm
        shellEquiv := fun i vQ v =>
          LinearEquiv.refl ℤ
            ((actualIntegralCapsuleContract I).logShell j |>.Shell i vQ v) } := rfl

end S1313

/-! ## 3. S1318: the actual `ℤ_[p]`-lattice capsule -/

namespace S1318

open LeanFormal.IUT.XiFPaper.S1270NontrivialCapsuleActual
open LeanFormal.IUT.XiFPaper.S1318IntegralCapsuleZpHomActual

/-- The label permutation of the actual S1318 poly-isomorphism is the label
permutation of the source Ind1 automorphism at the contract's selected index
`0`.  The first field therefore agrees. -/
theorem labelPerm_eq_source (j : Fin (capsuleLevels l)) :
    (actualZpPolyIso I j.val).labelPerm =
      (PrcAutomorphism.ofPerm (canonicalCapsuleTheaterAssignment I 0) j
        Fin.revPerm).perm := rfl

/-- The first field is literally `Fin.revPerm`. -/
theorem labelPerm_eq_revPerm (j : Fin (capsuleLevels l)) :
    (actualZpPolyIso I j.val).labelPerm = Fin.revPerm := rfl

/-- The shell component of the S1318 action is the actual integral
`-1` automorphism of the `ℤ_[p]`-lattice. -/
theorem shellEquiv_eq_neg (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : ActualValuation) (v : actualPlace I vQ) :
    (actualZpPolyIso I j.val).shellEquiv i vQ v =
      (LinearEquiv.neg (actualZpR vQ) :
        actualZpShell I vQ v ≃ₗ[actualZpR vQ] actualZpShell I vQ v) := rfl

/-- The S1318 poly-isomorphism is the source Ind1 label permutation with the
actual integral `-1` shell transport. -/
theorem actualZpCapsuleContract_polyIso_eq_source_signed
    (j : Fin (capsuleLevels l)) :
    (actualZpCapsuleContract I).polyIso j =
      { labelPerm :=
          (PrcAutomorphism.ofPerm (canonicalCapsuleTheaterAssignment I 0) j
            Fin.revPerm).perm
        shellEquiv := fun i vQ v =>
          (LinearEquiv.neg (actualZpR vQ) :
            actualZpShell I vQ v ≃ₗ[actualZpR vQ] actualZpShell I vQ v) } := rfl

/-- The exact first missing source agreement for the S1318 action.  The
`-1` shell equivalence would have to be the identity shell transport induced
by the source prime-strip link `PrcTransition`.  The current source API
(`FPrimeStripEquiv`) has no component on the common-prime completion or on the
integral log-shell lattice, so no such transport is defined.  This proposition
is recorded, not assumed, and no inhabitant is constructed. -/
def ActualZpShellAgreement (j : Fin (capsuleLevels l)) : Prop :=
  forall (i : Capsule j.val) (vQ : ActualValuation) (v : actualPlace I vQ),
    (actualZpPolyIso I j.val).shellEquiv i vQ v =
      (LinearEquiv.refl (actualZpR vQ) (actualZpShell I vQ v) :
        actualZpShell I vQ v ≃ₗ[actualZpR vQ] actualZpShell I vQ v)

end S1318

/-! ## 4. Axiom probes -/

#print axioms S1264.labelPerm_eq_source
#print axioms S1264.labelPerm_eq_revPerm
#print axioms S1264.shellEquiv_eq_refl
#print axioms S1264.actualContract_polyIso_eq_source
#print axioms S1313.labelPerm_eq_source
#print axioms S1313.labelPerm_eq_revPerm
#print axioms S1313.shellEquiv_eq_refl
#print axioms S1313.actualIntegralCapsuleContract_polyIso_eq_source
#print axioms S1318.labelPerm_eq_source
#print axioms S1318.labelPerm_eq_revPerm
#print axioms S1318.shellEquiv_eq_neg
#print axioms S1318.actualZpCapsuleContract_polyIso_eq_source_signed

end LeanFormal.IUT.XiFPaper.S1389PaperPolyIsoActual