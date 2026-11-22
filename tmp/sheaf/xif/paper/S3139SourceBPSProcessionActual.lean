import tmp.sheaf.xif.paper.MultiradialProcessionActual
import tmp.sheaf.xif.paper.S3139SourceBPSActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: the BPS procession (PrcMember / PrcTransition lifted to BPS)

The Stage-1 BPS object of `S3139SourceBPSActual` is lifted to the actual source
procession of `XiFPaper/MultiradialProcessionActual.lean`: members are the
actual F-prime-strips `PrcMember` (the prime strip of the selected actual Hodge
theater), transitions are the actual procession equivalences `PrcTransition`
(the prime-strip part of the actual link `I.linkAt`), and the Theta-link
gluing data of the BPS endpoints is the actual times-mu full poly-isomorphism
obtained by canonical lifting.

Paper source: Formalization of IUT (2026-04), §4 :507-513 (BPS glued via a full
poly-isomorphism), :602-610 (Stage-1 triangles); IUT III, Theorem 3.11.
The procession data comes from the existing actual carriers: no arbitrary
assignments, no sorry/axiom/True/PUnit.

The only *extra* named data beyond `OriginalInput` is the capsule-to-source
index assignment `CapsuleTheaterAssignment` already recorded in the production
source layer (its nonconstancy is a field-level choice, not constructed here).
-/

namespace LeanFormal.IUT.XiFPaper.S3139SourceBPSProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3139SourceBPSActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-! ## 1. BPS members and their Theta-link gluing data -/

/-- The BPS of the actual procession member (the prime strip of the selected
actual theater). -/
def sourceBPSPrcMember (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) : SourceBPS V :=
  sourceBPSOfStrip (PrcMember A j i)

/-- The Theta-link gluing data between two procession members: the canonical
lifting of the actual procession transition. -/
def sourceBPSPrcTransition (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i i' : Capsule j.val) :
    SourceBPSThetaGluing (sourceBPSPrcMember A j i)
      (sourceBPSPrcMember A j i') :=
  sourceBPSThetaGluingOfStripEquiv (PrcTransition A j i i')

/-- The gluing's underlying strip equivalence is the actual procession
transition. -/
theorem sourceBPSPrcTransition_toF (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i i' : Capsule j.val) :
    (sourceBPSPrcTransition A j i i').glue.toF = PrcTransition A j i i' := rfl

/-- The BPS member's underlying prime strip is the actual procession member. -/
theorem sourceBPSPrcMember_underlying (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    (sourceBPSPrcMember A j i).underlying = PrcMember A j i := rfl

/-- The BPS member's underlying strip is the prime strip of the selected actual
Hodge theater. -/
theorem sourceBPSPrcMember_theater (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    (sourceBPSPrcMember A j i).underlying = (A.toTheater j i).primeStrip := rfl

/-- The reflexive procession transition lifts to the reflexive BPS gluing on
the underlying strip. -/
theorem sourceBPSPrcTransition_refl (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i : Capsule j.val) :
    (sourceBPSPrcTransition A j i i).glue.toF =
      FPrimeStripEquiv.refl (PrcMember A j i) :=
  PrcTransition_refl A j i

/-- The composite of two procession transitions lifts to the composite of the
two underlying strip equivalences. -/
theorem sourceBPSPrcTransition_trans (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i i' i'' : Capsule j.val) :
    FPrimeStripEquiv.trans (sourceBPSPrcTransition A j i i').glue.toF
        (sourceBPSPrcTransition A j i' i'').glue.toF =
      (sourceBPSPrcTransition A j i i'').glue.toF :=
  PrcTransition_trans A j i i' i''

/-- The BPS gluing data of two procession members is the canonical lifting of
the actual source link's prime-strip equivalence. -/
theorem sourceBPSPrcTransition_sourceLink (A : CapsuleTheaterAssignment l V I)
    (j : Fin (capsuleLevels l)) (i i' : Capsule j.val) :
    (sourceBPSPrcTransition A j i i').glue.toF =
      (I.linkAt (A.index j i).1 (A.index j i).2
        (A.index j i').1 (A.index j i').2).primeStripEquiv := rfl

/-! ## 2. The (Ind1) graph gluing data of a capsule permutation -/

/-- The actual (Ind1)-type automorphism data of the BPS procession induced by
a capsule permutation: on the graph of the permutation, the BPS gluing data is
the actual procession transition. -/
def sourceBPSProcessionAutomorphismGraph
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (sigma : Capsule j.val ≃ Capsule j.val) :
    ∀ i : Capsule j.val,
      SourceBPSThetaGluing (sourceBPSPrcMember A j i)
        (sourceBPSPrcMember A j (sigma i)) :=
  fun i => sourceBPSPrcTransition A j i (sigma i)

/-- The graph gluing data is the canonical lifting of the actual procession
transition along the permutation. -/
theorem sourceBPSProcessionAutomorphismGraph_toF
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (sigma : Capsule j.val ≃ Capsule j.val) (i : Capsule j.val) :
    ((sourceBPSProcessionAutomorphismGraph A j sigma i)).glue.toF =
      PrcTransition A j i (sigma i) := rfl

end LeanFormal.IUT.XiFPaper.S3139SourceBPSProcessionActual

end
