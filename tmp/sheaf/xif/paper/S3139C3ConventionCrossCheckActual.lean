import tmp.sheaf.xif.paper.S3139C3ConventionClosureActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: C3 CONSISTENCY CROSS-CHECK — both polyIso conventions share the same in-place pure-tensor image

This is a CONSISTENCY CROSS-CHECK file only (Lead ruling: the paper convention
labelPerm := P.perm.symm is kept in the closure
`S3139C3ConventionClosureActual`; this file does not silently switch it).

We define the alternative polyIso convention labelPerm := P.perm and prove that
its pure-tensor image is the same in-place relabeling
tprod x |-> tprod (fun i => x i) as the paper convention's.  Consequently the
target-side entry-permutation comparison of the closure applies to both
conventions: the convention choice is immaterial at the pure-tensor level
(cross-check of `polyIsoOfPerm_tensorMap_tprod` and
`polyIsoOfPerm_tensorMap_tprod_eq_refl`).

**Component, not paper object.**  Registry FROZEN (final status/ledger only).
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C3ConventionCrossCheckActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionTheoremActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The alternative polyIso convention: labelPerm := P.perm (compared only as a
cross-check; the closure keeps the paper convention P.perm.symm). -/
def altPolyIsoOfPerm
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) :
    PolyIsoAction (standardRealLogShellFamily j.val) where
  labelPerm := P.perm
  shellEquiv := fun i vQ v => LinearEquiv.refl Real _

/-- The alternative convention has the same in-place pure-tensor image. -/
theorem altPolyIsoOfPerm_tensorMap_tprod
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    (altPolyIsoOfPerm A j P).tensorMap ()
        (PiTensorProduct.tprod Real x) =
      PiTensorProduct.tprod Real (fun i => x i) := by
  rw [PolyIsoAction.tensorMap_tprod]
  rfl

/-- CONSISTENCY: the two polyIso conventions give the same pure-tensor image,
so the closure's target-side entry permutation applies to both. -/
theorem polyIsoConventions_agree_on_tprod
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P Q : PrcAutomorphism A j)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    (altPolyIsoOfPerm A j P).tensorMap () (PiTensorProduct.tprod Real x) =
      (polyIsoOfPerm A j Q).tensorMap () (PiTensorProduct.tprod Real x) := by
  rw [altPolyIsoOfPerm_tensorMap_tprod, polyIsoOfPerm_tensorMap_tprod]

end LeanFormal.IUT.XiFPaper.S3139C3ConventionCrossCheckActual

end
