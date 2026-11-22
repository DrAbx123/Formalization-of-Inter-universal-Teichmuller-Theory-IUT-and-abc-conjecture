import tmp.sheaf.xif.paper.S3139C3Ind1BridgeActual
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 600000

/-!
# S3139: C3 — the in-place relabeling side of the convention identification

The C3 residual `SourceInd1ConventionIdentification` asks for a linear
comparison between two pure-tensor conventions.  This file proves the
constructible half: on pure tensors the polyIso action built from the
procession permutation (`polyIsoOfPerm`) acts by the in-place relabeling
tprod x |-> tprod (fun i => x i), using the production
`PolyIsoAction.tensorMap_tprod` and the trivial shell equivalences.

The remaining half — the target-side automorphism matching this in-place
relabeling to the position permutation tprod y |-> tprod (fun i => y
(P.perm.symm i)) — is the exact datum left in
`SourceInd1ConventionIdentification`.  Attempted Mathlib constructions
(`PiTensorProduct.reindex` with the procession permutation, and the
`PiTensorProduct.lift` of the multilinear entry-permutation maps) hit the
reindex codomain-family mismatch (reindex's codomain is the family
s (e.symm i), one step away from the permuted family s), so the datum is kept
as data (not assumed) rather than faked.

**Component, not paper object.**  Registry FROZEN (final status/ledger only).
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C3ConventionTheoremActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- On pure tensors the polyIso action built from the procession permutation
acts by the in-place relabeling: tprod x |-> tprod (fun i => x i). -/
theorem polyIsoOfPerm_tensorMap_tprod
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    (polyIsoOfPerm A j P).tensorMap ()
        (PiTensorProduct.tprod Real x) =
      PiTensorProduct.tprod Real (fun i => x i) := by
  rw [PolyIsoAction.tensorMap_tprod]
  rfl

/-- The in-place relabeling is independent of the procession automorphism at the
level of the pure-tensor image (it always produces tprod of the same entries):
the comparison datum must therefore be a target-side automorphism. -/
theorem polyIsoOfPerm_tensorMap_tprod_eq_refl
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P Q : PrcAutomorphism A j)
    (x : (i : Capsule j.val) →
      DirectSumFactor (standardRealLogShellFamily j.val) () i) :
    (polyIsoOfPerm A j P).tensorMap () (PiTensorProduct.tprod Real x) =
      (polyIsoOfPerm A j Q).tensorMap () (PiTensorProduct.tprod Real x) := by
  rw [polyIsoOfPerm_tensorMap_tprod, polyIsoOfPerm_tensorMap_tprod]

end LeanFormal.IUT.XiFPaper.S3139C3ConventionTheoremActual

end
