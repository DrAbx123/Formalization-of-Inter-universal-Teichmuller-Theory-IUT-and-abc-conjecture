import tmp.sheaf.xif.paper.S3139ToolsPiTensorEntryPermute
import tmp.sheaf.xif.paper.S3139C3ConventionTheoremActual
import tmp.sheaf.xif.paper.S3139C3Ind1BridgeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

/-!
# S3139: C3 CLOSURE — SourceInd1ConventionIdentification is a THEOREM (paper convention kept)

The paper convention is kept: the polyIso action
`polyIsoOfPerm` uses labelPerm := P.perm.symm (in-place relabeling), and the
procession action `PrcAutomorphismTensorAction` reindexes positions.  Using the
manufactured Mathlib-gap tool `S3139ToolsPiTensorEntryPermute.piTensorEntryPermute`
we construct the target-side automorphism of the permuted-family tensor power:

* the permuted fiber family is s i := DirectSumFactor ... (P.perm.symm i);
* all its fibers are the same type (standard real log-shell family is
  constant), giving the identity-type family equivalence
  `conventionFiberEquiv` : s (P.perm.symm i) ≃ s i;
* `sourceInd1ConventionComparison` := piTensorEntryPermute s P.perm
  conventionFiberEquiv acts on pure tensors by the entry permutation
  tprod y |-> tprod (fun i => y (P.perm.symm i))
  (`sourceInd1ConventionComparison_tprod`);
* combined with the proved in-place relabeling law
  (`polyIsoOfPerm_tensorMap_tprod`) the commuting square holds
  (`sourceInd1ConventionIdentification_holds`): the C3 convention
  identification is a THEOREM (IUT III:604-620, Fig. I.4-I.6).

**Component, not paper object.**  Registry FROZEN (final status/ledger only).
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C3ConventionClosureActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldBActual
open LeanFormal.IUT.XiFPaper.S3139C3Ind1BridgeActual
open LeanFormal.IUT.XiFPaper.S3139C3ConventionTheoremActual
open LeanFormal.IUT.XiFPaper.S3139ToolsPiTensorEntryPermute
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)

/-- The permuted fiber family of the polyIso convention:
s i := DirectSumFactor ... (P.perm.symm i). -/
abbrev conventionFiber (j : Fin (capsuleLevels l)) (P : PrcAutomorphism A j)
    (i : Capsule j.val) : Type :=
  DirectSumFactor (standardRealLogShellFamily j.val) () (P.perm.symm i)

/-- The identity-type family equivalence identifying the reindexed family with
the permuted family; it exists because the standard real log-shell family is
constant. -/
noncomputable def conventionFiberEquiv
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) :
    ∀ i, conventionFiber A j P (P.perm.symm i) ≃ₗ[Real]
      conventionFiber A j P i :=
  fun i => LinearEquiv.refl Real _

/-- The target-side automorphism of the permuted-family tensor power: the entry
permutation by the procession permutation. -/
noncomputable def sourceInd1ConventionComparison
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j) :
    (⨂[Real] i : Capsule j.val, conventionFiber A j P i) ≃ₗ[Real]
      (⨂[Real] i : Capsule j.val, conventionFiber A j P i) :=
  piTensorEntryPermute (s := fun i => conventionFiber A j P i)
    P.perm (conventionFiberEquiv A j P)

/-- The comparison acts on pure tensors by the entry permutation
tprod y |-> tprod (fun i => y (P.perm.symm i)). -/
theorem sourceInd1ConventionComparison_tprod
    (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))
    (P : PrcAutomorphism A j)
    (y : (i : Capsule j.val) → conventionFiber A j P i) :
    (sourceInd1ConventionComparison A j P)
        (PiTensorProduct.tprod Real y) =
      PiTensorProduct.tprod Real (fun i => y (P.perm.symm i)) := by
  rw [sourceInd1ConventionComparison, piTensorEntryPermute_tprod]
  rfl

/-- The C3 convention identification IS a theorem with the paper convention
kept: the explicit target-side entry permutation carries the polyIso
pure-tensor image to the procession reindex pure-tensor image. -/
theorem sourceInd1ConventionIdentification_holds
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (A : CapsuleTheaterAssignment l V I) :
    SourceInd1ConventionIdentification I A := by
  intro j P
  refine ⟨sourceInd1ConventionComparison A j P, ?_⟩
  intro x
  calc
    (sourceInd1ConventionComparison A j P)
        ((polyIsoOfPerm A j P).tensorMap ()
          (PiTensorProduct.tprod Real x))
        = (sourceInd1ConventionComparison A j P)
          (PiTensorProduct.tprod Real (fun i => x i)) := by
            rw [polyIsoOfPerm_tensorMap_tprod]
            rfl
    _ = PiTensorProduct.tprod Real (fun i => x (P.perm.symm i)) := by
          have h := sourceInd1ConventionComparison_tprod A j P
            (fun i => (show conventionFiber A j P i from x i))
          exact h
    _ = PrcAutomorphismTensorAction A (sourceRealCapsuleContract I) j () P
          (PiTensorProduct.tprod Real x) := by
          rw [PrcAutomorphismTensorAction_tprod]
          rfl

end LeanFormal.IUT.XiFPaper.S3139C3ConventionClosureActual

end
