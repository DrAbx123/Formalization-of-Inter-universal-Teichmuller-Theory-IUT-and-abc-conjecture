import Mathlib
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24UnionActual
import tmp.sheaf.xif.paper.Mzk1Lemma24AssemblyActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProvider2Actual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24UnionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24ProofActual

/-- **(S2) Generic first-alternative measure decrease** (paper [Mzk1] Lemma 2.4 lines
200-203): if every point of S' has reduced degree strictly smaller than m(S), then
m(S') < m(S).  This reduces the first alternative of the induction step to the
degree bound supplied by (S1a)/(S1b) on the f0-images f0(S ∪ S0). -/
theorem s3135_mOfPoints_lt_of_forall_reducedDegree_lt
    (S S' : Finset Qbar) (hS : S.Nonempty) (hS' : S'.Nonempty)
    (h : ∀ α ∈ S', reducedDegreeOfPoint α < mOfPoints S hS) :
    mOfPoints S' hS' < mOfPoints S hS := by
  rw [show mOfPoints S' hS' =
      (S'.image reducedDegreeOfPoint).max' (hS'.image reducedDegreeOfPoint) from rfl]
  rw [Finset.max'_lt_iff]
  intro y hy
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hy
  exact h α hα

 /-- **(S3) Goal transport, PROVED with an explicit image-set parameter** (paper
[Mzk1] Lemma 2.4 induction step composition): given a set Sim which is the h-image of S
(membership relation hmem), a Lemma 2.4 goal for (Sim, h β) transports to a goal for
(S, β) with unramifiedness transported by h.  This avoids the Finset.image
DecidableEq-instance mismatch by carrying Sim + hmem explicitly, and builds the
composed P1Morphism directly. -/
theorem s3135_goal_transport (S : Finset ℂ) (Sim : Finset (P1Point ℂ)) (β : ℂ)
    (h : P1Point ℂ → P1Point ℂ)
    (hmem : ∀ p : P1Point ℂ, p ∈ Sim ↔ ∃ a ∈ S, p = h (P1Point.ofFinite (K := ℂ) a))
    (hshape : Mzk1Lemma24Goal Sim (h (P1Point.ofFinite (K := ℂ) β))) :
    Mzk1Lemma24Goal (S.image (P1Point.ofFinite (K := ℂ)))
      (P1Point.ofFinite (K := ℂ) β) := by
  classical
  obtain ⟨T, unr, φ, hnc, hpres, hav, hunr⟩ := hshape
  let φ' : P1Morphism ℂ :=
    { ratFunc := φ.ratFunc
      mapPoints := fun p => φ.mapPoints (h p)
      nonconstant := φ.nonconstant
      nonconstant_proof := φ.nonconstant_proof }
  refine ⟨T, fun p => unr (h p), φ', hnc, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact hpres _ ((hmem _).mpr ⟨a, ha, rfl⟩)
  · exact hav
  · intro p hp
    exact hunr (h p) hp

 /-- (S2)/(S3) status: (S2) first alternative of the measure decrease reduced to the
degree bound on f0-images (proved generic lemma); (S3) the transport field of the
assembly step record is PROVED from hull's transfer lemma.  Remaining exact residue:
supply the f0-image degree bound (S1a/S1b) and the f0 morphism data from ShapeStep to
instantiate the step record, and handle the equal-m/d-decrease branch. -/
def Mzk1Lemma24StepProvider2Status : Audit.Obligation :=
  { id := "MZK1.lemma24.step-provider.2"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 195-206"
    status := Audit.VerificationStatus.interface
    note := "PROVED in this file: s3135_mOfPoints_lt_of_forall_reducedDegree_lt (S2 generic first alternative: all reduced degrees of S' < m(S) => m(S') < m(S), reducing it to the f0-image degree bound) and s3135_goal_transport (S3: Mzk1Lemma24Goal transport along an explicit point map h with explicit image set Sim + membership relation hmem; the composed P1Morphism is built directly and PreservesSet/AvoidsPoint/UnramifiedOver are transported pointwise, avoiding the Finset.image DecidableEq-instance mismatch which blocked the direct hull-transfer route). EXTERNAL PROVED INPUTS: S1a s3135_criticalPoint_degree_drop (Mzk1Lemma24StepProviderActual), S1b ValueDegreeDropStatement (stepxi Mzk1Lemma24ValueDegreeDropActual, CITABLE 6 decls), rational base provider (hull Mzk1Lemma24BaseProviderActual, CITABLE 3 decls). REMAINING: (i) instantiate the f0-image degree bound (S1a+S1b) for S'=f0(S union S0); (ii) f0 morphism data from Mzk1Lemma24ShapeStepActual.s3135_f0_step_shape; (iii) equal-m second alternative d(S')<d(S) bookkeeping; (iv) assemble Mzk1Lemma24StepProviderStatement. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.step-provider", "MZK1.lemma24.assembly" ]
    sorryItems :=
      [ "(i) f0-image degree bound instantiation (S1a+S1b both proved; wiring)",
        "(ii) f0 morphism data wiring from ShapeStep",
        "(iii) equal-m second alternative d-decrease" ] }

#check s3135_mOfPoints_lt_of_forall_reducedDegree_lt

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProvider2Actual
end