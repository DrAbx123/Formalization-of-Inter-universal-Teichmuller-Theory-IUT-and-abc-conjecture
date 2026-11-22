import tmp.sheaf.xif.paper.Ind1AutomorphismTensorActionActual
import tmp.sheaf.xif.paper.S1265SourceInd2Actual
import tmp.sheaf.xif.paper.S3139SourceBPSActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: first-triangle multiradial-algorithm mutation (actual data)

IUT III, §1-3 (III:584-729) and Formalization of IUT (2026-04) §4 :505-513
describe the first triangle

  BPS --multiradial algorithm--> multiradial representation

where the multiradial representation is (III:595-620, 663-709, Fig. I.6):

* (a) tensor packets of log-shells over the capsule labels;
* (b) the action of splitting monoids of LGP-monoids on the tensor packets
  (III:610-615, Fig. I.4; the actual `SourceLGPData.actionOnTensorPacket`);
* (c) copies `(F_mod^x)_j` acting on the tensor packets (III:616-620, Fig. I.5;
  the actual `sourceInd2RealTensorEquiv` with the actual source units);
* the (Ind1) action by procession automorphisms (III:669-674; the actual
  `PrcAutomorphismTensorAction`).

The algorithm's input is the BPS *up to* a full poly-isomorphism gluing to the
0-column BPS (Formalization :507-513).  This file constructs the actual
mutation: it maps a tensor-packet point of the supplied 0-column data, together
with an (unused) BPS gluing witness, to the representation point data (a)-(c)
and (Ind1).  The mutation is shown to be independent of the gluing witness
(`sourceMultiradialMutationOfBPS_*_invariant`): the algorithm uses the BPS only
through the indeterminate gluing, which is the paper's requirement.

The supplied data (log-shell capsule contract, LGP data, Real embedding of
F_mod) are explicit parameters; their source construction is the exact
residual recorded in `S3139FirstTriangleResidualActual`.  No sorry/axiom/
True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FirstTriangleMutationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer.SourceLGPData
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.S3139SourceBPSActual
open scoped TensorProduct

universe ua uv upi umon ui uM uVQ uPlace uShell

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (A : CapsuleTheaterAssignment l V I)
variable (D : SourceLGPData.{uM, 0, uVQ, uPlace, uShell, uv, ua, upi, umon, ui}
  Real l V I)
variable (φ : SourceFmodRealEmbedding (I := I))
variable (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ)

/-! ## 1. The multiradial-representation point data -/

/-- The actual multiradial-representation point data at capsule level `j` and
valuation `vQ`: the tensor-packet point (a) together with the actual (Ind1)
procession-automorphism action image, the actual splitting-monoid (LGP) action
images (b), and the actual `F_mod^x`-copy action images (c). -/
structure SourceMultiradialRepresentation where
  /-- (a) the tensor packet of log-shells -/
  point : D.tensorPacket j vQ
  /-- (Ind1) the procession-automorphism action on the point -/
  ind1Value : ∀ P : PrcAutomorphism A j,
    (⨂[Real] i : Capsule j.val,
      DirectSumFactor (D.capsule.logShell j) vQ (P.perm.symm i))
  /-- (Ind1) the action is the actual `PrcAutomorphismTensorAction` -/
  ind1Value_eq : ∀ P, ind1Value P =
    PrcAutomorphismTensorAction A D.capsule j vQ P point
  /-- (b) the splitting-monoid (LGP) action on the point -/
  lgpValue : D.lgp.Carrier → D.tensorPacket j vQ
  /-- (b) the action is the actual `actionOnTensorPacket` -/
  lgpValue_eq : ∀ g, lgpValue g = D.actionOnTensorPacket j vQ g point
  /-- (c) the actual `F_mod^x`-copy action on the point -/
  ind2Value : SourceFmodUnitCopies (I := I) j → D.tensorPacket j vQ
  /-- (c) the action is the actual source-unit Ind2 action -/
  ind2Value_eq : ∀ f, ind2Value f =
    sourceInd2RealTensorEquiv D.capsule j vQ φ f point

/-! ## 2. The actual mutation -/

/-- The actual multiradial-algorithm mutation at a tensor-packet point: reads
the point together with the three actual actions of the representation. -/
noncomputable def sourceMultiradialMutation (x : D.tensorPacket j vQ) :
    SourceMultiradialRepresentation A D φ j vQ where
  point := x
  ind1Value := fun P => PrcAutomorphismTensorAction A D.capsule j vQ P x
  ind1Value_eq := fun _ => rfl
  lgpValue := fun g => D.actionOnTensorPacket j vQ g x
  lgpValue_eq := fun _ => rfl
  ind2Value := fun f => sourceInd2RealTensorEquiv D.capsule j vQ φ f x
  ind2Value_eq := fun _ => rfl

/-! ## 3. Input side: BPS glued to the 0-column BPS -/

/-- The mutation driven by the actual first-triangle input: a BPS together with
a full poly-isomorphism gluing to the 0-column BPS of the actual original input
(Formalization :507-513).  The gluing is required as input validity but the
algorithm output is independent of it. -/
noncomputable def sourceMultiradialMutationOfBPS
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (B : SourceBPS V)
    (glue : SourceFTimesMuPrimeStripEquivalence B.timesMuStrip
      (sourceBPSOfTheater J 0 0).timesMuStrip)
    (x : D.tensorPacket j vQ) : SourceMultiradialRepresentation A D φ j vQ :=
  sourceMultiradialMutation A D φ j vQ x

/-- The algorithm's output is independent of the chosen full poly-isomorphism
gluing of the BPS input to the 0-column BPS: this is the paper's requirement
that the multiradial algorithm be invariant under the indeterminate gluing. -/
theorem sourceMultiradialMutationOfBPS_point_invariant
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (B : SourceBPS V)
    (glue₁ glue₂ : SourceFTimesMuPrimeStripEquivalence B.timesMuStrip
      (sourceBPSOfTheater J 0 0).timesMuStrip) (x : D.tensorPacket j vQ) :
    (sourceMultiradialMutationOfBPS A D φ j vQ J B glue₁ x).point =
      (sourceMultiradialMutationOfBPS A D φ j vQ J B glue₂ x).point := rfl

theorem sourceMultiradialMutationOfBPS_lgp_invariant
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (B : SourceBPS V)
    (glue₁ glue₂ : SourceFTimesMuPrimeStripEquivalence B.timesMuStrip
      (sourceBPSOfTheater J 0 0).timesMuStrip) (x : D.tensorPacket j vQ)
    (g : D.lgp.Carrier) :
    (sourceMultiradialMutationOfBPS A D φ j vQ J B glue₁ x).lgpValue g =
      (sourceMultiradialMutationOfBPS A D φ j vQ J B glue₂ x).lgpValue g := rfl

theorem sourceMultiradialMutationOfBPS_ind2_invariant
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (B : SourceBPS V)
    (glue₁ glue₂ : SourceFTimesMuPrimeStripEquivalence B.timesMuStrip
      (sourceBPSOfTheater J 0 0).timesMuStrip) (x : D.tensorPacket j vQ)
    (f : SourceFmodUnitCopies (I := I) j) :
    (sourceMultiradialMutationOfBPS A D φ j vQ J B glue₁ x).ind2Value f =
      (sourceMultiradialMutationOfBPS A D φ j vQ J B glue₂ x).ind2Value f := rfl

/-! ## 4. Naturality / action laws of the mutation -/

/-- (Ind1) at the identity procession automorphism fixes the representation. -/
theorem sourceMultiradialMutation_ind1_id (x : D.tensorPacket j vQ) :
    (sourceMultiradialMutation A D φ j vQ x).ind1Value (PrcAutomorphism.id A j) =
      x := by
  rw [SourceMultiradialRepresentation.ind1Value_eq]
  exact PrcAutomorphismTensorAction_id A D.capsule j vQ x

/-- (Ind1) on a pure tensor: the mutation reindexes the tensor factors. -/
theorem sourceMultiradialMutation_ind1_tprod
    (x : (i : Capsule j.val) → DirectSumFactor (D.capsule.logShell j) vQ i)
    (P : PrcAutomorphism A j) :
    (sourceMultiradialMutation A D φ j vQ (PiTensorProduct.tprod Real x)).ind1Value P =
      PiTensorProduct.tprod Real (fun i => x (P.perm.symm i)) := by
  rw [SourceMultiradialRepresentation.ind1Value_eq]
  exact PrcAutomorphismTensorAction_tprod A D.capsule j vQ P x

/-- (b)+(Ind1): the splitting-monoid action is compatible with the P1
poly-isomorphism action up to the actual scalar character. -/
theorem sourceMultiradialMutation_lgp_polyIso
    (x : D.tensorPacket j vQ) (g : D.lgp.Carrier) :
    (D.capsule.polyIso j).tensorMap vQ
        ((sourceMultiradialMutation A D φ j vQ x).lgpValue g) =
      (D.action j).scalar g •
        (D.capsule.polyIso j).tensorMap vQ x := by
  rw [SourceMultiradialRepresentation.lgpValue_eq]
  exact tensorMap_actionOnTensorPacket D j vQ g x

/-- (c) on a pure tensor: the `F_mod^x` copies act by the actual source units
on the corresponding tensor factors. -/
theorem sourceMultiradialMutation_ind2_tprod
    (x : (i : Capsule j.val) → DirectSumFactor (D.capsule.logShell j) vQ i)
    (f : SourceFmodUnitCopies (I := I) j) :
    (sourceMultiradialMutation A D φ j vQ (PiTensorProduct.tprod Real x)).ind2Value f =
      PiTensorProduct.tprod Real
        (fun i => ind2FactorAction (C := D.capsule) (j := j) (vQ := vQ)
          (Units.map φ.toMonoidHom (f i)) i (x i)) := by
  rw [SourceMultiradialRepresentation.ind2Value_eq]
  exact sourceInd2RealTensorEquiv_tprod D.capsule j vQ φ f x

end LeanFormal.IUT.XiFPaper.S3139FirstTriangleMutationActual

end
