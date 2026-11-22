import LeanFormal/IUT/IUTII/Kummer/SourceLogShellIQTensorPacket
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSHETransportObligations

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerIQDirectSumSHEActual — A476 real consumer theorems (IQ direct sum / SHE supply)

New conclusions combining existing donor theorems:

* `SourceLogShellIQTensorPacket.lean:113/118/128/135/148`:
  - `iqDirectSum_membership_package`: the single-fiber inclusion and the
    pStar-inverse scaling membership hold jointly (two donor theorems);
  - `iqDirectSum_mem_span_pi`: membership in the IQ direct-sum packet is
    exactly membership in the Q-span of the direct-sum packet set (chain of
    the decomposition theorem with the membership characterization).
* `SourceSHETransportObligations.lean:215/229/197`:
  - `sheSupply_slot_consumer`: the assembled conditional SHE supply transfers
    its square statement into a named `StepXIContract.she` slot (chain of
    `sheSupply` + `sheSlot_evidence`).

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerIQDirectSumSHEActual

open LeanFormal.IUT

/-- **IQ direct-sum membership package consumer**: single-fiber inclusion and
pStar-inverse scaled membership jointly. -/
theorem iqDirectSum_membership_package {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → SourceLogShellDatum) (i : ι) {x : (D i).K}
    (hx : x ∈ (D i).IQSpan)
    {y : (i : ι) → (D i).K} (hy : ∀ i, y i ∈ (D i).logShell) :
    (LinearMap.single ℚ (fun i => (D i).K) i x) ∈ sourceLogShellIQDirectSumPacket D ∧
      (fun i => ((D i).pStar : (D i).K)⁻¹ * y i) ∈ sourceLogShellIQDirectSumPacket D :=
  ⟨sourceLogShellIQDirectSumPacket_single_mem D i hx,
   sourceLogShellIQDirectSumPacket_pStar_inv_mul_mem D hy⟩

/-- **IQ direct-sum membership/span chain consumer**: membership in the
IQ direct-sum packet is membership in the Q-span of the packet set. -/
theorem iqDirectSum_mem_span_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → SourceLogShellDatum) (x : (i : ι) → (D i).K) :
    x ∈ sourceLogShellIQDirectSumPacket D ↔
      x ∈ Submodule.span ℚ (sourceLogShellDirectSumPacketSet D) := by
  rw [sourceLogShellIQDirectSumPacket_eq_span_pi D]

/-- **SHE supply slot consumer**: the assembled conditional SHE supply's square
statement fills a named `StepXIContract.she` slot. -/
theorem sheSupply_slot_consumer
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} {A B C D : FPrimeStrip V}
    (S : Theorem311Source.SourceKummerEvaluationSquare G A B C D)
    {contract : StepXIContract}
    (h : contract.she =
      (Theorem311Source.SourceKummerEvaluationSquare.sheSupply S).square.sheStatement) :
    contract.she :=
  SourceSHESquareSupply.sheSlot_evidence
    (Theorem311Source.SourceKummerEvaluationSquare.sheSupply S) h

#check iqDirectSum_membership_package
#check sheSupply_slot_consumer

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerIQDirectSumSHEActual
end