import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132PaperIQCarrierIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Fintype (C3.tensorPlaceIndex i)]

/-!
# Paper IQ operation at the actual carriers, and the exact paper carrier gap

IUT III, Proposition 3.2, (i), (ii) (pp. 97-99) attaches to a capsule of
D-prime-strips the local log-shells `I(D_v)` and defines `IQ(-)` as the
`Q`-span of the tensor packet of log-shells.  Remark 3.9.5, (i) (pp. 158-159)
forms the holomorphic hull of a region inside that `IQ`-carrier
`IQ(S^+-_{j+1}; n,circ D^vdash_{vQ})`; Step (xi-d) of the proof of Corollary 3.12
(corpus lines 10823-10863) uses that carrier for the possible images
`n,circ U_{j,vQ}`.

The tree constructs this `IQ` operation on two actual carriers built from actual
finite-place completions:

* `actualC3LogShellTensorIQ`: the `Q`-span of the actual C3 tensor integral
  region `actualC3LogShellTensorRegion` of the actual local log-shells
  `I(D_v) = integralLogShell`;
* `arithmeticIQCarrier (literalIQPlaces C3 j)`: the `Q`-span of the actual
  completion-packet tensor region at the source theater completions (the
  literal IQ carrier of the level-`j` completion packet).

This module proves the paper `IQ`-spanning property on both actual carriers,
i.e. the inclusion of the image regions `n,circ U` inside the `IQ`-carriers,
and records the exact missing identification of these actual carriers with the
paper inductive-system carrier.

Source: IUT III, Proposition 3.2, (i), (ii), pp. 97-99; Remark 3.9.5, (i),
pp. 158-159; Corollary 3.12 proof, Step (xi-d), pp. 174-175.  No inequality and
no new carrier is asserted.
-/

/-- **Paper IQ spanning property on the actual C3 tensor packet.**  The actual
tensor log-shell region `n,circ U` is contained in its `Q`-span, the actual IQ
carrier of Proposition 3.2, (ii). -/
theorem actualC3TensorRegion_subset_IQCarrier :
    (actualC3LogShellTensorRegion C3 : Set (C3LogShellTensorBlock C3)) ⊆
      (actualC3LogShellTensorIQ C3 : Set (C3LogShellTensorBlock C3)) :=
  Submodule.subset_span

/-- **Paper IQ spanning property on the actual literal IQ carrier.**  The actual
completion-packet tensor region at level `j` is contained in its `Q`-span. -/
theorem literalIQUnitRegion_subset_arithmeticIQCarrier (j : Nat) :
    literalIQUnitRegion C3 j ⊆
      (arithmeticIQCarrier (literalIQPlaces C3 j) :
        Set (LiteralIQAmbient C3 j)) := by
  intro x hx
  have h : (Submodule.span ℚ
      (arithmeticTensorLogRegion (literalIQPlaces C3 j)) :
        Set (LiteralIQAmbient C3 j)) =
      (arithmeticIQCarrier (literalIQPlaces C3 j) :
        Set (LiteralIQAmbient C3 j)) := rfl
  rw [← h]
  exact Submodule.subset_span hx

/-!
## Exact missing identification with the paper carrier

The actual carriers above are built from actual local fields, but their
identification with the paper inductive-system carrier
`IQ(S^+-_{j+1}; n,circ D^vdash_{vQ})` is not constructed in the tree.  The exact
missing datum is the existing record `PrimeStripC3PlaceComparison` /
`PrimeStripC3PlaceComparisonRequired` (`PrimeStripLogShellActual.lean`): an
equivalence `V = C3.tensorIndex` of the source prime-strip index with the C3
tensor index together with the matching of the prime-strip places with the
selected C3 tensor places.  Its source is IUT III, Theorem 3.11, pp. 160-162 and
IUT IV, Theorem 1.10 proof, pp. 26-27; it is not derivable from `OriginalInput`
plus the actual C3 data alone.  Once that place comparison is supplied, the
conditional `logShellDatumOnStrip` / `logShellOnStrip` of
`PrimeStripLogShellActual.lean` carry the actual local log-shell data to the
source prime-strip index, and the remaining step is bookkeeping, not new
mathematics.  No identification is asserted here.
-/

end LeanFormal.IUT.XiFPaper.S3132PaperIQCarrierIdentificationActual

end