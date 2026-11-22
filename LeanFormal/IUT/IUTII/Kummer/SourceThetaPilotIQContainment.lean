import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket
import LeanFormal.IUT.IUTIII.Theorem311.SourceLGPMonoidLayer

/-!
# Theta-pilot orbit containment in the source log-shell IQ packet

This file isolates the set-theoretic orbit step which is independent of the
missing source-to-arithmetic comparison.  For an actual `ThetaPilotObject`
over a tensor packet, an arbitrary submodule containing the chosen generator
and stable under the splitting-monoid action contains the whole
`possibleImage`.  This is the precise form of the implication

  generator in IQ and splitting action preserves IQ
    => possibleImage is contained in IQ.

The second part constructs the canonical comparison for the one-place source
log-shell packet: the tensor packet is built from copies of a single
`SourceLogShellDatum.K`, and the comparison is the product of the coordinates.
This is a real source-log-shell reduction, not the paper's full multi-place
arithmetic packet.  In particular it does not identify the source value
monoid with `ArithmeticTensorTupleBlock`, does not construct the missing
source-to-integral-tensor map, and does not close N4--N7.

The remaining source-realization gap is exact: there is no declaration in the
current tree of a map from `OriginalInput`/`ThetaPilotObject` data to the actual
integral log-shell tensor over `ArithmeticTensorTupleBlock`, nor a proof that
the theta-pilot generator lies in the image of such a map.  No such map is
postulated here.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open scoped BigOperators TensorProduct

open Theorem311Source.SourceProcessionCapsule
open Theorem311Source.SourceLGPMonoidLayer

noncomputable section

universe uK uM

/-! ## 1. Orbit containment for an arbitrary tensor packet -/

/-- A tensor-packet submodule containing a Theta-pilot generator and stable
under the splitting-monoid action contains the whole possible image.  This is
the general orbit lemma; the source-specific comparison is supplied below for
one place. -/
theorem possibleImage_subset_of_generator_mem
    {l : PrimeGeFive} {G : LGPMonoid.{uM} l}
    {R : Type*} [CommSemiring R]
    {VQ : Type*} {Place : VQ -> Type*} {j : Nat}
    {L : LogShellFamily R Place j}
    {P : LGPMonoidAction G R L} {vQ : VQ}
    (T : ThetaPilotObject P vQ)
    (Q : Submodule R (TensorPacket L vQ))
    (hgen : T.generator ∈ Q)
    (hstable : forall (g : G.Carrier), g ∈ G.splittingMonoid ->
      forall x : TensorPacket L vQ, x ∈ Q ->
        (LGPMonoidAction.actionOnTensorPacket P vQ) g x ∈ Q) :
    T.possibleImage ⊆ Q := by
  intro x hx
  rw [ThetaPilotObject.mem_possibleImage_iff] at hx
  rcases hx with ⟨g, hg, rfl⟩
  exact hstable g hg T.generator hgen

/-! ## 2. The one-place source log-shell packet -/

/-- The one-place log-shell family associated with a source log-shell datum.
Every tensor factor is the common log-coordinate field `D.K`; the place index
is the singleton.  This is the exact one-place reduction of the source packet,
not the paper's full place tensor. -/
def sourceLogShellOnePlaceFamily (D : SourceLogShellDatum.{uK}) (j : Nat) :
    LogShellFamily.{0, 0, 0, uK} Rat (fun _ : Unit => Unit) j where
  Shell := fun _ _ _ => D.K
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

/-- The one-place tensor packet over the source log-coordinate field. -/
abbrev SourceThetaPilotOnePlacePacket (D : SourceLogShellDatum.{uK}) (j : Nat) : Type _ :=
  TensorPacket (sourceLogShellOnePlaceFamily D j) ()

/-- The canonical product comparison from the one-place tensor packet to the
source log-coordinate field.  A pure tensor is sent to the product of its
coordinates; this is the reduced comparison used by the source log-shell
tensor packet. -/
def sourceThetaPilotProductMap (D : SourceLogShellDatum.{uK}) (j : Nat) :
    SourceThetaPilotOnePlacePacket D j →ₗ[Rat] D.K :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra Rat (Capsule j) D.K).compLinearMap
      (fun _ => (LinearMap.proj (R := Rat) () :
        (Unit -> D.K) →ₗ[Rat] D.K)))

/-- The canonical product map on a pure tensor is the product of its
coordinates. -/
theorem sourceThetaPilotProductMap_tprod
    (D : SourceLogShellDatum.{uK}) (j : Nat)
    (f : (i : Capsule j) -> Unit -> D.K) :
    sourceThetaPilotProductMap D j (PiTensorProduct.tprod Rat f) =
      ∏ i, f i () := by
  simp only [sourceThetaPilotProductMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  exact Finset.prod_congr rfl (fun i _ => LinearMap.proj_apply () (f i))

/-- The reduced tensor IQ packet: the `Rat`-span of products of source
log-shell elements.  This is the one-place form of
`SourceLogShellIQTensorPacket.sourceLogShellTensorProductSet`. -/
def sourceThetaPilotTensorIQPacket (D : SourceLogShellDatum.{uK}) (j : Nat) :
    Submodule Rat D.K :=
  Submodule.span Rat
    (sourceLogShellTensorProductSet (fun _ : Capsule j => D.logShell))

/-- The preimage of the reduced tensor IQ packet in the one-place tensor
packet.  This is the actual packet-level containment target for the orbit
lemma. -/
def sourceThetaPilotIQPacket (D : SourceLogShellDatum.{uK}) (j : Nat) :
    Submodule Rat (SourceThetaPilotOnePlacePacket D j) :=
  (sourceThetaPilotTensorIQPacket D j).comap (sourceThetaPilotProductMap D j)

/-- The one-place possible image is contained in the IQ packet whenever the
chosen generator is.  The splitting action is scalar multiplication by a
rational scalar, so it preserves the `Rat`-submodule automatically. -/
theorem possibleImage_subset_sourceThetaPilotIQPacket
    {l : PrimeGeFive} {G : LGPMonoid.{uM} l}
    {D : SourceLogShellDatum.{uK}} {j : Nat}
    {P : LGPMonoidAction G Rat (sourceLogShellOnePlaceFamily D j)}
    (T : ThetaPilotObject P ())
    (hgen : T.generator ∈ sourceThetaPilotIQPacket D j) :
    T.possibleImage ⊆ sourceThetaPilotIQPacket D j := by
  apply possibleImage_subset_of_generator_mem T
    (sourceThetaPilotIQPacket D j) hgen
  intro g _ x hx
  rw [LGPMonoidAction.actionOnTensorPacket_apply]
  exact (sourceThetaPilotIQPacket D j).smul_mem (P.scalar g) hx

/-- Consequently the comparison map sends the possible image into the reduced
tensor IQ packet. -/
theorem sourceThetaPilotProductMap_image_subset_tensorIQPacket
    {l : PrimeGeFive} {G : LGPMonoid.{uM} l}
    {D : SourceLogShellDatum.{uK}} {j : Nat}
    {P : LGPMonoidAction G Rat (sourceLogShellOnePlaceFamily D j)}
    (T : ThetaPilotObject P ())
    (hgen : T.generator ∈ sourceThetaPilotIQPacket D j) :
    sourceThetaPilotProductMap D j '' T.possibleImage ⊆
      (sourceThetaPilotTensorIQPacket D j : Set D.K) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' := possibleImage_subset_sourceThetaPilotIQPacket T hgen hx
  simpa [sourceThetaPilotIQPacket] using hx'

/-! ## 3. A source log-shell generator -/

/-- The pure tensor with prescribed source log-shell coordinates. -/
def sourceLogShellTensorGenerator (D : SourceLogShellDatum.{uK}) (j : Nat)
    (f : (i : Capsule j) -> D.K) : SourceThetaPilotOnePlacePacket D j :=
  PiTensorProduct.tprod Rat (fun i => fun _ => f i)

/-- The product comparison evaluates the source log-shell generator to the
product of its coordinates. -/
theorem sourceThetaPilotProductMap_sourceLogShellTensorGenerator
    (D : SourceLogShellDatum.{uK}) (j : Nat)
    (f : (i : Capsule j) -> D.K) :
    sourceThetaPilotProductMap D j (sourceLogShellTensorGenerator D j f) =
      ∏ i, f i := by
  simp only [sourceLogShellTensorGenerator, sourceThetaPilotProductMap,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]
  exact Finset.prod_congr rfl (fun i _ => by
    rfl)

/-- If every prescribed coordinate belongs to the source log-shell, the
generator lies in the one-place IQ packet.  This is the precise generator
membership step for the reduced packet. -/
theorem sourceLogShellTensorGenerator_mem_sourceThetaPilotIQPacket
    (D : SourceLogShellDatum.{uK}) (j : Nat)
    (f : (i : Capsule j) -> D.K) (hf : forall i, f i ∈ D.logShell) :
    sourceLogShellTensorGenerator D j f ∈ sourceThetaPilotIQPacket D j := by
  rw [sourceThetaPilotIQPacket, Submodule.mem_comap,
    sourceThetaPilotProductMap_sourceLogShellTensorGenerator]
  exact Submodule.subset_span ⟨f, hf, rfl⟩

/-! ## 4. Exact boundary -/

/-! The declarations above prove only a one-place source-log-shell comparison.
They do not construct the source-to-arithmetic map

  OriginalInput / ThetaPilotObject  ->  ArithmeticTensorTupleBlock

and they do not prove that the theta-pilot generator lies in the actual
integral tensor lattice.  The existing `SourceLogShellCarrier` and
`SourceLogShellIQTensorPacket` modules provide the source log-shell carrier
and its reduced tensor packet; `FinitePlaceIntegralLogTensorLattice` provides
the arithmetic tuple integral lattice.  No declaration in the current tree
connects these two carrier types.  Adding such a map as a structure field or
postulating its generator image would be a source-realization assumption, not
a proof of N4--N7. -/

end

end LeanFormal.IUT
