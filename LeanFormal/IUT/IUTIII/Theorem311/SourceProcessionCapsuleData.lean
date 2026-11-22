import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.Foundations.Algebra.FiniteTensorProductDistribution
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.style.whitespace false

/-!
# Processions, capsules, and tensor packets: the first data layer

Source anchor: IUT III, pp. 10--12 (the text surrounding the corpus lines
III:553--607).  The paper writes
`S±_{j+1} = {0,1,...,j}` for `j = 0,...,l⋇`, with `l± = 1 + l⋇ = (l+1)/2`.
Each element of `S±_{j+1}` parametrizes an `F`- or `D`-prime-strip.  For a
fixed `vQ` in the set `VQ` of valuations of `Q`, one first takes the direct
sum of the log-shells at the places `v` lying over `vQ`, and then the tensor
product over the labels `*` in `S±_{j+1}`.  The resulting collection over
`vQ` is the tensor packet of III:579--593.

This file is deliberately only the **data layer**.  It provides:

* `Capsule j`, the exact finite model `Fin (j+1)` of `S±_{j+1}`;
* `Procession` and `PrimeStripOf`, a family of prime-strips indexed by the
  capsule elements;
* `LogShellFamily`, the additional named log-shell modules at the places
  over a valuation;
* `TensorPacket`, the tensor product over the capsule of the finite direct
  sums of log-shells;
* `PolyIsoAction`, a label permutation together with the induced linear
  equivalences of log-shells, and its compatibility with the tensor packet.

What is derived from `OriginalInput`: the ambient initial Theta-data and the
Hodge-theater family.  `PrimeStripOf.ofOriginalInput` and
`Procession.ofOriginalInput` use the prime-strip of a single chosen theater
constantly over all capsule elements.  This supplies an inhabitant of the
data layer; it is **not** a construction of the paper's distinct prime-strip
assignment for every label.

What is additional named data, not present in `OriginalInput`: the valuation
set `VQ`, the place types `Place vQ`, the log-shell modules `Shell`, the
poly-isomorphism action, and the chosen procession in
`SourceProcessionCapsuleContract`.  The contract records exactly these
additional choices and is inhabited by the constant model below.

This file does not define a Gaussian object, does not assert N4 or N5 closed,
and does not state the final log-volume estimate.
-/

namespace LeanFormal.IUT
namespace Theorem311Source
namespace SourceProcessionCapsule

open scoped BigOperators TensorProduct

noncomputable section

universe ua uv upi umon ui uR uVQ uPlace uShell

/-! ## 1. The capsules `S±_{j+1} = {0,...,j}` -/

/-- The exact finite model of `S±_{j+1}`: the interval `{0,...,j}`. -/
abbrev Capsule (j : Nat) : Type := Fin (j + 1)

/-- The cardinality of the capsule is `j+1`, as in III:553--556. -/
@[simp] theorem capsule_card (j : Nat) :
    Fintype.card (Capsule j) = j + 1 := by
  simp [Capsule]

/-- Every element of the capsule is one of the labels `0,...,j`. -/
theorem capsule_mem_range {j : Nat} (i : Capsule j) :
    (i : Nat) ∈ Finset.range (j + 1) :=
  Finset.mem_range.mpr i.isLt

theorem capsule_nonempty (j : Nat) : Nonempty (Capsule j) :=
  ⟨⟨0, Nat.succ_pos j⟩⟩

/-- `l⋇ = (l-1)/2`. -/
def lStar (l : PrimeGeFive) : Nat :=
  (l.value - 1) / 2

/-- `l± = 1 + l⋇ = (l+1)/2`. -/
def lPlus (l : PrimeGeFive) : Nat :=
  (l.value + 1) / 2

/-- There are `l± = l⋇+1` capsule levels `j = 0,...,l⋇`. -/
def capsuleLevels (l : PrimeGeFive) : Nat :=
  lPlus l

theorem capsuleLevels_eq_lPlus (l : PrimeGeFive) :
    capsuleLevels l = lPlus l := rfl

/-- The paper's identity `l± = 1 + l⋇` for a prime `l ≥ 5`. -/
theorem lPlus_eq_lStar_add_one (l : PrimeGeFive) :
    lPlus l = lStar l + 1 := by
  obtain ⟨k, hk⟩ := l.odd
  unfold lPlus lStar
  rw [hk]
  have h1 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  have h2 : 2 * k + 1 - 1 = 2 * k := by omega
  rw [h1, h2]
  rw [Nat.mul_div_right (k + 1) (by norm_num : 0 < 2)]
  rw [Nat.mul_div_right k (by norm_num : 0 < 2)]

/-! ## 2. Prime strips indexed by capsule elements -/

/-- A family of prime-strips indexed by the capsule labels.  The paper allows
    both holomorphic `F`- or `D`-prime-strips and their mono-analytic versions.
    The holomorphic carrier is recorded through its Hodge theater, and the
    actual prime strip is exposed by `PrimeStripOf.primeStrip`. -/
structure PrimeStripOf (l : PrimeGeFive) (V : Type uv) where
  theater : (j : Fin (capsuleLevels l)) → Capsule j.val →
    HodgeTheater.{ua, uv, upi, umon} l V

namespace PrimeStripOf

variable {l : PrimeGeFive} {V : Type uv}

/-- The prime strip carried by a capsule element. -/
def primeStrip (P : PrimeStripOf l V) (j : Fin (capsuleLevels l))
    (i : Capsule j.val) : FPrimeStrip.{umon, uv, upi} V :=
  (P.theater j i).primeStrip

/-- The constant family obtained from one Hodge theater. -/
def ofTheater (T : HodgeTheater.{ua, uv, upi, umon} l V) :
    PrimeStripOf l V where
  theater := fun _ _ => T

/-- The constant prime-strip family obtained from one theater of an
    `OriginalInput`.  This is a data-layer inhabitant, not the paper's
    label-dependent assignment. -/
def ofOriginalInput (I : OriginalInput l V) (n m : Int) :
    PrimeStripOf l V :=
  ofTheater (I.theaterAt n m)

end PrimeStripOf

/-- A procession `Prc(n,◦D⊢_T)`: a prime-strip family together with the
    arithmetic-holomorphic index `n`. -/
structure Procession (l : PrimeGeFive) (V : Type uv)
    extends PrimeStripOf l V where
  n : Int

namespace Procession

variable {l : PrimeGeFive} {V : Type uv}

/-- The constant procession obtained from one theater of an `OriginalInput`. -/
def ofOriginalInput (I : OriginalInput l V) (n m : Int) :
    Procession l V where
  toPrimeStripOf := PrimeStripOf.ofOriginalInput I n m
  n := n

end Procession

theorem primeStripOf_nonempty.{uV, uA, uP, uM, uI}
    (I : OriginalInput.{uA, uV, uP, uM, uI} l V) :
    Nonempty (PrimeStripOf.{uA, uV, uP, uM} l V) :=
  ⟨PrimeStripOf.ofOriginalInput.{uV, uA, uP, uM, uI} I 0 0⟩

theorem procession_nonempty.{uV, uA, uP, uM, uI}
    (I : OriginalInput.{uA, uV, uP, uM, uI} l V) :
    Nonempty (Procession.{uV, uM, uP, uA} l V) :=
  ⟨Procession.ofOriginalInput.{uV, uA, uP, uM, uI} I 0 0⟩

/-! ## 3. Log-shell modules at the places over a valuation -/

/-- The additional named data of log-shells.  For every capsule label `i`,
    every valuation `vQ : VQ`, and every place `v : Place vQ` over `vQ`, this
    records an `R`-module `Shell i vQ v`.  Neither `VQ` nor `Place` nor
    `Shell` is extracted from `OriginalInput`. -/
structure LogShellFamily (R : Type uR) [CommSemiring R]
    {VQ : Type uVQ} (Place : VQ → Type uPlace) (j : Nat) where
  Shell : (i : Capsule j) → (vQ : VQ) → Place vQ → Type uShell
  [addCommMonoid : ∀ i vQ v, AddCommMonoid (Shell i vQ v)]
  [module : ∀ i vQ v, Module R (Shell i vQ v)]

attribute [instance] LogShellFamily.addCommMonoid LogShellFamily.module

section LogShells

variable {R : Type uR} [CommSemiring R]
variable {VQ : Type uVQ} {Place : VQ → Type uPlace}
variable {j : Nat}

/-- The finite direct sum of log-shells over the places over `vQ`.  For a
    finite place set this is the finite product, which is the same direct sum
    up to the canonical finite direct-sum/product equivalence. -/
abbrev DirectSumFactor (L : LogShellFamily R Place j) (vQ : VQ)
    (i : Capsule j) :=
  (v : Place vQ) → L.Shell i vQ v

/-- The tensor packet over the capsule `S±_{j+1}`: tensor over all labels `i`
    of the direct sums of log-shells at the places over `vQ`. -/
abbrev TensorPacket (L : LogShellFamily R Place j) (vQ : VQ) :=
  ⨂[R] i : Capsule j, DirectSumFactor L vQ i

/-- The tensor packet distributes over the finite direct sums: a tensor of
    direct sums is the direct sum, over all tuples of one place per label, of
    the tensor products of the chosen log-shells. -/
def tensorPacketEquiv (L : LogShellFamily R Place j) (vQ : VQ)
    [Fintype (Place vQ)] :
    TensorPacket L vQ ≃ₗ[R]
      ((tuple : (i : Capsule j) → Place vQ) →
        ⨂[R] i, L.Shell i vQ (tuple i)) :=
  FiniteTensorProductDistribution.tensorProductLinearEquiv R
    (fun i (v : Place vQ) => L.Shell i vQ v)

/-- The distribution equivalence on a pure tensor is the coordinatewise
    tensor, exactly as in III:579--593. -/
theorem tensorPacketEquiv_tprod (L : LogShellFamily R Place j) (vQ : VQ)
    [Fintype (Place vQ)]
    (x : (i : Capsule j) → (v : Place vQ) → L.Shell i vQ v)
    (tuple : (i : Capsule j) → Place vQ) :
    tensorPacketEquiv L vQ (PiTensorProduct.tprod R x) tuple =
      PiTensorProduct.tprod R (fun i => x i (tuple i)) :=
  FiniteTensorProductDistribution.tensorProductLinearEquiv_tprod R
    (fun i (v : Place vQ) => L.Shell i vQ v) x tuple

/-! ## 4. Poly-isomorphism actions on tensor packets -/

/-- A poly-isomorphism action at the data layer: a permutation of the capsule
    labels together with linear equivalences of the corresponding log-shell
    modules.  This is the shape used in the paper for the action of
    procession automorphisms on tensor packets (III:1100--1120). -/
structure PolyIsoAction (L : LogShellFamily R Place j) where
  labelPerm : Capsule j ≃ Capsule j
  shellEquiv : ∀ i (vQ : VQ) (v : Place vQ),
    L.Shell i vQ v ≃ₗ[R] L.Shell (labelPerm i) vQ v

namespace PolyIsoAction

variable {L : LogShellFamily R Place j}

/-- The induced equivalence on the direct-sum factor at a label. -/
def localFactorEquiv (A : PolyIsoAction L) (vQ : VQ) (i : Capsule j) :
    DirectSumFactor L vQ i ≃ₗ[R] DirectSumFactor L vQ (A.labelPerm i) :=
  LinearEquiv.piCongrRight (fun v => A.shellEquiv i vQ v)

/-- The tensor packet with its labels permuted by the poly-isomorphism. -/
abbrev PermutedTensorPacket (A : PolyIsoAction L) (vQ : VQ) :=
  ⨂[R] i : Capsule j, DirectSumFactor L vQ (A.labelPerm i)

/-- The linear map induced by the poly-isomorphism action on tensor packets.
    Its codomain is the tensor packet with permuted labels, which is the
    natural target of a label permutation. -/
def tensorMap (A : PolyIsoAction L) (vQ : VQ) :
    TensorPacket L vQ →ₗ[R] PermutedTensorPacket A vQ :=
  PiTensorProduct.map (fun i => (A.localFactorEquiv vQ i).toLinearMap)

/-- Compatibility of the poly-isomorphism action with the tensor packet on
    pure tensors. -/
theorem tensorMap_tprod (A : PolyIsoAction L) (vQ : VQ)
    (x : (i : Capsule j) → DirectSumFactor L vQ i) :
    A.tensorMap vQ (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i => A.localFactorEquiv vQ i (x i)) := by
  simp [tensorMap, localFactorEquiv, PiTensorProduct.map_tprod]

/-- The distribution equivalence for the permuted tensor packet. -/
def permutedTensorPacketEquiv (A : PolyIsoAction L) (vQ : VQ)
    [Fintype (Place vQ)] :
    PermutedTensorPacket A vQ ≃ₗ[R]
      ((tuple : (i : Capsule j) → Place vQ) →
        ⨂[R] i, L.Shell (A.labelPerm i) vQ (tuple i)) :=
  FiniteTensorProductDistribution.tensorProductLinearEquiv R
    (fun i (v : Place vQ) => L.Shell (A.labelPerm i) vQ v)

/-- Compatibility of the poly-isomorphism action with the distribution
    equivalence: acting on the tensor packet and then distributing is the
    same as distributing the permuted tensor packet coordinatewise. -/
theorem tensorMap_tprod_distributed (A : PolyIsoAction L) (vQ : VQ)
    [Fintype (Place vQ)]
    (x : (i : Capsule j) → DirectSumFactor L vQ i)
    (tuple : (i : Capsule j) → Place vQ) :
    A.permutedTensorPacketEquiv vQ
        (A.tensorMap vQ (PiTensorProduct.tprod R x)) tuple =
      PiTensorProduct.tprod R
        (fun i => A.localFactorEquiv vQ i (x i) (tuple i)) := by
  rw [A.tensorMap_tprod]
  exact FiniteTensorProductDistribution.tensorProductLinearEquiv_tprod R
    (fun i (v : Place vQ) => L.Shell (A.labelPerm i) vQ v)
    (fun i => A.localFactorEquiv vQ i (x i)) tuple

/-- The identity poly-isomorphism action. -/
def refl (L : LogShellFamily R Place j) : PolyIsoAction L where
  labelPerm := Equiv.refl (Capsule j)
  shellEquiv := fun i vQ v => LinearEquiv.refl R (L.Shell i vQ v)

end PolyIsoAction

theorem polyIsoAction_nonempty (L : LogShellFamily R Place j) :
    Nonempty (PolyIsoAction L) :=
  ⟨PolyIsoAction.refl L⟩

theorem tensorPacket_nonempty (L : LogShellFamily R Place j) (vQ : VQ) :
    Nonempty (TensorPacket L vQ) :=
  ⟨0⟩

end LogShells

/-! ## 5. The explicit additional-data contract -/

/-- The full additional data needed to inhabit the data layer.  The
    `OriginalInput` parameter supplies only the ambient initial Theta-data
    and Hodge-theater family; all fields below are additional named choices.
    In particular, this structure does not claim that the paper's
    label-dependent prime-strip assignment has been constructed. -/
structure SourceProcessionCapsuleContract (R : Type uR) [CommSemiring R]
    (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  procession : Procession.{uv, umon, upi, ua} l V
  VQ : Type uVQ
  place : VQ → Type uPlace
  [fintypePlace : ∀ vQ, Fintype (place vQ)]
  logShell : (j : Fin (capsuleLevels l)) →
    LogShellFamily.{uR, uVQ, uPlace, uShell} R place j.val
  polyIso : (j : Fin (capsuleLevels l)) →
    PolyIsoAction.{uR, uVQ, uPlace, uShell} (logShell j)

attribute [instance] SourceProcessionCapsuleContract.fintypePlace

/-- A canonical log-shell family over the one-point valuation/place model,
    used only to prove that the additional-data contract is inhabited. -/
def unitLogShellFamily (R : Type uR) [CommSemiring R] (j : Nat) :
    LogShellFamily R (fun _ : PUnit => PUnit) j where
  Shell := fun _ _ _ => R
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

/-- The contract is inhabited for every `OriginalInput`, using the constant
    procession and the one-point log-shell model.  This is an inhabitant of
    the data layer, not a faithfulness or existence claim for the source
    prime-strip packet. -/
def SourceProcessionCapsuleContract.trivial
    (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, uR, 0, 0, uR} R l V I where
  procession := Procession.ofOriginalInput.{uv, ua, upi, umon, ui} I 0 0
  VQ := PUnit
  place := fun _ => PUnit
  fintypePlace := fun _ => inferInstance
  logShell := fun j => unitLogShellFamily R j.val
  polyIso := fun j => PolyIsoAction.refl (unitLogShellFamily R j.val)

theorem sourceProcessionCapsuleContract_nonempty
    (R : Type uR) [CommSemiring R]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Nonempty (SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, uR, 0, 0, uR} R l V I) :=
  ⟨SourceProcessionCapsuleContract.trivial R I⟩

/-- The tensor packet associated to a contract at level `j` and valuation
    `vQ`. -/
abbrev SourceProcessionCapsuleContract.tensorPacket
    (R : Type uR) [CommSemiring R]
    (C : SourceProcessionCapsuleContract R l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :=
  TensorPacket (C.logShell j) vQ

/-- The tensor-packet distribution equivalence associated to a contract. -/
def SourceProcessionCapsuleContract.tensorPacketEquiv
    (R : Type uR) [CommSemiring R]
    (C : SourceProcessionCapsuleContract R l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :
    SourceProcessionCapsuleContract.tensorPacket R C j vQ ≃ₗ[R]
      ((tuple : (i : Capsule j.val) → C.place vQ) →
        ⨂[R] i, (C.logShell j).Shell i vQ (tuple i)) := by
  letI := C.fintypePlace vQ
  exact SourceProcessionCapsule.tensorPacketEquiv (C.logShell j) vQ

end

end SourceProcessionCapsule
end Theorem311Source
end LeanFormal.IUT
