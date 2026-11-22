import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellScalarClosure
import tmp.sheaf.n8.closure.SourcePilotRegion
import Mathlib.Tactic

/-!
# OrigXiF: actual Ind1/Ind2/Ind3 on the paper output carrier and on log-Kummer

STATUS: original Theta-link layer (O).  Not the normalized (N) value scalar, not
the native (T) target, not the `SourceDefinition31Data` contract (S), not the
D4-D9 assembly (D).

## Paper output carrier

`OrigXiFPaperOutputCarrier j` is the underlying tensor type of the paper `1,circ`
IQ tensor packet of the actual completion-packet factors:

  `⨂[Q_p] x : Fin (j+1) x C3.tensorIndex, CompletionPacket (C3.tensorPlaces x.2)`

i.e. the same type as `ArithmeticPacketTensor (literalIQPlaces j)` of the paper
IQ construction (`LiteralIQAmbient j`): the factor at `(i,t)` depends only on
`t`, so this is the paper tensor of one completion packet over
`S_{j+1} = {0,...,j}`.  The normed/topological structure of
`FinitePadicTensor` is not used below; only the tensor type, the actual
log-shell tensor integral region `arithmeticTensorLogRegion`, and the region
log-volume.

The actual paper log-volume is `haarLogVolume` (`FinitePlaceIQHullInterface`,
the additive-Haar region functional) of an additive-Haar measure on the carrier.
The invariance statements are proved for *every* measure `mu` on the carrier, so
no normalization is assumed and no `Real` scalar surrogate is used; the paper's
actual additive-Haar log-volume is covered.

## Log-Kummer carrier

The actual times-mu prime-strip stage
`TimesMuQuotient ((I.fPrimeStripAt 1 m).Mon v)^x` with the actual times-mu
action, the actual stage comparison induced by the source prime-strip link, the
actual vertical Kummer layer/arrow of `LogKummerCorrespondenceFromSource`, and
the actual realified degree `FPrimeStrip.timesMuDegreeOfUnits` as log-volume
readout.

## What is constructed actually

1. (Ind1) the actual capsule permutations `Equiv.Perm (Fin (j+1))` acting on the
   paper output carrier by `PiTensorProduct.reindex`, with unit and composition
   laws;
2. (Ind2) independent copies of the norm-one units of the completed base field
   acting on each completion coordinate by scalar multiplication, with unit and
   product laws on pure tensors;
3. (Ind3) the actual times-mu action on the log-Kummer stage, the actual stage
   comparison, and compatibility of the comparison with the action;
4. the region/log-volume invariance: the actual log-shell tensor region is fixed
   by Ind1 and Ind2 (setwise, not merely comparable), hence the log-volume of
   the region is unchanged; the Ind3 stage comparison preserves the realified
   degree on every log-Kummer stage, and the times-mu action preserves the
   log-Kummer stage region.

No carrier is changed: the Ind1/Ind2 actions are linear automorphisms of the
paper output carrier and the Ind3 action is an automorphism of the times-mu
stage.  No `sorry`, `axiom`, `True`, `PUnit`, or arbitrary witness is used.

## What is NOT claimed

The paper's soft (Ind3) upper-semi comparison at the level of log-volumes is not
constructed here; at the actual times-mu quotient level the stage comparison is
an isomorphism, so the upper-semi inclusion holds with equality.  That stronger
paper statement remains a separate obligation.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open scoped BigOperators TensorProduct

namespace LeanFormal.IUT.XiFPaper.OrigXiFIndeterminaciesActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.FPrimeStrip
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-! ## 1. The paper output carrier and its actual region -/

/-- The paper tensor index `S_{j+1} x (C3 tensor index)`. -/
abbrev OrigXiFIndex (j : Nat) : Type _ :=
  Fin (j + 1) × C3.tensorIndex

/-- The completion-packet place index at a paper tensor index. -/
abbrev OrigXiFPlaceIndex (j : Nat) (x : OrigXiFIndex (C3 := C3) j) : Type _ :=
  C3.tensorPlaceIndex x.2

/-- The actual completion-packet places of the paper tensor packet: the same
`C3.tensorPlaces t` at every capsule label. -/
def OrigXiFPaperPlaces (j : Nat) :
    (x : OrigXiFIndex (C3 := C3) j) -> OrigXiFPlaceIndex (C3 := C3) j x ->
      FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  fun x => C3.tensorPlaces x.2

/-- The actual paper output carrier at level `j`: the underlying tensor type of
the paper `1,circ` IQ tensor packet of the actual completion-packet factors. -/
abbrev OrigXiFPaperOutputCarrier (j : Nat) : Type _ :=
  ⨂[ℚ_[C3.p]] x : OrigXiFIndex (C3 := C3) j,
    CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x)

/-- The actual paper output region: the log-shell tensor integral region. -/
def OrigXiFPaperOutputRegion (j : Nat) :
    Set (OrigXiFPaperOutputCarrier (C3 := C3) j) :=
  arithmeticTensorLogRegion (OrigXiFPaperPlaces (C3 := C3) j)

/-- The actual paper log-volume: the additive-Haar log-volume `haarLogVolume` of
an additive-Haar measure on the paper output carrier. -/
def OrigXiFPaperOutputLogVolume (j : Nat)
    [MeasurableSpace (OrigXiFPaperOutputCarrier (C3 := C3) j)]
    (mu : Measure (OrigXiFPaperOutputCarrier (C3 := C3) j))
    (S : Set (OrigXiFPaperOutputCarrier (C3 := C3) j)) : ENNReal :=
  haarLogVolume mu S

theorem OrigXiFPaperOutputLogVolume_eq (j : Nat)
    [MeasurableSpace (OrigXiFPaperOutputCarrier (C3 := C3) j)]
    (mu : Measure (OrigXiFPaperOutputCarrier (C3 := C3) j))
    (S : Set (OrigXiFPaperOutputCarrier (C3 := C3) j)) :
    OrigXiFPaperOutputLogVolume C3 j mu S = haarLogVolume mu S := rfl

/-- The actual paper log-volume is monotone on regions. -/
theorem OrigXiFPaperOutputLogVolume_mono (j : Nat)
    [MeasurableSpace (OrigXiFPaperOutputCarrier (C3 := C3) j)]
    (mu : Measure (OrigXiFPaperOutputCarrier (C3 := C3) j))
    {S T : Set (OrigXiFPaperOutputCarrier (C3 := C3) j)} (hST : S ⊆ T) :
    OrigXiFPaperOutputLogVolume C3 j mu S <=
      OrigXiFPaperOutputLogVolume C3 j mu T :=
  haarLogVolume_mono hST

/-- Membership in the actual paper output region, in pure-tensor form. -/
theorem OrigXiFPaperOutputRegion_mem_iff (j : Nat)
    (z : OrigXiFPaperOutputCarrier (C3 := C3) j) :
    z ∈ OrigXiFPaperOutputRegion (C3 := C3) j <->
      exists a : (x : OrigXiFIndex (C3 := C3) j) ->
          CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x),
        (forall x, a x ∈ completionPacketLogRegion
            (OrigXiFPaperPlaces (C3 := C3) j x)) ∧
          z = PiTensorProduct.tprod ℚ_[C3.p] a := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, fun x => Set.mem_pi.mp ha x (Set.mem_univ x), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Set.mem_pi.mpr (fun x _ => ha x), rfl⟩

/-! ## 2. Ind1: actual capsule permutations of the paper output carrier -/

/-- The capsule permutation as an equivalence of the paper tensor index.  It moves
only the capsule label `Fin (j+1)` and fixes the completion-packet index. -/
def OrigXiFIndexEquiv (sigma : Equiv.Perm (Fin (j + 1))) :
    OrigXiFIndex (C3 := C3) j ≃ OrigXiFIndex (C3 := C3) j where
  toFun x := (sigma x.1, x.2)
  invFun x := (sigma.symm x.1, x.2)
  left_inv x := by
    obtain ⟨i, t⟩ := x
    simp
  right_inv x := by
    obtain ⟨i, t⟩ := x
    simp

@[simp] theorem OrigXiFIndexEquiv_symm_apply (sigma : Equiv.Perm (Fin (j + 1)))
    (x : OrigXiFIndex (C3 := C3) j) :
    (OrigXiFIndexEquiv (C3 := C3) (j := j) sigma).symm x =
      (sigma.symm x.1, x.2) := rfl

theorem OrigXiFIndexEquiv_apply (sigma : Equiv.Perm (Fin (j + 1)))
    (x : OrigXiFIndex (C3 := C3) j) :
    OrigXiFIndexEquiv (C3 := C3) (j := j) sigma x = (sigma x.1, x.2) := rfl

theorem OrigXiFIndexEquiv_one :
    OrigXiFIndexEquiv (C3 := C3) (j := j) (Equiv.refl (Fin (j + 1))) =
      Equiv.refl (OrigXiFIndex (C3 := C3) j) := by
  ext x <;> rfl

/-- (Ind1) actual action of the capsule permutation group on the paper output
carrier by tensor re-indexing. -/
noncomputable def OrigXiFInd1Equiv (sigma : Equiv.Perm (Fin (j + 1))) :
    OrigXiFPaperOutputCarrier (C3 := C3) j ≃ₗ[ℚ_[C3.p]]
      OrigXiFPaperOutputCarrier (C3 := C3) j :=
  PiTensorProduct.reindex (R := ℚ_[C3.p])
    (s := fun x => CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
    (OrigXiFIndexEquiv (C3 := C3) (j := j) sigma)

theorem OrigXiFInd1Equiv_apply_tprod (sigma : Equiv.Perm (Fin (j + 1)))
    (a : (x : OrigXiFIndex (C3 := C3) j) ->
      CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x)) :
    OrigXiFInd1Equiv (C3 := C3) (j := j) sigma
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
      PiTensorProduct.tprod ℚ_[C3.p]
        (fun i : OrigXiFIndex (C3 := C3) j => a (sigma.symm i.1, i.2)) := by
  rw [OrigXiFInd1Equiv]
  exact PiTensorProduct.reindex_tprod (R := ℚ_[C3.p])
    (s := fun x => CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
    (e := OrigXiFIndexEquiv (C3 := C3) (j := j) sigma) a

/-- The Ind1 action of the identity capsule permutation is the identity on pure
tensors. -/
theorem OrigXiFInd1Equiv_one_tprod
    (a : (x : OrigXiFIndex (C3 := C3) j) ->
      CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x)) :
    OrigXiFInd1Equiv (C3 := C3) (j := j) (Equiv.refl (Fin (j + 1)))
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
      PiTensorProduct.tprod ℚ_[C3.p] a := by
  rw [OrigXiFInd1Equiv_apply_tprod]
  rfl

/-- The Ind1 action is a representation: composite permutations act by the
composite of the actual actions. -/
theorem OrigXiFInd1Equiv_trans (sigma tau : Equiv.Perm (Fin (j + 1))) :
    (OrigXiFInd1Equiv (C3 := C3) (j := j) sigma).trans
        (OrigXiFInd1Equiv (C3 := C3) (j := j) tau) =
      OrigXiFInd1Equiv (C3 := C3) (j := j) (sigma.trans tau) := by
  rw [OrigXiFInd1Equiv, OrigXiFInd1Equiv, OrigXiFInd1Equiv]
  exact PiTensorProduct.reindex_trans (R := ℚ_[C3.p])
    (s := fun x => CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
    (e := OrigXiFIndexEquiv (C3 := C3) (j := j) sigma)
    (e' := OrigXiFIndexEquiv (C3 := C3) (j := j) tau)

/-- The Ind1 action fixes the actual log-shell tensor region setwise: the
capsule permutation fixes the completion-packet index, so every permuted pure
tensor has the same factor regions. -/
theorem OrigXiFInd1Equiv_region_fixed (sigma : Equiv.Perm (Fin (j + 1))) :
    OrigXiFInd1Equiv (C3 := C3) (j := j) sigma ''
        OrigXiFPaperOutputRegion (C3 := C3) j =
      OrigXiFPaperOutputRegion (C3 := C3) j := by
  apply Set.Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    rcases (OrigXiFPaperOutputRegion_mem_iff (C3 := C3) (j := j) w).mp hw with
      ⟨a, ha, rfl⟩
    refine (OrigXiFPaperOutputRegion_mem_iff (C3 := C3) (j := j)
      (OrigXiFInd1Equiv (C3 := C3) (j := j) sigma
        (PiTensorProduct.tprod ℚ_[C3.p] a))).mpr ?_
    refine ⟨fun i => a (sigma.symm i.1, i.2), ?_, ?_⟩
    · intro i
      exact ha (sigma.symm i.1, i.2)
    · rw [OrigXiFInd1Equiv_apply_tprod]
      rfl
  · intro z hz
    rcases (OrigXiFPaperOutputRegion_mem_iff (C3 := C3) (j := j) z).mp hz with
      ⟨a, ha, rfl⟩
    refine ⟨(OrigXiFInd1Equiv (C3 := C3) (j := j) sigma).symm
        (PiTensorProduct.tprod ℚ_[C3.p] a),
      ?_, LinearEquiv.apply_symm_apply _ _⟩
    have hsymm : (OrigXiFInd1Equiv (C3 := C3) (j := j) sigma).symm
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
        PiTensorProduct.tprod ℚ_[C3.p]
          (fun i : OrigXiFIndex (C3 := C3) j => a (sigma i.1, i.2)) := by
      have h : OrigXiFInd1Equiv (C3 := C3) (j := j) sigma
          (PiTensorProduct.tprod ℚ_[C3.p]
            (fun i : OrigXiFIndex (C3 := C3) j => a (sigma i.1, i.2))) =
          PiTensorProduct.tprod ℚ_[C3.p] a := by
        rw [OrigXiFInd1Equiv_apply_tprod]
        congr 1
        funext i
        rw [Equiv.apply_symm_apply]
      rw [← h, LinearEquiv.symm_apply_apply]
      rfl
    rw [hsymm]
    exact (OrigXiFPaperOutputRegion_mem_iff (C3 := C3) (j := j)
      (PiTensorProduct.tprod ℚ_[C3.p]
        (fun i : OrigXiFIndex (C3 := C3) j => a (sigma i.1, i.2)))).mpr
      ⟨fun i => a (sigma i.1, i.2), fun i => ha (sigma i.1, i.2), rfl⟩

/-- Log-volume invariance under the actual Ind1 action. -/
theorem OrigXiFInd1Equiv_logVolume (sigma : Equiv.Perm (Fin (j + 1)))
    [MeasurableSpace (OrigXiFPaperOutputCarrier (C3 := C3) j)]
    (mu : Measure (OrigXiFPaperOutputCarrier (C3 := C3) j)) :
    OrigXiFPaperOutputLogVolume C3 j mu
        (OrigXiFInd1Equiv (C3 := C3) (j := j) sigma ''
          OrigXiFPaperOutputRegion (C3 := C3) j) =
      OrigXiFPaperOutputLogVolume C3 j mu
        (OrigXiFPaperOutputRegion (C3 := C3) j) := by
  rw [OrigXiFInd1Equiv_region_fixed]

/-! ## 3. Ind2: independent norm-one unit copies on the paper output carrier -/

/-- The actual independent unit copy family at level `j`: one copy of the
norm-one units of the completed base field for every factor and every place.
These are exactly the units of the completed integer ring, presented by
`||a|| = 1`. -/
abbrev OrigXiFInd2Unit (j : Nat) : Type :=
  (x : OrigXiFIndex (C3 := C3) j) -> (v : OrigXiFPlaceIndex (C3 := C3) j x) ->
    {a : ℚ_[C3.p]ˣ // ‖(a : ℚ_[C3.p])‖ = 1}

/-- A copy unit is a nonzero scalar. -/
theorem OrigXiFInd2Unit_ne_zero (x : OrigXiFIndex (C3 := C3) j)
    (u : (v : OrigXiFPlaceIndex (C3 := C3) j x) ->
      {a : ℚ_[C3.p]ˣ // ‖(a : ℚ_[C3.p])‖ = 1})
    (v : OrigXiFPlaceIndex (C3 := C3) j x) :
    ((u v).1 : ℚ_[C3.p]) ≠ 0 := by
  intro h
  have h2 : ‖((u v).1 : ℚ_[C3.p])‖ = 1 := (u v).2
  rw [h, norm_zero] at h2
  exact zero_ne_one h2

/-- The copy unit as an element of the completed integer ring. -/
noncomputable def OrigXiFInd2IntegralUnit (x : OrigXiFIndex (C3 := C3) j)
    (u : (v : OrigXiFPlaceIndex (C3 := C3) j x) ->
      {a : ℚ_[C3.p]ˣ // ‖(a : ℚ_[C3.p])‖ = 1})
    (v : OrigXiFPlaceIndex (C3 := C3) j x) : ℤ_[C3.p] :=
  ⟨((u v).1 : ℚ_[C3.p]), le_of_eq (u v).2⟩

/-- The actual action of one unit copy on one completion packet. -/
noncomputable def OrigXiFInd2FactorEquiv (x : OrigXiFIndex (C3 := C3) j)
    (u : (v : OrigXiFPlaceIndex (C3 := C3) j x) ->
      {a : ℚ_[C3.p]ˣ // ‖(a : ℚ_[C3.p])‖ = 1}) :
    CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x) ≃ₗ[ℚ_[C3.p]]
      CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x) where
  toFun f v := ((u v).1 : ℚ_[C3.p]) • f v
  invFun f v := ((((u v).1 : ℚ_[C3.p])))⁻¹ • f v
  left_inv f := by
    funext v
    show ((((u v).1 : ℚ_[C3.p]))⁻¹ • (((u v).1 : ℚ_[C3.p]) • f v)) = f v
    rw [smul_smul, inv_mul_cancel₀ (OrigXiFInd2Unit_ne_zero (C3 := C3) (j := j) x u v),
      one_smul]
  right_inv f := by
    funext v
    show (((u v).1 : ℚ_[C3.p]) • ((((u v).1 : ℚ_[C3.p])))⁻¹ • f v) = f v
    rw [smul_smul, mul_inv_cancel₀ (OrigXiFInd2Unit_ne_zero (C3 := C3) (j := j) x u v),
      one_smul]
  map_add' f g := by
    funext v
    exact smul_add _ (f v) (g v)
  map_smul' a f := by
    funext v
    show ((u v).1 : ℚ_[C3.p]) • (a • f v) = a • ((u v).1 : ℚ_[C3.p]) • f v
    rw [smul_smul, smul_smul, mul_comm]

/-- The one unit copy action preserves the log-shell at a place. -/
theorem OrigXiFInd2FactorEquiv_mem_logRegion (x : OrigXiFIndex (C3 := C3) j)
    (u : (v : OrigXiFPlaceIndex (C3 := C3) j x) ->
      {a : ℚ_[C3.p]ˣ // ‖(a : ℚ_[C3.p])‖ = 1})
    (a : CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
    (ha : a ∈ completionPacketLogRegion (OrigXiFPaperPlaces (C3 := C3) j x)) :
    OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x u a ∈
      completionPacketLogRegion (OrigXiFPaperPlaces (C3 := C3) j x) := by
  intro v _
  have hv : a v ∈ integralLogShell (K := CommonPrimeCompletion
      (OrigXiFPaperPlaces (C3 := C3) j x v)) (p := C3.p) := ha v (Set.mem_univ v)
  have hmem := integralLogShell_padicInt_mul_mem (p := C3.p)
    (K := CommonPrimeCompletion (OrigXiFPaperPlaces (C3 := C3) j x v))
    (OrigXiFInd2IntegralUnit (C3 := C3) (j := j) x u v) hv
  show ((u v).1 : ℚ_[C3.p]) • a v ∈ _
  rw [Algebra.smul_def]
  exact hmem

/-- The same for the inverse unit action. -/
theorem OrigXiFInd2FactorEquiv_symm_mem_logRegion (x : OrigXiFIndex (C3 := C3) j)
    (u : (v : OrigXiFPlaceIndex (C3 := C3) j x) ->
      {a : ℚ_[C3.p]ˣ // ‖(a : ℚ_[C3.p])‖ = 1})
    (a : CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
    (ha : a ∈ completionPacketLogRegion (OrigXiFPaperPlaces (C3 := C3) j x)) :
    (OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x u).symm a ∈
      completionPacketLogRegion (OrigXiFPaperPlaces (C3 := C3) j x) := by
  intro v _
  have hv : a v ∈ integralLogShell (K := CommonPrimeCompletion
      (OrigXiFPaperPlaces (C3 := C3) j x v)) (p := C3.p) := ha v (Set.mem_univ v)
  have hinv : ‖((((u v).1 : ℚ_[C3.p]))⁻¹)‖ = 1 := by
    rw [norm_inv, (u v).2, inv_one]
  have hmem := integralLogShell_padicInt_mul_mem (p := C3.p)
    (K := CommonPrimeCompletion (OrigXiFPaperPlaces (C3 := C3) j x v))
    (⟨((((u v).1 : ℚ_[C3.p]))⁻¹), le_of_eq hinv⟩) hv
  show ((((u v).1 : ℚ_[C3.p]))⁻¹ • a v) ∈ _
  rw [Algebra.smul_def]
  exact hmem

/-- (Ind2) actual action of the independent unit copies on the paper output
carrier. -/
noncomputable def OrigXiFInd2Equiv (u : OrigXiFInd2Unit (C3 := C3) j) :
    OrigXiFPaperOutputCarrier (C3 := C3) j ≃ₗ[ℚ_[C3.p]]
      OrigXiFPaperOutputCarrier (C3 := C3) j :=
  PiTensorProduct.congr
    (fun x => OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x (u x))

theorem OrigXiFInd2Equiv_apply_tprod (u : OrigXiFInd2Unit (C3 := C3) j)
    (a : (x : OrigXiFIndex (C3 := C3) j) ->
      CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x)) :
    OrigXiFInd2Equiv (C3 := C3) (j := j) u
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
      PiTensorProduct.tprod ℚ_[C3.p]
        (fun x => OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x (u x) (a x)) := by
  rw [OrigXiFInd2Equiv]
  exact PiTensorProduct.congr_tprod
    (R := ℚ_[C3.p])
    (s := fun x => CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
    (t := fun x => CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
    (fun x => OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x (u x)) a

/-- The unit copy family acts trivially on pure tensors. -/
theorem OrigXiFInd2Equiv_one_tprod
    (a : (x : OrigXiFIndex (C3 := C3) j) ->
      CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x)) :
    OrigXiFInd2Equiv (C3 := C3) (j := j) (fun _ _ => ⟨1, by simp⟩)
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
      PiTensorProduct.tprod ℚ_[C3.p] a := by
  rw [OrigXiFInd2Equiv_apply_tprod]
  congr 1
  funext x v
  show (((1 : ℚ_[C3.p]ˣ) : ℚ_[C3.p])) • a x v = a x v
  rw [Units.val_one, one_smul]

/-- The copy family action is multiplicative on pure tensors. -/
theorem OrigXiFInd2Equiv_mul_tprod
    (u u' : OrigXiFInd2Unit (C3 := C3) j)
    (a : (x : OrigXiFIndex (C3 := C3) j) ->
      CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x)) :
    OrigXiFInd2Equiv (C3 := C3) (j := j)
        (fun x v => ⟨(u x v).1 * (u' x v).1, by
          rw [Units.val_mul, norm_mul, (u x v).2, (u' x v).2, one_mul]⟩)
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
      OrigXiFInd2Equiv (C3 := C3) (j := j) u
        (OrigXiFInd2Equiv (C3 := C3) (j := j) u'
          (PiTensorProduct.tprod ℚ_[C3.p] a)) := by
  rw [OrigXiFInd2Equiv_apply_tprod, OrigXiFInd2Equiv_apply_tprod,
    OrigXiFInd2Equiv_apply_tprod]
  congr 1
  funext x v
  show ((((u x v).1 * (u' x v).1 : ℚ_[C3.p]ˣ) : ℚ_[C3.p])) • a x v =
    (((u x v).1 : ℚ_[C3.p])) • ((((u' x v).1 : ℚ_[C3.p])) • a x v)
  rw [Units.val_mul, smul_smul]

/-- The Ind2 action fixes the actual log-shell tensor region setwise. -/
theorem OrigXiFInd2Equiv_region_fixed (u : OrigXiFInd2Unit (C3 := C3) j) :
    OrigXiFInd2Equiv (C3 := C3) (j := j) u ''
        OrigXiFPaperOutputRegion (C3 := C3) j =
      OrigXiFPaperOutputRegion (C3 := C3) j := by
  apply Set.Subset.antisymm
  · rintro z ⟨w, hw, rfl⟩
    rcases (OrigXiFPaperOutputRegion_mem_iff (C3 := C3) (j := j) w).mp hw with
      ⟨a, ha, rfl⟩
    refine (OrigXiFPaperOutputRegion_mem_iff (C3 := C3) (j := j)
      (OrigXiFInd2Equiv (C3 := C3) (j := j) u
        (PiTensorProduct.tprod ℚ_[C3.p] a))).mpr ?_
    refine ⟨fun x => OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x (u x) (a x),
      ?_, ?_⟩
    · intro x
      exact OrigXiFInd2FactorEquiv_mem_logRegion (C3 := C3) (j := j) x (u x) (a x) (ha x)
    · rw [OrigXiFInd2Equiv_apply_tprod]
  · intro z hz
    rcases (OrigXiFPaperOutputRegion_mem_iff (C3 := C3) (j := j) z).mp hz with
      ⟨a, ha, rfl⟩
    refine ⟨(OrigXiFInd2Equiv (C3 := C3) (j := j) u).symm
        (PiTensorProduct.tprod ℚ_[C3.p] a),
      ?_, LinearEquiv.apply_symm_apply _ _⟩
    have hsymm : (OrigXiFInd2Equiv (C3 := C3) (j := j) u).symm
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
        PiTensorProduct.tprod ℚ_[C3.p]
          (fun x => (OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x (u x)).symm (a x)) := by
      rw [OrigXiFInd2Equiv]
      exact PiTensorProduct.congr_symm_tprod
        (R := ℚ_[C3.p])
        (s := fun x => CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
        (t := fun x => CompletionPacket (OrigXiFPaperPlaces (C3 := C3) j x))
        (fun x => OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x (u x)) a
    rw [hsymm]
    refine (OrigXiFPaperOutputRegion_mem_iff (C3 := C3) (j := j)
      (PiTensorProduct.tprod ℚ_[C3.p]
        (fun x => (OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x (u x)).symm (a x)))).mpr ?_
    refine ⟨fun x => (OrigXiFInd2FactorEquiv (C3 := C3) (j := j) x (u x)).symm (a x),
      ?_, rfl⟩
    intro x
    exact OrigXiFInd2FactorEquiv_symm_mem_logRegion (C3 := C3) (j := j) x (u x) (a x) (ha x)

/-- Log-volume invariance under the actual Ind2 action. -/
theorem OrigXiFInd2Equiv_logVolume (u : OrigXiFInd2Unit (C3 := C3) j)
    [MeasurableSpace (OrigXiFPaperOutputCarrier (C3 := C3) j)]
    (mu : Measure (OrigXiFPaperOutputCarrier (C3 := C3) j)) :
    OrigXiFPaperOutputLogVolume C3 j mu
        (OrigXiFInd2Equiv (C3 := C3) (j := j) u ''
          OrigXiFPaperOutputRegion (C3 := C3) j) =
      OrigXiFPaperOutputLogVolume C3 j mu
        (OrigXiFPaperOutputRegion (C3 := C3) j) := by
  rw [OrigXiFInd2Equiv_region_fixed]

/-! ## 4. Ind3: the actual times-mu action and stage comparison on log-Kummer -/

/-- The actual log-Kummer times-mu stage at column `m` and place `v`. -/
abbrev OrigXiFLogKummerStage (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (m : Int) : Type _ :=
  TimesMuQuotient ((I.fPrimeStripAt 1 m).Mon v)ˣ

/-- (Ind3) the actual times-mu action of the D-prime-strip on the log-Kummer
stage. -/
noncomputable def OrigXiFInd3Action (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (m : Int) :
    (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v →*
      MulAut (OrigXiFLogKummerStage I v m) :=
  (I.fPrimeStripAt 1 m).timesMuAction v

/-- The actual Ind3 stage comparison to the core stage `0`, induced by the
actual source prime-strip link. -/
noncomputable def OrigXiFInd3StageComparison
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) (m : Int) :
    OrigXiFLogKummerStage I v m ≃* OrigXiFLogKummerStage I v 0 :=
  TimesMuQuotient.congr (Units.mapEquiv ((I.fLinkAt 1 m 1 0).isoMon v))

/-- The actual log-volume readout on the log-Kummer stage: the realified degree
of the times-mu prime-strip. -/
noncomputable def OrigXiFLogKummerLogVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) (m : Int) :
    OrigXiFLogKummerStage I v m →* Multiplicative ℝ :=
  FPrimeStrip.timesMuDegreeOfUnits (I.fPrimeStripAt 1 m) v

/-- The Ind3 stage comparison preserves the actual log-volume readout. -/
theorem OrigXiFInd3StageComparison_logVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) (m : Int)
    (x : OrigXiFLogKummerStage I v m) :
    OrigXiFLogKummerLogVolume I v 0 (OrigXiFInd3StageComparison I v m x) =
      OrigXiFLogKummerLogVolume I v m x := by
  refine Quotient.inductionOn x ?_
  intro u
  show (FPrimeStrip.timesMuDegreeOfUnits (I.fPrimeStripAt 1 0) v)
      ((TimesMuQuotient.congr (Units.mapEquiv ((I.fLinkAt 1 m 1 0).isoMon v)))
        (TimesMuQuotient.quotientMap u)) =
    (FPrimeStrip.timesMuDegreeOfUnits (I.fPrimeStripAt 1 m) v)
      (TimesMuQuotient.quotientMap u)
  simp only [TimesMuQuotient.congr_quotientMap,
    FPrimeStrip.timesMuDegreeOfUnits_quotientMap, Units.coe_mapEquiv]
  exact (I.fLinkAt 1 m 1 0).compatDegree v (u : (I.fPrimeStripAt 1 m).Mon v)

/-- The actual Ind3 action is compatible with the stage comparison. -/
theorem OrigXiFInd3StageComparison_action
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    (x : OrigXiFLogKummerStage I v m) :
    OrigXiFInd3StageComparison I v m (OrigXiFInd3Action I v m g x) =
      OrigXiFInd3Action I v 0 ((I.fLinkAt 1 m 1 0).isoPi v g)
        (OrigXiFInd3StageComparison I v m x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show (TimesMuQuotient.congr (Units.mapEquiv ((I.fLinkAt 1 m 1 0).isoMon v)))
      (((I.fPrimeStripAt 1 m).timesMuAction v) g (TimesMuQuotient.quotientMap u)) =
    ((I.fPrimeStripAt 1 0).timesMuAction v) ((I.fLinkAt 1 m 1 0).isoPi v g)
      ((TimesMuQuotient.congr (Units.mapEquiv ((I.fLinkAt 1 m 1 0).isoMon v)))
        (TimesMuQuotient.quotientMap u))
  simp only [TimesMuQuotient.congr_quotientMap,
    FPrimeStrip.timesMuAction_quotientMap]
  exact congrArg TimesMuQuotient.quotientMap
    (FPrimeStripEquiv.unitsAction_compat (I.fLinkAt 1 m 1 0) v g u)

/-- The actual log-Kummer stage region: the whole times-mu quotient stage. -/
def OrigXiFLogKummerRegion (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (m : Int) : Set (OrigXiFLogKummerStage I v m) :=
  Set.univ

/-- The Ind3 times-mu action preserves the actual log-Kummer stage region. -/
theorem OrigXiFInd3Action_region_fixed
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v) :
    OrigXiFInd3Action I v m g '' OrigXiFLogKummerRegion I v m =
      OrigXiFLogKummerRegion I v m := by
  rw [OrigXiFLogKummerRegion]
  exact Set.eq_univ_of_forall (fun y =>
    ⟨(OrigXiFInd3Action I v m g).symm y, Set.mem_univ _,
      MulEquiv.apply_symm_apply _ _⟩)

/-! ## 5. The actual Indeterminacies package -/

/-- The actual Ind1/Ind2/Ind3 data on the paper output carrier and on
log-Kummer, with representation laws and the actual region/log-volume
invariance statements. -/
structure OrigXiFIndeterminaciesActual (j : Nat) (v : V)
    [MeasurableSpace (OrigXiFPaperOutputCarrier (C3 := C3) j)]
    (mu : Measure (OrigXiFPaperOutputCarrier (C3 := C3) j)) where
  /-- Ind1: actual capsule-permutation actions on the paper output carrier. -/
  ind1 : Equiv.Perm (Fin (j + 1)) →
    (OrigXiFPaperOutputCarrier (C3 := C3) j ≃ₗ[ℚ_[C3.p]]
      OrigXiFPaperOutputCarrier (C3 := C3) j)
  ind1_eq : forall sigma, ind1 sigma = OrigXiFInd1Equiv (C3 := C3) (j := j) sigma
  /-- Ind1 representation laws, on the pure-tensor generators. -/
  ind1_one_tprod : forall a,
    OrigXiFInd1Equiv (C3 := C3) (j := j) (Equiv.refl (Fin (j + 1)))
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
      PiTensorProduct.tprod ℚ_[C3.p] a
  ind1_mul : forall sigma tau,
    (ind1 sigma).trans (ind1 tau) = ind1 (sigma.trans tau)
  /-- Ind2: actual independent norm-one unit copy actions. -/
  ind2 : OrigXiFInd2Unit (C3 := C3) j →
    (OrigXiFPaperOutputCarrier (C3 := C3) j ≃ₗ[ℚ_[C3.p]]
      OrigXiFPaperOutputCarrier (C3 := C3) j)
  ind2_eq : forall u, ind2 u = OrigXiFInd2Equiv (C3 := C3) (j := j) u
  /-- Ind2 representation laws, on the pure-tensor generators. -/
  ind2_one_tprod : forall a,
    OrigXiFInd2Equiv (C3 := C3) (j := j) (fun _ _ => ⟨1, by simp⟩)
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
      PiTensorProduct.tprod ℚ_[C3.p] a
  ind2_mul_tprod : forall (u u' : OrigXiFInd2Unit (C3 := C3) j) a,
    OrigXiFInd2Equiv (C3 := C3) (j := j)
        (fun x hv => ⟨(u x hv).1 * (u' x hv).1, by
          rw [Units.val_mul, norm_mul, (u x hv).2, (u' x hv).2, one_mul]⟩)
        (PiTensorProduct.tprod ℚ_[C3.p] a) =
      OrigXiFInd2Equiv (C3 := C3) (j := j) u
        (OrigXiFInd2Equiv (C3 := C3) (j := j) u'
          (PiTensorProduct.tprod ℚ_[C3.p] a))
  /-- Ind3: the actual times-mu action on the log-Kummer stage. -/
  ind3 : (I.fPrimeStripAt 1 0).toDPrimeStrip.Pi v →*
    MulAut (OrigXiFLogKummerStage I v 0)
  ind3_eq : forall g, ind3 g = OrigXiFInd3Action I v 0 g
  /-- The paper output region is fixed by Ind1. -/
  ind1_region : forall sigma,
    OrigXiFInd1Equiv (C3 := C3) (j := j) sigma ''
        OrigXiFPaperOutputRegion (C3 := C3) j =
      OrigXiFPaperOutputRegion (C3 := C3) j
  /-- The paper output region is fixed by Ind2. -/
  ind2_region : forall u,
    OrigXiFInd2Equiv (C3 := C3) (j := j) u ''
        OrigXiFPaperOutputRegion (C3 := C3) j =
      OrigXiFPaperOutputRegion (C3 := C3) j
  /-- The paper output log-volume is unchanged by Ind1. -/
  ind1_logVolume : forall sigma,
    OrigXiFPaperOutputLogVolume C3 j mu
        (OrigXiFInd1Equiv (C3 := C3) (j := j) sigma ''
          OrigXiFPaperOutputRegion (C3 := C3) j) =
      OrigXiFPaperOutputLogVolume C3 j mu
        (OrigXiFPaperOutputRegion (C3 := C3) j)
  /-- The paper output log-volume is unchanged by Ind2. -/
  ind2_logVolume : forall u,
    OrigXiFPaperOutputLogVolume C3 j mu
        (OrigXiFInd2Equiv (C3 := C3) (j := j) u ''
          OrigXiFPaperOutputRegion (C3 := C3) j) =
      OrigXiFPaperOutputLogVolume C3 j mu
        (OrigXiFPaperOutputRegion (C3 := C3) j)
  /-- The Ind3 stage comparison preserves the log-Kummer log-volume readout. -/
  ind3_logVolume : forall (m : Int) (x : OrigXiFLogKummerStage I v m),
    OrigXiFLogKummerLogVolume I v 0 (OrigXiFInd3StageComparison I v m x) =
      OrigXiFLogKummerLogVolume I v m x
  /-- The Ind3 action preserves the log-Kummer region. -/
  ind3_region : forall (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v),
    OrigXiFInd3Action I v m g '' OrigXiFLogKummerRegion I v m =
      OrigXiFLogKummerRegion I v m
  /-- The Ind3 action is compatible with the stage comparison. -/
  ind3_comparison : forall (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    (x : OrigXiFLogKummerStage I v m),
    OrigXiFInd3StageComparison I v m (OrigXiFInd3Action I v m g x) =
      OrigXiFInd3Action I v 0 ((I.fLinkAt 1 m 1 0).isoPi v g)
        (OrigXiFInd3StageComparison I v m x)

/-- The actual Indeterminacies package. -/
noncomputable def origXiFIndeterminaciesActual (j : Nat) (v : V)
    [MeasurableSpace (OrigXiFPaperOutputCarrier (C3 := C3) j)]
    (mu : Measure (OrigXiFPaperOutputCarrier (C3 := C3) j)) :
    OrigXiFIndeterminaciesActual (C3 := C3) (I := I) j v mu where
  ind1 := fun sigma => OrigXiFInd1Equiv (C3 := C3) (j := j) sigma
  ind1_eq := fun sigma => rfl
  ind1_one_tprod := fun a => OrigXiFInd1Equiv_one_tprod (C3 := C3) (j := j) a
  ind1_mul := fun sigma tau => OrigXiFInd1Equiv_trans (C3 := C3) (j := j) sigma tau
  ind2 := fun u => OrigXiFInd2Equiv (C3 := C3) (j := j) u
  ind2_eq := fun u => rfl
  ind2_one_tprod := fun a => OrigXiFInd2Equiv_one_tprod (C3 := C3) (j := j) a
  ind2_mul_tprod := fun u u' a =>
    OrigXiFInd2Equiv_mul_tprod (C3 := C3) (j := j) u u' a
  ind3 := OrigXiFInd3Action I v 0
  ind3_eq := fun g => rfl
  ind1_region := fun sigma => OrigXiFInd1Equiv_region_fixed (C3 := C3) (j := j) sigma
  ind2_region := fun u => OrigXiFInd2Equiv_region_fixed (C3 := C3) (j := j) u
  ind1_logVolume := fun sigma =>
    OrigXiFInd1Equiv_logVolume (C3 := C3) (j := j) sigma mu
  ind2_logVolume := fun u =>
    OrigXiFInd2Equiv_logVolume (C3 := C3) (j := j) u mu
  ind3_logVolume := fun m x => OrigXiFInd3StageComparison_logVolume I v m x
  ind3_region := fun m g => OrigXiFInd3Action_region_fixed I v m g
  ind3_comparison := fun m g x => OrigXiFInd3StageComparison_action I v m g x

end LeanFormal.IUT.XiFPaper.OrigXiFIndeterminaciesActual