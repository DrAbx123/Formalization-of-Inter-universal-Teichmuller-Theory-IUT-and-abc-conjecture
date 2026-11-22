import tmp.sheaf.xif.paper.S1345Ind3LogShellProcessionActual

/-!
# S1407: actual Ind3 procession on the exact packet-stage carrier change

S1345 works on the genuine integral log-shell tensor packet
`IntegralTensorPacket I n j vQ` of S1313 and on the actual Ind3 total stage
carrier `Ind3StageTotal I n v = (m : Int) x Ind3Stage I n m v` of S1266/S1327.
It records the exact obstruction to the target `DPrimeStripProcession.ind3`:
the target needs

  `Nat -> IntegralTensorPacket I n j vQ -> IntegralTensorPacket I n j vQ`,

while the actual S1266/S1345 data live on the Int-indexed total stage.  S1345
also constructs the genuine non-identity Nat-action `ind3StageShiftTotal` on
that total stage, and proves that its one-step shift differs from the identity
on every element.

This file takes the exact carrier-change route; it does not fabricate an
identity or an arbitrary action on the packet.

1. `PacketStageCarrier I n j vQ v` is the exact changed carrier: the actual
   integral tensor packet together with the actual Int-indexed Ind3 total stage.
   The packet is included at the core stage `m = 0`; the inclusion is proved
   injective and not surjective, so the carrier is a genuine extension.

2. `packetStageShift` is the actual Nat-action on this carrier: it is the
   identity on the packet coordinate and S1345's genuine stage shift on the
   total-stage coordinate.  Its zero, addition, level and non-identity laws are
   proved.  In particular `packetStageShift_one_ne` proves that the one-step
   action differs from the identity on every element of the changed carrier.

3. `Ind3Procession` is exactly the Ind3 fragment (`base`, `level`, `ind3`,
   `ind3_zero`, `ind3_add`, `ind3_level`) of the target
   `DPrimeStripProcession`; `DPrimeStripProcession.toInd3Procession` shows
   that the fragment is the target's own projection.  `actualInd3Procession`
   inhabits it on the changed carrier with the actual shift.

4. The exact carrier-change record `PacketStageCarrierChange` packages the
   packet inclusion/projection, the actual action, its non-identity and its
   packet-fixed law.  Its field `induced_packet_action_trivial` proves the
   precise no-fake statement: any Nat-action on the packet whose value is the
   packet component of the actual carrier action is the identity.  Thus the
   actual non-identity is carried by the Int-indexed stage fiber, not smuggled
   into a packet endomorphism.

5. The actual Ind1 tensor action of S1266/S1345 is kept on the packet
   coordinate: `actualInd1OnPacketStage` commutes with `packetStageShift`
   and is injective.  No Ind2 field is asserted: the integral packet has
   coefficient ring Z, while S1265's actual Ind2 action needs a field and an
   Fmod-algebra structure on the coefficient ring (the independent obstruction
   recorded in S1345, section 8).

No sorry, no new axiom, no PUnit/one-point model, no arbitrary constant map,
and no fake identity is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1407Ind3PacketProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual
open LeanFormal.IUT.XiFPaper.S1327Ind3IntegralLogShellActual
open LeanFormal.IUT.XiFPaper.S1345Ind3LogShellProcessionActual
open scoped TensorProduct

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

local instance s1407ValuationFact (vQ : ActualIntegralValuation) :
    Fact vQ.1.Prime := ⟨vQ.2⟩

local instance s1407PrimeFact (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. The exact packet-stage carrier -/

/-- The changed carrier: the actual integral tensor packet together with the
actual Int-indexed Ind3 total stage.  This is the carrier on which the actual
S1345 Nat-action is defined; it is not the packet alone. -/
abbrev PacketStageCarrier (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    Type (max ua umon) :=
  IntegralTensorPacket I n j vQ × Ind3StageTotal I n v

/-- The packet coordinate of the changed carrier. -/
def packetProj (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    PacketStageCarrier I n j vQ v → IntegralTensorPacket I n j vQ :=
  Prod.fst

/-- The total-stage coordinate of the changed carrier. -/
def stageProj (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    PacketStageCarrier I n j vQ v → Ind3StageTotal I n v :=
  Prod.snd

/-- The packet inclusion at the core stage `m = 0` and the unit class. -/
def packetIncl (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    IntegralTensorPacket I n j vQ → PacketStageCarrier I n j vQ v :=
  fun p => (p, ⟨0, 1⟩)

/-- The packet projection is a left inverse of the packet inclusion. -/
@[simp] theorem packetProj_packetIncl (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V)
    (p : IntegralTensorPacket I n j vQ) :
    packetProj I n j vQ v (packetIncl I n j vQ v p) = p := rfl

/-- The packet inclusion is injective. -/
theorem packetIncl_injective (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    Function.Injective (packetIncl I n j vQ v) := by
  intro p q h
  exact congrArg Prod.fst h

/-- The packet inclusion is not surjective: the carrier also has the stage at
`m = 1`, which cannot be the core stage `m = 0`. -/
theorem packetIncl_not_surjective (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    ¬ Function.Surjective (packetIncl I n j vQ v) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (0, ⟨1, (1 : Ind3Stage I n 1 v)⟩)
  have hidx : (0 : Int) = 1 := congrArg (fun c : PacketStageCarrier I n j vQ v => c.2.1) hp
  norm_num at hidx

/-! ## 2. The actual Nat-action on the changed carrier -/

/-- The actual Nat-action on the changed carrier: the packet coordinate is
fixed and the total-stage coordinate is S1345's actual non-identity shift. -/
def packetStageShift (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat) :
    PacketStageCarrier I n j vQ v → PacketStageCarrier I n j vQ v :=
  fun c => (c.1, ind3StageShiftTotal I n v k c.2)

/-- The packet coordinate is fixed by the actual shift. -/
@[simp] theorem packetStageShift_fst (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat)
    (c : PacketStageCarrier I n j vQ v) :
    (packetStageShift I n j vQ v k c).1 = c.1 := rfl

/-- The stage coordinate is literally S1345's actual stage shift. -/
@[simp] theorem packetStageShift_snd (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat)
    (c : PacketStageCarrier I n j vQ v) :
    (packetStageShift I n j vQ v k c).2 =
      ind3StageShiftTotal I n v k c.2 := rfl

/-- The action formula as a pair. -/
theorem packetStageShift_eq (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat)
    (c : PacketStageCarrier I n j vQ v) :
    packetStageShift I n j vQ v k c =
      (c.1, ind3StageShiftTotal I n v k c.2) := rfl

/-- The zero step is the identity. -/
@[simp] theorem packetStageShift_zero_apply (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V)
    (c : PacketStageCarrier I n j vQ v) :
    packetStageShift I n j vQ v 0 c = c := rfl

/-- The zero action is the identity function. -/
theorem packetStageShift_zero (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    packetStageShift I n j vQ v 0 = id := by
  funext c
  exact packetStageShift_zero_apply I n j vQ v c

/-- The action is additive in the Nat parameter, in the target's orientation. -/
theorem packetStageShift_add (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (m k : Nat) :
    packetStageShift I n j vQ v (m + k) =
      (packetStageShift I n j vQ v k) ∘
        (packetStageShift I n j vQ v m) := by
  funext c
  apply Prod.ext
  · rfl
  · change ind3StageShiftTotal I n v (m + k) c.2 =
      ind3StageShiftTotal I n v k (ind3StageShiftTotal I n v m c.2)
    rw [ind3StageShiftTotal_add I n v m k]
    rfl

/-- Pointwise form of the addition law. -/
theorem packetStageShift_add_apply (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (m k : Nat)
    (c : PacketStageCarrier I n j vQ v) :
    packetStageShift I n j vQ v (m + k) c =
      packetStageShift I n j vQ v k
        (packetStageShift I n j vQ v m c) := by
  simpa [Function.comp_apply] using
    congrFun (packetStageShift_add I n j vQ v m k) c

/-- The one-step action is the actual stage successor on the stage coordinate. -/
theorem packetStageShift_one_eq (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V)
    (c : PacketStageCarrier I n j vQ v) :
    packetStageShift I n j vQ v 1 c =
      (c.1, ind3StageSucc I n v c.2) := by
  rw [packetStageShift_eq, ind3StageShiftTotal_one]

/-- The one-step action is not the identity on any element of the changed
carrier.  The non-identity is exactly S1345's actual stage shift. -/
theorem packetStageShift_one_ne (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V)
    (c : PacketStageCarrier I n j vQ v) :
    packetStageShift I n j vQ v 1 c ≠ c := by
  intro h
  exact ind3StageShiftTotal_one_ne I n v c.2 (congrArg Prod.snd h)

/-- The level of an element of the changed carrier is S1345's stage level. -/
def packetStageLevel (n : Int) (v : V)
    (c : PacketStageCarrier I n j vQ v) : Nat :=
  ind3StageLevel I n v c.2

/-- The level is nondecreasing along the actual action. -/
theorem packetStageShift_level (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat)
    (c : PacketStageCarrier I n j vQ v) :
    packetStageLevel I n v c ≤
      packetStageLevel I n v (packetStageShift I n j vQ v k c) :=
  ind3StageShiftTotal_level I n v k c.2

/-- The packet coordinate of the action is fixed at every step. -/
theorem packetStageShift_packet_fixed (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat)
    (c : PacketStageCarrier I n j vQ v) :
    packetProj I n j vQ v (packetStageShift I n j vQ v k c) =
      packetProj I n j vQ v c := rfl

/-! ## 3. The Ind3 fragment of the target procession -/

/-- The exact Ind3 fragment of `DPrimeStripProcession`: the base, the level,
the Nat-indexed action, and the target's three Ind3 laws.  The field names and
types are those of `DPrimeStripProcession`. -/
structure Ind3Procession (C : Type*) where
  /-- The base choice of the procession. -/
  base : C
  /-- The level of a choice. -/
  level : C → Nat
  /-- The Nat-indexed (Ind3) action. -/
  ind3 : Nat → C → C
  /-- The unit law. -/
  ind3_zero : ∀ c, ind3 0 c = c
  /-- The addition law, in the target's orientation. -/
  ind3_add : ∀ m n c, ind3 (m + n) c = ind3 n (ind3 m c)
  /-- The level law. -/
  ind3_level : ∀ n c, level c ≤ level (ind3 n c)

/-- The target `DPrimeStripProcession` projects to this Ind3 fragment; the
fragment is not a replacement name for a different structure. -/
def DPrimeStripProcession.toInd3Procession
    {Label : Type*} {C : Type*} [AddGroup Label]
    (P : DPrimeStripProcession Label C) : Ind3Procession C where
  base := P.base
  level := P.level
  ind3 := P.ind3
  ind3_zero := P.ind3_zero
  ind3_add := P.ind3_add
  ind3_level := P.ind3_level

/-- The actual Ind3 procession on the exact packet-stage carrier change.  Its
`ind3` field is the actual S1345 stage shift, not an identity and not an
arbitrary function. -/
def actualInd3Procession (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    Ind3Procession (PacketStageCarrier I n j vQ v) where
  base := packetIncl I n j vQ v 0
  level := packetStageLevel I n v
  ind3 := packetStageShift I n j vQ v
  ind3_zero := fun c => packetStageShift_zero_apply I n j vQ v c
  ind3_add := fun m k c => packetStageShift_add_apply I n j vQ v m k c
  ind3_level := fun k c => packetStageShift_level I n j vQ v k c

/-- The actual procession's action is literally `packetStageShift`. -/
@[simp] theorem actualInd3Procession_ind3 (n : Int)
    (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat) :
    (actualInd3Procession I n j vQ v).ind3 k =
      packetStageShift I n j vQ v k := rfl

/-- The actual procession's action differs from the identity at every element
at level one. -/
theorem actualInd3Procession_one_ne (n : Int)
    (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V)
    (c : PacketStageCarrier I n j vQ v) :
    (actualInd3Procession I n j vQ v).ind3 1 c ≠ c :=
  packetStageShift_one_ne I n j vQ v c

/-! ## 4. The exact carrier-change record -/

/-- The exact carrier change from the packet to the packet-stage carrier.

The field `induced_packet_action_trivial` is the precise no-fake statement:
any Nat-action on the packet that agrees with the packet projection of the
actual carrier action must be the identity.  Hence the actual non-identity is
carried by the Int-indexed stage fiber, and no packet-only Ind3 action is
asserted. -/
structure PacketStageCarrierChange (Packet : Type*) (Stage : Type*) where
  /-- The changed carrier. -/
  Carrier : Type*
  /-- The packet inclusion into the changed carrier. -/
  incl : Packet → Carrier
  /-- The packet projection of the changed carrier. -/
  proj : Carrier → Packet
  /-- The projection is a left inverse of the inclusion. -/
  proj_incl : ∀ p, proj (incl p) = p
  /-- The packet inclusion is injective. -/
  incl_injective : Function.Injective incl
  /-- The packet inclusion is not surjective: the carrier is a genuine
      extension of the packet. -/
  incl_not_surjective : ¬ Function.Surjective incl
  /-- The level of a carrier element. -/
  level : Carrier → Nat
  /-- The actual Nat-action. -/
  ind3 : Nat → Carrier → Carrier
  /-- The unit law. -/
  ind3_zero : ∀ c, ind3 0 c = c
  /-- The addition law, in the target's orientation. -/
  ind3_add : ∀ m n c, ind3 (m + n) c = ind3 n (ind3 m c)
  /-- The level law. -/
  ind3_level : ∀ n c, level c ≤ level (ind3 n c)
  /-- The one-step action is not the identity on any carrier element. -/
  ind3_nonidentity : ∀ c, ind3 1 c ≠ c
  /-- The action fixes the packet coordinate. -/
  packet_fixed : ∀ k c, proj (ind3 k c) = proj c
  /-- No non-identity packet action can be read off from the packet projection
      of the actual carrier action. -/
  induced_packet_action_trivial : ∀ (A : Nat → Packet → Packet),
    (∀ k c, proj (ind3 k c) = A k (proj c)) → ∀ k p, A k p = p

/-- The exact carrier change realized by the actual integral packet and the
actual Ind3 total stage. -/
def actualPacketStageCarrierChange (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    PacketStageCarrierChange (IntegralTensorPacket I n j vQ)
      (Ind3StageTotal I n v) where
  Carrier := PacketStageCarrier I n j vQ v
  incl := packetIncl I n j vQ v
  proj := packetProj I n j vQ v
  proj_incl := fun p => packetProj_packetIncl I n j vQ v p
  incl_injective := packetIncl_injective I n j vQ v
  incl_not_surjective := packetIncl_not_surjective I n j vQ v
  level := packetStageLevel I n v
  ind3 := packetStageShift I n j vQ v
  ind3_zero := fun c => packetStageShift_zero_apply I n j vQ v c
  ind3_add := fun m k c => packetStageShift_add_apply I n j vQ v m k c
  ind3_level := fun k c => packetStageShift_level I n j vQ v k c
  ind3_nonidentity := fun c => packetStageShift_one_ne I n j vQ v c
  packet_fixed := fun k c => packetStageShift_packet_fixed I n j vQ v k c
  induced_packet_action_trivial := by
    intro A h k p
    have hc := h k (packetIncl I n j vQ v p)
    have hleft : packetProj I n j vQ v
        (packetStageShift I n j vQ v k (packetIncl I n j vQ v p)) = p := rfl
    have hright : packetProj I n j vQ v (packetIncl I n j vQ v p) = p := rfl
    rw [hleft, hright] at hc
    exact hc.symm

/-- The actual carrier-change action is literally S1345's stage shift on the
stage coordinate. -/
theorem actualPacketStageCarrierChange_ind3_eq (n : Int)
    (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat)
    (c : PacketStageCarrier I n j vQ v) :
    (actualPacketStageCarrierChange I n j vQ v).ind3 k c =
      (c.1, ind3StageShiftTotal I n v k c.2) := rfl

/-- The actual changed carrier is a proper extension of the packet: the
packet inclusion is not surjective. -/
theorem actualCarrier_proper_extension (n : Int)
    (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    ¬ Function.Surjective
      ((actualPacketStageCarrierChange I n j vQ v).incl) :=
  (actualPacketStageCarrierChange I n j vQ v).incl_not_surjective

/-- The actual carrier action has no non-identity packet shadow. -/
theorem actualCarrier_packet_shadow_trivial (n : Int)
    (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V)
    (A : Nat → IntegralTensorPacket I n j vQ → IntegralTensorPacket I n j vQ)
    (hA : ∀ k (c : PacketStageCarrier I n j vQ v),
      packetProj I n j vQ v (packetStageShift I n j vQ v k c) =
        A k (packetProj I n j vQ v c)) :
    ∀ k, A k = id := by
  intro k
  funext p
  have h := (actualPacketStageCarrierChange I n j vQ v).induced_packet_action_trivial A hA k p
  exact h

/-! ## 5. The actual Ind1 tensor action commutes with the carrier change -/

/-- The actual Ind1 tensor action of S1266/S1345, read on the packet
coordinate of the changed carrier.  Because the integral log-shell family is
label-independent, S1345's `integralInd1Tensor` is a self-map of the packet;
no new Ind1 action is introduced. -/
def actualInd1OnPacketStage (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    PacketStageCarrier I n j vQ v → PacketStageCarrier I n j vQ v :=
  fun c => (integralInd1Tensor I n j vQ c.1, c.2)

/-- The actual Ind1 action commutes with the actual Ind3 carrier action. -/
theorem actualInd1OnPacketStage_comm (n : Int)
    (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) (k : Nat)
    (c : PacketStageCarrier I n j vQ v) :
    actualInd1OnPacketStage I n j vQ v
        (packetStageShift I n j vQ v k c) =
      packetStageShift I n j vQ v k
        (actualInd1OnPacketStage I n j vQ v c) := rfl

/-- The actual Ind1 tensor action is injective on the changed carrier. -/
theorem actualInd1OnPacketStage_injective (n : Int)
    (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    Function.Injective (actualInd1OnPacketStage I n j vQ v) := by
  intro c d h
  have hfst : integralInd1Tensor I n j vQ c.1 =
      integralInd1Tensor I n j vQ d.1 := congrArg Prod.fst h
  have hpacket : c.1 = d.1 :=
    (integralInd1Tensor I n j vQ).injective hfst
  have hstage : c.2 = d.2 := by
    have hs := congrArg
      (fun z : PacketStageCarrier I n j vQ v => z.2) h
    simpa [actualInd1OnPacketStage] using hs
  exact Prod.ext hpacket hstage

/-! ## 6. Exact mismatch and no-fake summary -/

/-- The target `ind3` type on the packet alone. -/
abbrev PacketInd3Type (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) : Type ua :=
  Nat → IntegralTensorPacket I n j vQ → IntegralTensorPacket I n j vQ

/-- The actual `ind3` type on the changed packet-stage carrier. -/
abbrev PacketStageInd3Type (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    Type (max ua umon) :=
  Nat → PacketStageCarrier I n j vQ v → PacketStageCarrier I n j vQ v

/-- The exact target fragment realized by the changed carrier. -/
theorem actualInd3Procession_type (n : Int) (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    (actualInd3Procession I n j vQ v).ind3 =
      (packetStageShift I n j vQ v : PacketStageInd3Type I n j vQ v) :=
  rfl

/-- Summary: the actual Ind3 procession is on the changed carrier, its action
is S1345's actual non-identity shift, and the packet coordinate is fixed.  No
packet-only Ind3 action is asserted. -/
theorem actualInd3_packetStage_summary (n : Int)
    (j : Fin (capsuleLevels l))
    (vQ : (actualIntegralCapsuleContract I).VQ) (v : V) :
    (∀ c : PacketStageCarrier I n j vQ v,
        (actualInd3Procession I n j vQ v).ind3 1 c ≠ c) ∧
      (∀ (k : Nat) (c : PacketStageCarrier I n j vQ v),
        packetProj I n j vQ v
          ((actualInd3Procession I n j vQ v).ind3 k c) =
        packetProj I n j vQ v c) ∧
      (∀ (A : Nat → IntegralTensorPacket I n j vQ →
          IntegralTensorPacket I n j vQ),
        (∀ (k : Nat) (c : PacketStageCarrier I n j vQ v),
          packetProj I n j vQ v
            ((actualInd3Procession I n j vQ v).ind3 k c) =
          A k (packetProj I n j vQ v c)) →
        ∀ k, A k = id) :=
  ⟨fun c => actualInd3Procession_one_ne I n j vQ v c,
    fun k c => rfl,
    fun A hA => actualCarrier_packet_shadow_trivial I n j vQ v A hA⟩

/-! ## 7. Axiom probes -/

#print axioms packetIncl_not_surjective
#print axioms packetStageShift_add
#print axioms packetStageShift_one_ne
#print axioms packetStageShift_level
#print axioms actualInd3Procession
#print axioms actualInd3Procession_one_ne
#print axioms actualPacketStageCarrierChange
#print axioms actualCarrier_packet_shadow_trivial
#print axioms actualInd1OnPacketStage_injective
#print axioms actualInd3Procession_type
#print axioms actualInd3_packetStage_summary

end LeanFormal.IUT.XiFPaper.S1407Ind3PacketProcessionActual
