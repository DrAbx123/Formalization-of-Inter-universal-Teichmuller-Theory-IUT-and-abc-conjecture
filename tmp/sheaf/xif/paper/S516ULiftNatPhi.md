# S516: ULift Nat DivisorialAddMonoid and Qv-Phi ramification model

Date: 2026-10-29. Independent construction; no fake ramification index.

## DivisorialAddMonoid at universe u+1

uliftNatDivisorialAddMonoid : DivisorialAddMonoid.{u+1}
  carrier := ULift.{u+1} Nat
  integral: Nat.add_left_cancel via ULift.down
  sharp: IsAddUnit maps to Nat, Nat.isAddUnit_iff
  saturated: Grothendieck equality mapped by stageDivisorGrothendieckEquivInt;
    nonnegativity then Int.toNat gives the preimage.

## Multiplication by e

uliftNatMulLeft e : ULift Nat ->+ ULift Nat
  n |-> ULift.up (e * n.down)
map_zero/map_add proved.
uliftNatMulLeft_injective: e > 0 gives injective via Nat.mul_left_cancel.

## Qv-Phi ramification model

QvRamificationIndexData K:
  index : (X -> Y) -> Nat
  positive, id, comp, and iso-arrow index=1 laws.

qvPhiRamificationModel E : DivisorialMonoidOn (Example32SmallBase K) (IsIso)
  obj X := uliftNatDivisorialAddMonoid
  pullback f := uliftNatMulLeft (E.index f)
  pullback_id/comp, characteristicallyInjective, fsmPullbackIsIso proved.

No τ, no q_v value, no completion/L.
