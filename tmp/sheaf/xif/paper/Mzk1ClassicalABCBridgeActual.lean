/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib.Tactic

/-! # A873/A875: ClassicalABC (lana shape) <-> ABCConjecture (our Statement) -/

/- PROVENANCE: lana `Iut/Abc/Classical.lean:38` defines `ClassicalABC` with the shape
  `forall eps>0, exists C, forall a b c : Nat, 0<a -> 0<b -> Nat.Coprime a b -> a+b=c ->
     (c:Real) <= C * ((radical (a*b*c) : Nat) : Real) ^ (1+eps)`.
We use `LeanFormal.IUT.radical` (= `natRadical` = Mathlib UFD radical) and write the
real power as `Real.rpow`, which is exactly `^` on `Real` with real exponent.
Our statement (ABCBridge/Statement.lean:28-35) uses `PrimitiveAdditiveTriple`
`= 0<a ∧ 0<b ∧ a+b=c ∧ Nat.Coprime a b` and requires `0<K`.  The iff below handles the
conjunction order, the positivity of `K` (`K = max C 1`) and the `rpow` shape. -/

noncomputable section

open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Mzk1ClassicalABCBridgeActual

/-- Radical by factorization (dictionary candidate for lana/Mathlib `radical`). -/
def radShape (n : ℕ) : ℕ := (Nat.factorization n).support.prod (fun p => p)

/-- lana `ClassicalABC` shape, written on our `radical` and `Real.rpow`. -/
def ClassicalABCNatShape : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ,
    0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ C * Real.rpow ((radical (a * b * c) : ℕ) : ℝ) (1 + ε)

theorem primitiveTriple_iff (a b c : ℕ) :
    IsABCTriple a b c ↔ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a + b = c := by
  unfold IsABCTriple PrimitiveAdditiveTriple
  constructor
  · rintro ⟨ha, hb, hsum, hcop⟩
    exact ⟨ha, hb, hcop, hsum⟩
  · rintro ⟨ha, hb, hcop, hsum⟩
    exact ⟨ha, hb, hsum, hcop⟩

/-- **The iff** (the main deliverable of A875). -/
theorem classicalABCNatShape_iff_ABCConjecture :
    ClassicalABCNatShape ↔ ABCConjecture := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
    intro a b c habc
    obtain ⟨ha, hb, hcop, hsum⟩ := (primitiveTriple_iff a b c).mp habc
    have hle := hC a b c ha hb hcop hsum
    have hX : 0 ≤ Real.rpow ((radical (a * b * c) : ℕ) : ℝ) (1 + ε) := by
      exact Real.rpow_nonneg (by positivity) _
    have hCK : C ≤ max C 1 := le_max_left C 1
    have hmono : C * Real.rpow ((radical (a * b * c) : ℕ) : ℝ) (1 + ε) ≤
        max C 1 * Real.rpow ((radical (a * b * c) : ℕ) : ℝ) (1 + ε) :=
      mul_le_mul_of_nonneg_right hCK hX
    exact le_trans hle hmono
  · intro h ε hε
    obtain ⟨K, hKpos, hK⟩ := h ε hε
    refine ⟨K, fun a b c ha hb hcop hsum => ?_⟩
    have habc : IsABCTriple a b c := (primitiveTriple_iff a b c).mpr ⟨ha, hb, hcop, hsum⟩
    exact hK a b c habc

def classicalABCRows : List (String × String × String) :=
  [ ("ClassicalABCNatShape", "lana ClassicalABC shape on our radical + rpow", "DEF") ,
    ("radShape", "factorization radical (lana radical dictionary candidate)", "DEF") ,
    ("primitiveTriple_iff", "IsABCTriple <-> 0<a,0<b,coprime,a+b=c", "PROVED") ,
    ("classicalABCNatShape_iff_ABCConjecture", "shape <-> ABCConjecture (C positivity via max C 1)", "PROVED") ,
    ("lana Iut.ClassicalABC = ClassicalABCNatShape", "one-line glue after lana oleans", "PENDING") ]

theorem classicalABCRows_length : classicalABCRows.length = 5 := rfl

-- 待 lana olean: Iut.ClassicalABC = ClassicalABCNatShape（defeq/iff，一行）

end LeanFormal.IUT.XiFPaper.Mzk1ClassicalABCBridgeActual
