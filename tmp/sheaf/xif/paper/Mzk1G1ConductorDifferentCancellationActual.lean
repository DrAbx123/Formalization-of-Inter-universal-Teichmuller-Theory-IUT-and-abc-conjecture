/- H-T 8.2 (first batch): the conductor / arithmetic-different cancellation interface, based on
sophie's 8.1 interface Mzk1HT81InterfaceActual.HT81Interface, and the discriminant tower formula
specialization (rings of integers). -/
import tmp.sheaf.xif.paper.Mzk1HT81InterfaceActual
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual

universe u

/-- The normalized log-discriminant D(K) = log |disc K| / [K : Q] (route F2, K-end). -/
def normalizedLogDisc (K : Type u) [Field K] [NumberField K] : ℝ :=
  Real.log ((discr K).natAbs : ℝ) / (Module.finrank ℚ K : ℝ)

/-- The conductor / arithmetic-different quantities for one selected morphism phi_i, over
sophie's 8.1 interface (E_i, phi_i, y, K_i, L).

conductorAtD = N_D(phi_i(y)), conductorAtE = N_{E_i}(y), heightE = h_{E_i}(y),
constant = C_i (independent of y).  These are the 8.1/8.2 quantities; **NO INHABITANT is
provided at this stage**: the actual values come from the 8.1 construction. -/
structure ConductorDifferentData (H : HT81Interface) (i : H.I) where
  /-- N_D(phi_i(y)): normalized truncated conductor at D -/
  conductorAtD : ℝ
  /-- N_{E_i}(y): normalized truncated conductor at E_i -/
  conductorAtE : ℝ
  /-- h_{E_i}(y): height of y relative to O(E_i) -/
  heightE : ℝ
  /-- C_i: fixed constant (independent of y) -/
  constant : ℝ

/-- Route F2: D(K_i) + N_D(phi_i(y)) <= D(L) + N_{E_i}(y) + C_i. -/
def F2 (H : HT81Interface) (i : H.I) (A : ConductorDifferentData H i) : Prop :=
  normalizedLogDisc (H.K i) + A.conductorAtD <=
    normalizedLogDisc H.L + A.conductorAtE + A.constant

/-- Route F3: N_{E_i}(y) <= h_{E_i}(y) + C_i. -/
def F3 (H : HT81Interface) (i : H.I) (A : ConductorDifferentData H i) : Prop :=
  A.conductorAtE <= A.heightE + A.constant

/-- F2 + F3 give the conductor/different cancellation bound:
D(K_i) + N_D(phi_i(y)) <= D(L) + h_{E_i}(y) + 2 C_i. -/
theorem f2_f3_cancellation (H : HT81Interface) (i : H.I) (A : ConductorDifferentData H i)
    (h2 : F2 H i A) (h3 : F3 H i A) :
    normalizedLogDisc (H.K i) + A.conductorAtD <=
      normalizedLogDisc H.L + A.heightE + 2 * A.constant := by
  unfold F2 at h2
  unfold F3 at h3
  linarith

/-! ## Discriminant tower formula (route 8.2, discriminant tower step) -/

/-- Discriminant tower formula: |disc L| = |N(different(O_K,O_L))| * |disc K|^[L:K].
This is the actual inequality source for the conductor/different cancellation (F2). -/
theorem discriminant_tower_formula_ringOfIntegers
    {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]
    [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)] :
    (discr L).natAbs =
      Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) * (discr K).natAbs ^ Module.finrank K L :=
  natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (K := K) (𝒪 := 𝓞 K) (L := L)
    (𝒪' := 𝓞 L)

#print axioms f2_f3_cancellation
#print axioms discriminant_tower_formula_ringOfIntegers
end LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual

