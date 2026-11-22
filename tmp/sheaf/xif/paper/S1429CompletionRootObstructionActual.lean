import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
# S1429: completion-root obstruction

S1314/S1341 record that the old C3 SourcePilotRegionData schema asks for

  roots : NatRootSystem (candidateUnits place q)

where candidateUnits place q is the q-candidate itself regarded as a unit of
the completion.  This file proves that this completion root system cannot exist,
for any q-candidate, and therefore records the exact first missing field as an
impossible field rather than fabricating a root or replacing the completion by
its algebraic closure.

The proof is valuation-theoretic.  The q-candidate has nonzero valuation
v(q) = exp(-e) with e = q.exponent > 0.  A NatRootSystem would contain an
n-th root for every natural n; taking n = e + 1 gives a unit r with
r ^ n = q.  Applying v and WithZero.log yields

  n * log v(r) = -e,

so n divides e, which is impossible because n = e + 1 > e > 0.
-/

noncomputable section
set_option autoImplicit false

namespace LeanFormal.IUT.XiFPaper.S1429CompletionRootObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- The completion-unit root-system carrier attached to a q-candidate. -/
abbrev CompletionRootCarrier (q : FinitePlaceQCandidate place.val) : Type u :=
  NatRootSystem (candidateUnits place q)

/-- The exact completion-root obstruction: the missing first field of the old
C3 completion schema, stated as an existence proposition. -/
def CompletionRootObstruction (q : FinitePlaceQCandidate place.val) : Prop :=
  Nonempty (CompletionRootCarrier place q)

/-- The obstruction is definitionally the missing completion root system. -/
theorem completionRootObstruction_iff (q : FinitePlaceQCandidate place.val) :
    CompletionRootObstruction place q ↔
      Nonempty (NatRootSystem (candidateUnits place q)) :=
  Iff.rfl

/-- No q-candidate in a number-field completion admits a compatible root system
in the completion itself.  This is an actual no-go theorem, not a missing-field
record. -/
theorem no_completionRootSystem (q : FinitePlaceQCandidate place.val) :
    ¬ Nonempty (CompletionRootCarrier place q) := by
  rintro ⟨r⟩
  let e : Nat := q.order
  have he_pos : 0 < e := q.order_pos
  have he_int : (e : Int) = q.exponent := by
    rw [show e = q.order from rfl, FinitePlaceQCandidate.order,
      Int.toNat_of_nonneg (le_of_lt q.exponent_pos)]
  let n : Nat := e + 1
  have hn : n ≠ 0 := Nat.succ_ne_zero e
  have hpow : r.root n ^ n = candidateUnits place q :=
    NatRootSystem.pow_self r n hn
  let u : Units (Completion place.val) :=
    (r.root n : Units (Completion place.val))
  let uq : Units (Completion place.val) :=
    (candidateUnits place q : Units (Completion place.val))
  have hpow' : u ^ n = uq := hpow
  have hcoe :
      (Units.val u : Completion place.val) ^ n =
        (Units.val uq : Completion place.val) := by
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun w : Units (Completion place.val) => Units.val w) hpow'
  have hval :
      ((Valued.v (Units.val u) : WithZero (Multiplicative Int))) ^ n =
        ((Valued.v (Units.val uq) : WithZero (Multiplicative Int))) := by
    simpa using congrArg
      (fun x : Completion place.val =>
        (Valued.v x : WithZero (Multiplicative Int))) hcoe
  have huq : Units.val uq = (q.q : Completion place.val) := rfl
  have hq_ne :
      ((Valued.v (Units.val uq) : WithZero (Multiplicative Int))) ≠ 0 := by
    rw [huq]
    exact q.valuation_ne_zero
  have hroot_ne :
      ((Valued.v (Units.val u) : WithZero (Multiplicative Int))) ≠ 0 := by
    intro hzero
    have hzero_pow :
        ((Valued.v (Units.val u) : WithZero (Multiplicative Int))) ^ n = 0 := by
      rw [hzero, zero_pow hn]
    rw [hval] at hzero_pow
    exact hq_ne hzero_pow
  let a : Int :=
    WithZero.log ((Valued.v (Units.val u) :
      WithZero (Multiplicative Int)))
  have hvroot_exp :
      ((Valued.v (Units.val u) : WithZero (Multiplicative Int))) =
        WithZero.exp a := by
    rw [← WithZero.exp_log hroot_ne]
  have h_unzero :
      Multiplicative.toAdd
        (WithZero.unzero q.valuation_ne_zero) = -(e : Int) := by
    have hqexp : q.exponent =
        -Multiplicative.toAdd
          (WithZero.unzero q.valuation_ne_zero) := rfl
    omega
  have hvq_exp :
      ((Valued.v (q.q : Completion place.val)) :
        WithZero (Multiplicative Int)) = WithZero.exp (-(e : Int)) := by
    calc
      ((Valued.v (q.q : Completion place.val)) :
          WithZero (Multiplicative Int)) =
          ↑(WithZero.unzero q.valuation_ne_zero) :=
            (WithZero.coe_unzero q.valuation_ne_zero).symm
      _ = WithZero.exp
            (Multiplicative.toAdd
              (WithZero.unzero q.valuation_ne_zero)) := rfl
      _ = WithZero.exp (-(e : Int)) := by rw [h_unzero]
  have h_exp :
      (WithZero.exp a) ^ n =
        WithZero.exp (-(e : Int)) := by
    rw [← hvroot_exp, ← hvq_exp, ← huq]
    exact hval
  have h_int : (n : Int) * a = -(e : Int) := by
    have h1 : WithZero.exp ((n : Int) * a) =
        WithZero.exp (-(e : Int)) := by
      rw [← nsmul_eq_mul]
      rw [WithZero.exp_nsmul]
      exact h_exp
    exact WithZero.exp_injective h1
  have hn_pos : (0 : Int) < (n : Int) := by
    exact_mod_cast Nat.succ_pos e
  have he_pos_int : (0 : Int) < (e : Int) := by
    exact_mod_cast he_pos
  have ha_neg : a < 0 := by
    nlinarith [h_int, hn_pos, he_pos_int]
  have hc : (1 : Int) ≤ -a := by omega
  have hmain : (e : Int) = (n : Int) * (-a) := by
    nlinarith [h_int]
  have hmul : (n : Int) * 1 ≤ (n : Int) * (-a) :=
    mul_le_mul_of_nonneg_left hc (le_of_lt hn_pos)
  have hge : (e : Int) ≥ (n : Int) := by
    rw [hmain]
    simpa using hmul
  have hn_eq : (n : Int) = (e : Int) + 1 := by
    simp [n]
  omega

/-- The exact first field is not merely missing: its type is empty, for every
q-candidate. -/
theorem completionRootObstruction_holds (q : FinitePlaceQCandidate place.val) :
    ¬ CompletionRootObstruction place q :=
  no_completionRootSystem place q

/-- The old C3 completion schema is uninhabited: its roots field asks for a
completion root system of the q-candidate, which the no-go theorem forbids. -/
theorem sourcePilotRegionData_isEmpty
    {l : PrimeGeFive} {V : Type u} (I : OriginalInput l V) :
    IsEmpty (SourcePilotRegionData I) := by
  refine ⟨fun D => ?_⟩
  have hroots : Nonempty (NatRootSystem (candidateUnits D.place D.q)) :=
    ⟨Eq.ndrec (motive := fun x => NatRootSystem x) D.roots D.qUnit_eq⟩
  exact no_completionRootSystem D.place D.q hroots

end LeanFormal.IUT.XiFPaper.S1429CompletionRootObstructionActual
