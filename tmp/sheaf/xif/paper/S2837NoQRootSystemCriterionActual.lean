import tmp.sheaf.xif.paper.S2836UniformizerNoRootSystemActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2837NoQRootSystemCriterionActual

variable {K : Type*} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}

/-- The unit attached to a finite-place q candidate. -/
noncomputable def S2837QUnit (q : FinitePlaceQCandidate place) : (Completion place)ˣ :=
  Units.mk0 q.q q.q_ne_zero

/-- Criterion: if every natural n divides the exponent of q, then no
NatRootSystem exists for the associated completion unit. -/
theorem S2837_no_NatRootSystem_of_forall_dvd
    (q : FinitePlaceQCandidate place)
    (h : forall n : Nat, 0 < n -> (n : Int) ∣ q.exponent) :
    ¬ Nonempty (NatRootSystem (S2837QUnit q)) := by
  rintro ⟨R⟩
  have hpos : 0 < q.exponent := q.exponent_pos
  have hdvd := h (q.order + 1) (Nat.succ_pos _)
  have horder : (q.order : Int) = q.exponent := by
    rw [FinitePlaceQCandidate.order]
    exact Int.toNat_of_nonneg (le_of_lt hpos)
  -- rewrite the divisibility in terms of order
  rw [← horder] at hdvd
  have hposn : 0 < q.order := q.order_pos
  -- (order + 1) divides order, impossible
  have hdvdNat : (q.order + 1) ∣ q.order := by
    exact_mod_cast hdvd
  exact Nat.not_dvd_of_pos_of_lt hposn (Nat.lt_succ_self q.order) hdvdNat

/-- Exact remaining valuation input: a NatRootSystem forces every n to divide
the q exponent.  Stated as a Prop; not proved here. -/
def S2837RootSystemImpliesDvd (q : FinitePlaceQCandidate place) : Prop :=
  Nonempty (NatRootSystem (S2837QUnit q)) ->
    forall n : Nat, (n : Int) ∣ q.exponent

/-- Conditional no-go: the valuation input plus the criterion rules out any
NatRootSystem for a q candidate. -/
theorem S2837_no_NatRootSystem_of_rootSystemImpliesDvd
    (q : FinitePlaceQCandidate place)
    (h : S2837RootSystemImpliesDvd q) :
    ¬ Nonempty (NatRootSystem (S2837QUnit q)) := by
  intro hr
  exact (S2837_no_NatRootSystem_of_forall_dvd q (fun n _ => h hr n)) hr

private lemma S2837_log_eq_toAdd_unzero
    {x : WithZero (Multiplicative Int)} (hx : x ≠ 0) :
    WithZero.log x = (WithZero.unzero hx).toAdd := by
  apply WithZero.exp_injective
  rw [WithZero.exp_log hx, WithZero.exp_eq_coe_ofAdd]
  exact (WithZero.coe_unzero hx).symm

/-- Valuation divisibility: a NatRootSystem forces every positive n to divide
the q exponent. -/
theorem S2837_rootSystem_implies_dvd
    (q : FinitePlaceQCandidate place)
    (R : NatRootSystem (S2837QUnit q)) (n : Nat) (hn : 0 < n) :
    (n : Int) ∣ q.exponent := by
  let u : (Completion place)ˣ := R.root n
  have hu : ((u : (Completion place)ˣ) : Completion place) ^ n = q.q := by
    have h := R.pow_self n hn.ne'
    have hcoe := congrArg (fun x : (Completion place)ˣ => (x : Completion place)) h
    simpa [u, S2837QUnit] using hcoe
  have hqne : Valued.v q.q ≠ 0 := by
    intro h
    exact q.q_ne_zero ((Valued.v).map_eq_zero_iff.mp h)
  have hlogq : WithZero.log (Valued.v q.q) = -q.exponent := by
    unfold FinitePlaceQCandidate.exponent
    rw [S2837_log_eq_toAdd_unzero q.valuation_ne_zero]
    simp
  have hvq : Valued.v q.q = WithZero.exp (-q.exponent) := by
    rw [← WithZero.exp_log hqne, hlogq]
  let x : WithZero (Multiplicative Int) :=
    Valued.v ((u : (Completion place)ˣ) : Completion place)
  have hxne : x ≠ 0 := by
    intro hx0
    have hzero : ((u : (Completion place)ˣ) : Completion place) = 0 :=
      (Valued.v).map_eq_zero_iff.mp hx0
    exact Units.ne_zero u hzero
  have hval : x ^ n = WithZero.exp (-q.exponent) := by
    rw [← map_pow]
    rw [hu]
    exact hvq
  have hvlog : WithZero.exp ((n : Int) • WithZero.log x) =
      WithZero.exp (-q.exponent) := by
    rw [WithZero.exp_zsmul]
    rw [zpow_natCast, ← hval]
    rw [WithZero.exp_log hxne]
  have hlogeq : (n : Int) • WithZero.log x = -q.exponent :=
    WithZero.exp_injective hvlog
  refine ⟨-WithZero.log x, ?_⟩
  rw [zsmul_eq_mul] at hlogeq
  have h := congrArg Neg.neg hlogeq
  have h' : (n : Int) * -WithZero.log x = q.exponent := by
    rw [mul_neg]
    simpa using h
  exact h'.symm

/-- Unconditional no-go: no finite-place q candidate has a NatRootSystem in the
completion. -/
theorem S2837_no_NatRootSystem
    (q : FinitePlaceQCandidate place) :
    ¬ Nonempty (NatRootSystem (S2837QUnit q)) := by
  rintro ⟨R⟩
  exact S2837_no_NatRootSystem_of_forall_dvd q
    (fun n hn => S2837_rootSystem_implies_dvd q R n hn) ⟨R⟩

#check S2837QUnit
#check S2837_no_NatRootSystem_of_forall_dvd
#check S2837RootSystemImpliesDvd
#check S2837_no_NatRootSystem_of_rootSystemImpliesDvd
#check S2837_no_NatRootSystem
#print axioms S2837_no_NatRootSystem

end LeanFormal.IUT.XiFPaper.S2837NoQRootSystemCriterionActual
end
