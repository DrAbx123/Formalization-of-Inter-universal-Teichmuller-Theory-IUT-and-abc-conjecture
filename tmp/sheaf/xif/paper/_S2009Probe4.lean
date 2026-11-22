/-
S2009 probe 4: transitivity of the pair action.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open Matrix

namespace S2009Probe4

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev V2 := Fin 2 → K5

abbrev IsRep (v : V2) : Prop :=
  (v 0 = 1 ∨ v 0 = 2) ∨ (v 0 = 0 ∧ (v 1 = 1 ∨ v 1 = 2))

abbrev PairRep := {v : V2 // IsRep v}

def normSign (v : V2) : K5 :=
  if v 0 = 1 ∨ v 0 = 2 then 1
  else if v 0 = 3 ∨ v 0 = 4 then -1
  else if v 1 = 1 ∨ v 1 = 2 then 1
  else -1

def normalize (v : V2) : V2 := normSign v • v

theorem normalize_isRep : ∀ v : V2, v ≠ 0 → IsRep (normalize v) := by decide
theorem normalize_eq_or_neg : ∀ v : V2, normalize v = v ∨ normalize v = -v := by decide
theorem normalize_neg : ∀ v : V2, normalize (-v) = normalize v := by decide
theorem normalize_of_isRep : ∀ v : V2, IsRep v → normalize v = v := by decide
theorem isRep_ne_zero : ∀ v : V2, IsRep v → v ≠ 0 := by decide

theorem smul_eq_zero_iff (g : GL2) (v : V2) : g • v = 0 ↔ v = 0 := by
  constructor
  · intro h
    exact Matrix.eq_zero_of_mulVec_eq_zero (Matrix.GeneralLinearGroup.det_ne_zero g) h
  · intro h
    rw [h]
    simp

def pairAct (g : GL2) (x : PairRep) : PairRep :=
  ⟨normalize (g • x.1), normalize_isRep (g • x.1) (by
    intro h
    exact isRep_ne_zero x.1 x.2 ((smul_eq_zero_iff g x.1).mp h))⟩

theorem pairAct_one (x : PairRep) : pairAct 1 x = x := by
  apply Subtype.ext
  show normalize (1 • x.1) = x.1
  rw [one_smul, normalize_of_isRep x.1 x.2]

theorem normalize_smul_congr (g : GL2) {v w : V2} (h : w = v ∨ w = -v) :
    normalize (g • w) = normalize (g • v) := by
  rcases h with rfl | rfl
  · rfl
  · rw [show g • (-v) = -(g • v) by simp, normalize_neg]

theorem pairAct_mul (g h : GL2) (x : PairRep) :
    pairAct (g * h) x = pairAct g (pairAct h x) := by
  apply Subtype.ext
  show normalize ((g * h) • x.1) = normalize (g • normalize (h • x.1))
  rw [mul_smul]
  exact (normalize_smul_congr g (normalize_eq_or_neg (h • x.1))).symm

def toE0Matrix (v : V2) : Matrix (Fin 2) (Fin 2) K5 :=
  if h : v 0 = 0 then !![0, (v 1)⁻¹; -v 1, 0]
  else !![(v 0)⁻¹, 0; -v 1, v 0]

theorem toE0Matrix_det (v : V2) (hv : v ≠ 0) : (toE0Matrix v).det ≠ 0 := by
  unfold toE0Matrix
  split_ifs with h0
  · have hv1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    rw [Matrix.det_fin_two]
    simp [h0, hv1]
  · rw [Matrix.det_fin_two]
    simp [h0]

def toE0 (v : V2) (hv : v ≠ 0) : GL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (toE0Matrix v) (toE0Matrix_det v hv)

theorem toE0_val (v : V2) (hv : v ≠ 0) :
    ((toE0 v hv : GL2) : Matrix (Fin 2) (Fin 2) K5) = toE0Matrix v :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem toE0_smul (v : V2) (hv : v ≠ 0) : toE0 v hv • v = ![1, 0] := by
  ext i
  fin_cases i
  · show (toE0Matrix v *ᵥ v) 0 = (![1, 0] : V2) 0
    unfold toE0Matrix
    split_ifs with h0
    · have hv1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        funext j
        fin_cases j <;> simp [h0, h1]
      simp [Matrix.mulVec_fin_two, h0, inv_mul_cancel₀ hv1]
    · simp [Matrix.mulVec_fin_two, h0, inv_mul_cancel₀ h0]
  · show (toE0Matrix v *ᵥ v) 1 = (![1, 0] : V2) 1
    unfold toE0Matrix
    split_ifs with h0
    · simp [Matrix.mulVec_fin_two, h0]
    · simp [Matrix.mulVec_fin_two, h0]

theorem exists_smul_eq (v w : V2) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : GL2, g • v = w := by
  refine ⟨(toE0 w hw)⁻¹ * toE0 v hv, ?_⟩
  rw [mul_smul, toE0_smul v hv]
  have h := toE0_smul w hw
  rw [← h]
  rw [← mul_smul, inv_mul_cancel, one_smul]

theorem pairAct_transitive (x y : PairRep) : ∃ g : GL2, pairAct g x = y := by
  obtain ⟨g, hg⟩ := exists_smul_eq x.1 y.1 (isRep_ne_zero x.1 x.2) (isRep_ne_zero y.1 y.2)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  show normalize (g • x.1) = y.1
  rw [hg, normalize_of_isRep y.1 y.2]

def pairEquiv (g : GL2) : PairRep ≃ PairRep where
  toFun := pairAct g
  invFun := pairAct g⁻¹
  left_inv x := by
    rw [← pairAct_mul, inv_mul_cancel, pairAct_one]
  right_inv x := by
    rw [← pairAct_mul, mul_inv_cancel, pairAct_one]

def pairPermHom : GL2 →* Equiv.Perm PairRep where
  toFun g := pairEquiv g
  map_one' := by
    apply Equiv.ext
    intro x
    exact pairAct_one x
  map_mul' g h := by
    apply Equiv.ext
    intro x
    exact pairAct_mul g h x

end S2009Probe4