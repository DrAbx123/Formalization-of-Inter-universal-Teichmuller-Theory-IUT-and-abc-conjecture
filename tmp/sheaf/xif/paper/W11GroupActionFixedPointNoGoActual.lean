import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# W11: the mu_{2l} group action, fixed points, Lefschetz, and the log

Task W11 proposed using the finite group action of mu_{2l} on a compact
hull/space to produce a fixed point or invariant representative, hence
eliminating the root ambiguity and proving that the log is invariant.

## Verdict

REFUSE the fixed-point / Lefschetz / Borsuk-Ulam route.

The actual action of the nontrivial generator of mu_{2l} on the root stack is
free: it has no fixed point at all.  On the ambient field L, its fixed set is
exactly {0}; the root is nonzero, so the fixed point is not a representative
of the root.  The equal-weight orbit sum is also 0 (the finite geometric sum),
so the averaging representative is again 0, not a root.  The genuine
Lefschetz/trace computation on the finite regular fiber gives
L(a) = 2l for a = 0 and L(a) = 0 for a != 0; in particular no nontrivial group
element has a fixed point or a nonzero Lefschetz number.

The log invariance is true, but it is a metric fact: roots of unity have norm
one, so ||zeta * r|| = ||r||, and r^(2l) = q gives
log ||r|| = (1/(2l)) log ||q||.  This is not a topological theorem.  W8
already proves that no homeomorphism-invariant functional of the p-adic region
can equal the log.  The only genuine topological input in this neighbourhood
is the fixed-point/Lefschetz computation, and it yields zero.

No target is changed, no paper inequality is asserted, and no fake carrier is
introduced.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.W11GroupActionFixedPointNoGoActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The actual generator and its fixed points -/

/-- The primitive 2l-th root of unity used by S782 is primitive. -/
theorem stackMuRoot_isPrimitiveRoot :
    IsPrimitiveRoot
      (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
        rootNormedAmbient T b)) (2 * l.value) := by
  unfold stackMuRoot
  rw [Units.val_mk0]
  exact Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot (rootNormedAmbient T b) (2 * l.value))

/-- 2l > 1, so the primitive root is not one. -/
theorem twoL_gt_one : 1 < 2 * l.value := by
  have h : 5 ≤ l.value := l.ge_five
  omega

/-- The S782 generator is a nontrivial unit of the finite root stack. -/
theorem stackMuUnit_ne_one : stackMuUnit (l := l) T b ≠ 1 := by
  intro h
  have hval : ((stackMuUnit (l := l) T b : rootStackExtension T b)) = 1 := by
    rw [h]
    rfl
  have hroot : ((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
      rootNormedAmbient T b) = 1 := by
    have h' := congrArg (fun x : rootStackExtension T b =>
      (x : rootNormedAmbient T b)) hval
    simpa [stackMuUnit] using h'
  exact (stackMuRoot_isPrimitiveRoot (l := l) T b).ne_one twoL_gt_one hroot

/-- The generator as an element of the finite root stack. -/
noncomputable def stackMuElem : rootStackExtension T b :=
  ((stackMuUnit (l := l) T b : (rootStackExtension T b)ˣ) :
    rootStackExtension T b)

theorem stackMuElem_ne_one : stackMuElem (l := l) T b ≠ 1 := by
  intro h
  apply stackMuUnit_ne_one (l := l) T b
  apply Units.ext
  rw [Units.val_one]
  exact h

theorem stackMuElem_ne_zero : stackMuElem (l := l) T b ≠ 0 := by
  simpa [stackMuElem] using Units.ne_zero (stackMuUnit (l := l) T b)

/-- Multiplication by the nontrivial generator has no fixed point in the unit
group of the finite root stack. -/
theorem stackMuUnit_mul_ne_self (u : (rootStackExtension T b)ˣ) :
    stackMuUnit (l := l) T b * u ≠ u := by
  intro h
  apply stackMuUnit_ne_one (l := l) T b
  have h' := congrArg (fun x : (rootStackExtension T b)ˣ => x * u⁻¹) h
  simpa [mul_assoc] using h'

/-- The S782 action on the root-stack carrier has no fixed point. -/
theorem stackMuAction_no_fixed (u : StackSectionCarrier T b) :
    stackMuAction (l := l) T b u ≠ u := by
  intro h
  have hfst : stackMuUnit (l := l) T b * u.1 = u.1 := by
    simpa [stackMuAction] using congrArg Prod.fst h
  exact stackMuUnit_mul_ne_self (l := l) T b u.1 hfst

/-- On the ambient field, the only fixed point of the generator is zero. -/
theorem stackMuElem_mul_eq_self_iff (x : rootStackExtension T b) :
    stackMuElem (l := l) T b * x = x ↔ x = 0 := by
  constructor
  · intro h
    have hsub : (stackMuElem (l := l) T b - 1) * x = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    have hne : (stackMuElem (l := l) T b - 1) ≠ 0 :=
      sub_ne_zero.mpr (stackMuElem_ne_one (l := l) T b)
    exact (mul_eq_zero.mp hsub).resolve_left hne
  · intro h
    rw [h, mul_zero]

/-- Exact fixed set of the actual nontrivial generator on the root stack: it
is the singleton {0}. -/
theorem stackMuElem_fixedPoints_eq_singleton :
    {x : rootStackExtension T b | stackMuElem (l := l) T b * x = x} = {0} := by
  ext x
  exact stackMuElem_mul_eq_self_iff (l := l) T b x

/-- The S782 root section as a unit of the root-stack extension. -/
noncomputable def stackRootUnit : (rootStackExtension T b)ˣ :=
  (stackRootSection (l := l) T b).1

/-- The S782 q section as a unit of the root-stack extension. -/
noncomputable def stackQUnit : (rootStackExtension T b)ˣ :=
  (stackQSection (l := l) T b).1

theorem stackRootUnit_pow :
    stackRootUnit (l := l) T b ^ (2 * l.value) = stackQUnit (l := l) T b :=
  congrArg Prod.fst (stackRootSection_pow (l := l) T b)

theorem stackRootUnit_ne_zero :
    ((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
      rootStackExtension T b) ≠ 0 :=
  Units.ne_zero (stackRootUnit (l := l) T b)

/-- The actual root is not fixed by the nontrivial generator: the only fixed
point is 0, and the root is nonzero. -/
theorem stackRootUnit_not_fixed :
    stackMuElem (l := l) T b *
        ((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          rootStackExtension T b) ≠
      ((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b) := by
  intro h
  exact stackRootUnit_ne_zero (l := l) T b
    ((stackMuElem_mul_eq_self_iff (l := l) T b _).mp h)

/-! ## 2. The finite Lefschetz/trace computation

The genuine fixed-point/Lefschetz computation in this problem is on the
finite regular fiber mu_{2l}.  Its Lefschetz number is the trace of the
permutation matrix.  It is 2l at the identity and zero at every nontrivial
element. -/

/-- The order of the finite root-stack group mu_{2l}. -/
def w11RootStackIndex (l : PrimeGeFive) : Nat := 2 * l.value

theorem w11RootStackIndex_pos (l : PrimeGeFive) : 0 < w11RootStackIndex l := by
  unfold w11RootStackIndex
  exact Nat.mul_pos (by norm_num) l.prime.pos

instance w11RootStackIndexNeZero (l : PrimeGeFive) :
    NeZero (w11RootStackIndex l) :=
  ⟨Nat.ne_of_gt (w11RootStackIndex_pos l)⟩

/-- Translation by a on the finite group mu_{2l}, as a permutation. -/
noncomputable def w11RegularPerm
    (a : ZMod (w11RootStackIndex l)) :
    Equiv.Perm (ZMod (w11RootStackIndex l)) where
  toFun x := a + x
  invFun x := -a + x
  left_inv x := by simp
  right_inv x := by simp

theorem w11_fixedPoints (a : ZMod (w11RootStackIndex l)) :
    Function.fixedPoints (w11RegularPerm (l := l) a) =
      if a = 0 then (Set.univ : Set (ZMod (w11RootStackIndex l))) else ∅ := by
  by_cases ha : a = 0
  · ext x
    simp [Function.mem_fixedPoints, w11RegularPerm, ha, Function.IsFixedPt]
  · ext x
    simp only [Function.mem_fixedPoints, w11RegularPerm, ha, if_false,
      Set.mem_empty_iff_false]
    constructor
    · intro h
      have h' : a + x = (0 : ZMod (w11RootStackIndex l)) + x := by
        rw [zero_add]
        exact h
      exact ha (add_right_cancel h')
    · intro h
      exact False.elim h

/-- The Lefschetz number of the regular action at a group element is the
permutation trace, i.e. the fixed-point count. -/
theorem w11_matrixTrace (a : ZMod (w11RootStackIndex l)) :
    Matrix.trace ((w11RegularPerm (l := l) a).permMatrix ℝ) =
      if a = 0 then (w11RootStackIndex l : ℝ) else 0 := by
  rw [Matrix.trace_permutation, w11_fixedPoints]
  by_cases ha : a = 0
  · simp [ha, Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
  · simp [ha]

/-- Every nontrivial group element has Lefschetz number zero. -/
theorem lefschetzNumber_nontrivial_eq_zero
    (a : ZMod (w11RootStackIndex l)) (ha : a ≠ 0) :
    Matrix.trace ((w11RegularPerm (l := l) a).permMatrix ℝ) = 0 := by
  rw [w11_matrixTrace (l := l) a]
  simp [ha]

/-- Every nontrivial group element has empty fixed set. -/
theorem fixedPoints_nontrivial_eq_empty
    (a : ZMod (w11RootStackIndex l)) (ha : a ≠ 0) :
    Function.fixedPoints (w11RegularPerm (l := l) a) = ∅ := by
  rw [w11_fixedPoints (l := l) a]
  simp [ha]

/-- The identity has fixed set the whole fiber. -/
theorem fixedPoints_identity :
    Function.fixedPoints (w11RegularPerm (l := l) 0) =
      (Set.univ : Set (ZMod (w11RootStackIndex l))) := by
  rw [w11_fixedPoints (l := l) 0]
  simp

/-! ## 3. Averaging the actual root orbit

The equal-weight algebraic average of the mu_{2l}-orbit is zero.  This is the
finite geometric-sum identity, not a topological average.  In particular the
averaging representative is not the root. -/

/-- The finite geometric sum with a primitive n-th root vanishes. -/
theorem geom_sum_mul_eq_zero {K : Type*} [Field K] {ζ r : K} {n : Nat}
    (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) :
    (∑ k ∈ Finset.range n, ζ ^ k * r) = 0 := by
  rw [← Finset.sum_mul, IsPrimitiveRoot.geom_sum_eq_zero hζ hn, zero_mul]

/-- The primitive generator as an element of the ambient field. -/
noncomputable def rootMuElem : rootNormedAmbient T b :=
  ((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
    rootNormedAmbient T b)

theorem rootMuElem_isPrimitiveRoot :
    IsPrimitiveRoot (rootMuElem (l := l) T b) (2 * l.value) :=
  stackMuRoot_isPrimitiveRoot (l := l) T b

/-- The sum of the full mu_{2l}-orbit of the actual root is zero. -/
theorem rootOrbitSum_eq_zero :
    (∑ k ∈ Finset.range (2 * l.value),
      (rootMuElem (l := l) T b) ^ k * rootNormedElement T b) = 0 :=
  geom_sum_mul_eq_zero (rootMuElem_isPrimitiveRoot (l := l) T b) twoL_gt_one

/-- The equal-weight algebraic average of the orbit is zero. -/
theorem rootOrbitAverage_eq_zero :
    (((2 * l.value : Nat) : rootNormedAmbient T b))⁻¹ *
      (∑ k ∈ Finset.range (2 * l.value),
        (rootMuElem (l := l) T b) ^ k * rootNormedElement T b) = 0 := by
  rw [rootOrbitSum_eq_zero (l := l) T b, mul_zero]

/-- The ambient root is nonzero (the root is a unit). -/
theorem rootNormedElement_ne_zero : rootNormedElement T b ≠ 0 := by
  intro h
  have hpow := rootNormedElement_pow T b
  rw [h, zero_pow (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)] at hpow
  have hq : ((unitToAlgClosed (sourceRootQUnit T b) :
      (rootNormedAmbient T b)ˣ) : rootNormedAmbient T b) ≠ 0 :=
    Units.ne_zero (unitToAlgClosed (sourceRootQUnit T b))
  exact hq hpow.symm

/-- The averaging representative is zero, so it is not the root. -/
theorem rootOrbitAverage_ne_root :
    (((2 * l.value : Nat) : rootNormedAmbient T b))⁻¹ *
        (∑ k ∈ Finset.range (2 * l.value),
          (rootMuElem (l := l) T b) ^ k * rootNormedElement T b) ≠
      rootNormedElement T b := by
  rw [rootOrbitAverage_eq_zero (l := l) T b]
  exact (rootNormedElement_ne_zero (l := l) T b).symm

/-! ## 4. The invariant log: a metric fact, not a topological theorem -/

/-- A finite-order element of a normed field has norm one. -/
theorem norm_eq_one_of_pow_eq_one {K : Type*} [NormedField K] {ζ : K} {n : Nat}
    (hn : 0 < n) (hζ : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have hpow : ‖ζ‖ ^ n = 1 := by
    rw [← norm_pow, hζ, norm_one]
  exact pow_left_inj₀ (norm_nonneg ζ) zero_le_one hn.ne' |>.mp (by
    simpa using hpow)

/-- Pointwise log invariance: multiplying the root by a 2l-th root of unity
does not change its log-norm. -/
theorem rootLog_branch_independent {ζ : rootNormedAmbient T b}
    (hζ : ζ ^ (2 * l.value) = 1) :
    Real.log ‖ζ * rootNormedElement T b‖ =
      Real.log ‖rootNormedElement T b‖ := by
  have hζnorm : ‖ζ‖ = 1 :=
    norm_eq_one_of_pow_eq_one
      (Nat.mul_pos (by norm_num) l.prime.pos) hζ
  rw [norm_mul, hζnorm, one_mul]

/-- The actual root log is (1/(2l)) times the q log.  This is the genuine
q[2u] normalization; it uses only r^(2l) = q and multiplicativity of the
norm. -/
theorem rootLog_eq_inv_card_mul_qLog :
    Real.log ‖rootNormedElement T b‖ =
      (1 / (2 * (l.value : Real))) *
        Real.log ‖(unitToAlgClosed (sourceRootQUnit T b) :
          rootNormedAmbient T b)‖ := by
  have hpow : ‖rootNormedElement T b‖ ^ (2 * l.value) =
      ‖(unitToAlgClosed (sourceRootQUnit T b) :
        rootNormedAmbient T b)‖ := by
    have h := congrArg (fun x : rootNormedAmbient T b => ‖x‖)
      (rootNormedElement_pow T b)
    rw [norm_pow] at h
    exact h
  have hlog := congrArg Real.log hpow
  rw [Real.log_pow] at hlog
  have hcast : ((2 * l.value : Nat) : Real) = 2 * (l.value : Real) := by
    push_cast
    ring
  rw [hcast] at hlog
  have h2l : (2 * (l.value : Real)) ≠ 0 := by
    have := l.prime.ne_zero
    positivity
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  calc
    Real.log ‖rootNormedElement T b‖ =
        (1 / (2 * (l.value : Real))) *
          ((2 * (l.value : Real)) * Real.log ‖rootNormedElement T b‖) := by
      field_simp [h2l, hl]
    _ = (1 / (2 * (l.value : Real))) *
        Real.log ‖(unitToAlgClosed (sourceRootQUnit T b) :
          rootNormedAmbient T b)‖ := by
      rw [hlog]

/-- The same log identity on the actual stack-root unit. -/
theorem stackRootLog_eq_inv_card_mul_qLog :
    Real.log ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b)‖ =
      (1 / (2 * (l.value : Real))) *
        Real.log ‖((stackQUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          rootStackExtension T b)‖ := by
  have hpow : ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
      rootStackExtension T b)‖ ^ (2 * l.value) =
      ‖((stackQUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b)‖ := by
    have h := congrArg (fun x : (rootStackExtension T b)ˣ =>
      ‖(x : rootStackExtension T b)‖) (stackRootUnit_pow (l := l) T b)
    rw [Units.val_pow_eq_pow_val, norm_pow] at h
    exact h
  have hlog := congrArg Real.log hpow
  rw [Real.log_pow] at hlog
  have hcast : ((2 * l.value : Nat) : Real) = 2 * (l.value : Real) := by
    push_cast
    ring
  rw [hcast] at hlog
  have h2l : (2 * (l.value : Real)) ≠ 0 := by
    have := l.prime.ne_zero
    positivity
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  calc
    Real.log ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b)‖ =
        (1 / (2 * (l.value : Real))) *
          ((2 * (l.value : Real)) *
            Real.log ‖((stackRootUnit (l := l) T b :
              (rootStackExtension T b)ˣ) : rootStackExtension T b)‖) := by
      field_simp [h2l, hl]
    _ = (1 / (2 * (l.value : Real))) *
        Real.log ‖((stackQUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          rootStackExtension T b)‖ := by
      rw [hlog]

/-- Branch independence on the actual stack-root unit: multiplying by any
norm-one unit does not change the log. -/
theorem stackRootLog_branch_independent
    (ζ : (rootStackExtension T b)ˣ)
    (hζ : ‖(ζ : rootStackExtension T b)‖ = 1) :
    Real.log ‖(((ζ * stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b))‖ =
      Real.log ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b)‖ := by
  rw [Units.val_mul, norm_mul, hζ, one_mul]

/-! ## 5. Summary no-go -/

/-- No fixed point of the actual nontrivial mu_{2l} generator is a root. -/
theorem no_fixed_point_is_root :
    ∀ x : rootStackExtension T b,
      stackMuElem (l := l) T b * x = x →
        x ≠ ((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          rootStackExtension T b) := by
  intro x hx hxroot
  have hx0 : x = 0 := (stackMuElem_mul_eq_self_iff (l := l) T b x).mp hx
  rw [hx0] at hxroot
  exact stackRootUnit_ne_zero (l := l) T b hxroot.symm

/-- The fixed set of the actual generator is {0}, and the root is outside it. -/
theorem fixedSet_eq_singleton_and_root_not_mem :
    {x : rootStackExtension T b | stackMuElem (l := l) T b * x = x} = {0} ∧
      ((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b) ∉
        {x : rootStackExtension T b | stackMuElem (l := l) T b * x = x} := by
  constructor
  · exact stackMuElem_fixedPoints_eq_singleton (l := l) T b
  · rw [stackMuElem_fixedPoints_eq_singleton (l := l) T b]
    simp [stackRootUnit_ne_zero (l := l) T b]

#print axioms stackMuUnit_ne_one
#print axioms stackMuAction_no_fixed
#print axioms stackMuElem_fixedPoints_eq_singleton
#print axioms lefschetzNumber_nontrivial_eq_zero
#print axioms rootOrbitAverage_eq_zero
#print axioms rootOrbitAverage_ne_root
#print axioms rootLog_eq_inv_card_mul_qLog
#print axioms stackRootLog_eq_inv_card_mul_qLog
#print axioms no_fixed_point_is_root

end LeanFormal.IUT.XiFPaper.W11GroupActionFixedPointNoGoActual

end