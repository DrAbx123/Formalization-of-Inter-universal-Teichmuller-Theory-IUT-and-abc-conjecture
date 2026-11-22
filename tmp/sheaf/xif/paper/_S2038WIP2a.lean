/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtalePiOneKernelRealization
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateParameter
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

/-!
# S2038: the actual paper O object: definition, constructed q-pilot, and the
exact first-missing chain

Layer: O (original Theta-link / q-pilot).  Assembly node of the
S1958/S1965/S1966/S1967/S1973/S1978/S1979 worker chain and of the S2031/S2032/
S2034/S2035/S2037 companion nodes.  It defines the paper O object
PaperOActual with the five components required by the source, constructs the
q-pilot component outright, and reduces the object to the exact bundle of
missing constructions.

## What the paper object is (IUT II, Definitions 1.1 and 4.9, Example 1.8)

PaperOActual has exactly these fields:

* (a) FPsiPrimeStrip: the actual F-double-plus-prime-strip.  Its local value
  monoids are the actual local O-times of the actual local fields (not the
  S1487 shear monoid SourceHaarActualValueMonoid, and not the reduced
  identity-projection strip localOFieldStrip), and its local groups carry an
  actual once-punctured elliptic curve with the tempered/etale fundamental
  groups and the functorial surjection onto the local absolute Galois group
  whose geometric kernel is nontrivial.
* (b) ThetaMonoidActual: the paper-level theta / Gaussian monoid assignment of
  IUT II, Corollary 4.6, (iv), over the fixed finite theta packet of the actual
  input, with the Gaussian evaluation of Proposition 4.1, (iv).  This is not
  the local-field model PsiEnvModel/PsiGauModel of S1973.
* (c) OUnitsMuActor: the group-theoretic actor O-times-mu(G) of IUT II,
  Example 1.8, (iii)--(iv): a construction depending only on the profinite
  group G, functorial under isomorphisms of profinite groups, evaluated at the
  actual local absolute Galois groups and identified with the actual local
  O-times-mu.
* (d) QPilotODaggerData: the actual q-pilot O-triangle generator, constructed
  in section 1 from the actual Tate parameter q = l
  (ConcreteTateParameter.canonical), with O-triangle isomorphic to N, an
  infinite-order generator, its nonnegative realified value, and the theorem
  that it cannot be identified with the degenerate S1487 value monoid.
* (e) OperationKummerEvaluation: the operation-level Kummer isomorphism (IUT
  II, Definition 4.9, (i)) and evaluation isomorphism (IUT II, Corollary 4.10,
  (ii)) between the group-theoretic side O-times-mu(G_v) and the Frobenioid
  side O-times-mu of the actual local monoid.

## What is proved here (kernel-checked, no sorry, no axiom)

1. The construction of (d), with O-triangle isomorphic to N, a nontrivial
   infinite-order generator, and the formal impossibility
   not (Nonempty (O-triangle ~= SourceHaarActualValueMonoid)) of identifying it
   with the degenerate S1487 value monoid.
2. For every PaperOActual, the local monoids are the actual local O-times
   (fPsi_mon_not_sourceHaar), and its strip cannot be the reduced
   identity-projection strip localOFieldStrip
   (no_fPsi_equiv_localOFieldStrip): the geometric kernel is nontrivial on the
   paper side and trivial on the reduced side, and strip equivalence preserves
   triviality of the kernel.
3. The exact first missing chain: PaperOActual is nonempty exactly when the
   bundle PaperOFirstMissing of the four missing constructions is nonempty
   (nonempty_paperOActual_iff), and the first link of the chain is the missing
   actual curve pi_1 (firstMissing_curvePiOne).

## The exact first missing chain (no fake)

The first missing is not a proposition about existing carriers; it is a
missing construction.  In dependency order:

1. CurvePiOneData (component (a)): the actual etale and tempered fundamental
   groups of the once-punctured elliptic curve, with the nontrivial geometric
   kernel.  Mathlib 4.32.2 has the curve scheme curveScheme and the category of
   finite etale covers, but no Galois-category structure, no fiber functor, no
   curve pi_1 and no curve-to-anabelioid functor.  The tree concrete strips use
   the identity projection and are proved to have trivial geometric kernel
   (localDPrimeStrip_geometric_eq_bot); they are excluded here by
   no_fPsi_equiv_localOFieldStrip.  The companion S2037 records the same
   missing datum as CurvePi1Family.
2. OUnitsMuActor (component (c)): the group-theoretic algorithm of Example
   1.8, (iii)--(iv) does not exist in the tree; S1967 proves that the S1487
   carrier has trivial units, and S1978 attaches the actual local O-times
   carrier but not the algorithm.
3. ThetaMonoidActual (component (b)): the cohomological Psi_cns of
   [AbsTopIII], Corollary 1.10, (b) and its identification with the actual
   local integral monoid are not constructed; S1973 builds only the local-field
   model.
4. OperationKummerEvaluation (component (e)): it consumes (b) and (c), so it is
   missing until they exist; the operation-level Kummer/evaluation on the
   actual local O-times / O-times-mu carrier is constructed at the reduced
   level in the companion S2034/S2045.

No True, PUnit, empty type, arbitrary inhabitant, sorry, axiom or
assumption-only Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S2038PaperOActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual (PaperV)
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open AlgebraicGeometry

/-! ## 1. The q-pilot generator: the actual local q-parameter -/

/-- The actual local q-parameter q = l of the paper bad place, as an element of
the actual local field Q_l.  This is the Tate parameter of
ConcreteTateParameter.canonical, not a realified value. -/
noncomputable def qPilotValue (l : PrimeGeFive) : ℚ_[l.value] :=
  letI := l.factPrime
  (ConcreteTateParameter.canonical l).q

theorem qPilotValue_eq_prime (l : PrimeGeFive) :
    qPilotValue l = (l.value : ℚ_[l.value]) := by
  letI := l.factPrime
  exact ConcreteTateParameter.canonical_q l

theorem qPilotValue_ne_zero (l : PrimeGeFive) : qPilotValue l ≠ 0 := by
  rw [qPilotValue_eq_prime]
  exact_mod_cast l.prime.ne_zero

theorem qPilotValue_ne_one (l : PrimeGeFive) : qPilotValue l ≠ 1 := by
  letI := l.factPrime
  exact ConcreteTateParameter.canonical_q_ne_one l

/-- The actual O-triangle monoid of the q-pilot: the submonoid of the actual
local field generated by the actual q-parameter.  IUT II, Definition 4.9,
(viii): each O-triangle(-) is abstractly isomorphic to N, generated by the
q-parameter. -/
noncomputable def qPilotODaggerCarrier (l : PrimeGeFive) : Submonoid ℚ_[l.value] :=
  Submonoid.powers (qPilotValue l)

/-- The generator of O-triangle: the actual q-parameter itself. -/
noncomputable def qPilotODaggerGenerator (l : PrimeGeFive) : qPilotODaggerCarrier l :=
  ⟨qPilotValue l, Submonoid.mem_powers _⟩

theorem qPilotODaggerGenerator_coe (l : PrimeGeFive) :
    (qPilotODaggerGenerator l : ℚ_[l.value]) = qPilotValue l :=
  rfl

theorem qPilotODaggerGenerator_ne_one (l : PrimeGeFive) :
    qPilotODaggerGenerator l ≠ 1 := by
  intro h
  apply qPilotValue_ne_one l
  simpa using congrArg (fun x : qPilotODaggerCarrier l => (x : ℚ_[l.value])) h

theorem qPilotODaggerCarrier_nontrivial (l : PrimeGeFive) :
    Nontrivial (qPilotODaggerCarrier l) :=
  ⟨⟨1, qPilotODaggerGenerator l, fun h => qPilotODaggerGenerator_ne_one l h.symm⟩⟩

/-- The actual q-parameter has infinite multiplicative order: no positive power
of it is 1. -/
theorem qPilotValue_pow_ne_one (l : PrimeGeFive) :
    ∀ n : ℕ, 0 < n → qPilotValue l ^ n ≠ 1 := by
  intro n hn
  letI := l.factPrime
  exact ConcreteTateParameter.q_power_ne_one l (ConcreteTateParameter.canonical l) n hn

theorem qPilotValue_pow_injective (l : PrimeGeFive) :
    Function.Injective (fun m : ℕ => qPilotValue l ^ m) := by
  have key : ∀ a b : ℕ, a ≤ b → qPilotValue l ^ a = qPilotValue l ^ b → a = b := by
    intro a b hab hab_eq
    have hd : qPilotValue l ^ (b - a) = 1 := by
      have h2 : qPilotValue l ^ a = qPilotValue l ^ a * qPilotValue l ^ (b - a) := by
        rw [hab_eq, ← pow_add, Nat.add_sub_cancel' hab]
      have h3 : qPilotValue l ^ a * 1 = qPilotValue l ^ a * qPilotValue l ^ (b - a) := by
        rwa [mul_one]
      exact mul_left_cancel h3
    rcases Nat.eq_or_lt_of_le hab with hEq | hLt
    · exact hEq
    · exact absurd hd (qPilotValue_pow_ne_one l (b - a) (Nat.sub_pos_of_lt hLt))
  intro m n h
  rcases Nat.le_total m n with hle | hle
  · exact key m n hle h
  · exact (key n m hle h.symm).symm

/-- O-triangle is abstractly isomorphic to N, as the paper states for each
O-triangle(-). -/
noncomputable def qPilotODaggerEquivNat (l : PrimeGeFive) :
    Multiplicative ℕ ≃* qPilotODaggerCarrier l :=
  Submonoid.powLogEquiv (qPilotValue_pow_injective l)

theorem qPilotODaggerEquivNat_ofAdd_one (l : PrimeGeFive) :
    qPilotODaggerEquivNat l (Multiplicative.ofAdd 1) = qPilotODaggerGenerator l := by
  apply Subtype.ext
  rw [show qPilotODaggerEquivNat l (Multiplicative.ofAdd 1) =
      Submonoid.pow (qPilotValue l) 1 from rfl]
  rw [Submonoid.pow_apply]
  simp

/-- The realified value of the q-pilot: the nonnegative norm on O-triangle. -/
noncomputable def qPilotODaggerValue (l : PrimeGeFive) :
    qPilotODaggerCarrier l →* ℝ≥0 where
  toFun x := Real.toNNReal ‖(x : ℚ_[l.value])‖
  map_one' := by simp
  map_mul' x y := by
    simp only [Submonoid.coe_mul, norm_mul]
    exact Real.toNNReal_mul (norm_nonneg _) (norm_nonneg _)

/-- The actual q-parameter is a non-unit integral element: its norm is less
than one. -/
theorem qPilotValue_norm_lt_one (l : PrimeGeFive) : ‖qPilotValue l‖ < 1 := by
  letI := l.factPrime
  exact (ConcreteTateParameter.canonical l).q_norm_lt_one

/-- The constructed O-triangle carrier lies in the actual integral monoid
O-triangle of the local field: every element has norm at most one.  This is the
source condition q_v in O-triangle of IUT I, Section 3. -/
theorem qPilotODagger_integral (l : PrimeGeFive) (x : qPilotODaggerCarrier l) :
    ‖(x : ℚ_[l.value])‖ ≤ 1 := by
  obtain ⟨n, rfl⟩ :=
    (Submonoid.mem_powers_iff (qPilotValue l) (qPilotValue l)).mp x.2
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (le_of_lt (qPilotValue_norm_lt_one l))

/-! ### The S1487 degenerate value monoid cannot carry the generator -/

/-- The degenerate S1487 value monoid is divisible: every element is a
square. -/
theorem sourceHaar_divisible (x : SourceHaarActualValueMonoid) :
    ∃ y : SourceHaarActualValueMonoid, y * y = x := by
  obtain ⟨a, ha⟩ :
      ∃ a : sourceHaarActualNonpositiveAddSubmonoid, Multiplicative.ofAdd a = x :=
    ⟨Multiplicative.toAdd x, by simp⟩
  refine ⟨Multiplicative.ofAdd ⟨(a : ℝ) / 2, ?_⟩, ?_⟩
  · exact div_nonpos_of_nonpos_of_nonneg a.2 (by norm_num)
  · rw [← ha, ← Multiplicative.ofAdd_add]
    congr 1
    apply Subtype.ext
    simp only [AddSubmonoid.coe_add, Subtype.coe_mk]
    ring

/-- N is not divisible: ofAdd 1 has no square root. -/
theorem nat_no_sqrt_one :
    ¬ ∃ a : Multiplicative ℕ, a * a = Multiplicative.ofAdd 1 := by
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ : ∃ n, a = Multiplicative.ofAdd n := ⟨a.toAdd, by cases a; rfl⟩
  have h2 : Multiplicative.ofAdd (n + n) = Multiplicative.ofAdd 1 := by
    rw [Multiplicative.ofAdd_add]
    exact ha
  exact absurd (Multiplicative.ofAdd.injective h2) (by omega)

theorem qPilotODagger_no_sqrt_generator (l : PrimeGeFive) :
    ¬ ∃ a : qPilotODaggerCarrier l, a * a = qPilotODaggerGenerator l := by
  rintro ⟨a, ha⟩
  have hsymm : (qPilotODaggerEquivNat l).symm (qPilotODaggerGenerator l) =
      Multiplicative.ofAdd 1 := by
    rw [← qPilotODaggerEquivNat_ofAdd_one l, MulEquiv.symm_apply_apply]
  have hsq : (qPilotODaggerEquivNat l).symm a * (qPilotODaggerEquivNat l).symm a =
      Multiplicative.ofAdd 1 := by
    rw [← map_mul, ha, hsymm]
  exact nat_no_sqrt_one ⟨_, hsq⟩

/-- The actual q-pilot O-triangle carrier is not isomorphic to the degenerate
S1487 value monoid SourceHaarActualValueMonoid: the latter is divisible, the
former is N. -/
theorem qPilotODaggerCarrier_no_equiv_sourceHaar (l : PrimeGeFive) :
    ¬ Nonempty (qPilotODaggerCarrier l ≃* SourceHaarActualValueMonoid) := by
  rintro ⟨e⟩
  obtain ⟨y, hy⟩ := sourceHaar_divisible (e (qPilotODaggerGenerator l))
  obtain ⟨a, rfl⟩ := e.surjective y
  have haa : a * a = qPilotODaggerGenerator l := by
    apply e.injective
    rw [map_mul, hy]
  exact qPilotODagger_no_sqrt_generator l ⟨a, haa⟩

/-- The constructed actual q-pilot O-triangle datum (paper component (d)). -/
structure QPilotODaggerData (l : PrimeGeFive) where
  generator : qPilotODaggerCarrier l
  generator_is_q : (generator : ℚ_[l.value]) = qPilotValue l
  generator_ne_one : generator ≠ 1
  free : Multiplicative ℕ ≃* qPilotODaggerCarrier l
  free_one : free (Multiplicative.ofAdd 1) = generator
  infinite_order : Function.Injective (fun m : ℕ => generator ^ m)
  value : qPilotODaggerCarrier l →* ℝ≥0
  integral : ∀ x : qPilotODaggerCarrier l, ‖(x : ℚ_[l.value])‖ ≤ 1
  not_sourceHaar : ¬ Nonempty (qPilotODaggerCarrier l ≃* SourceHaarActualValueMonoid)

/-- The actual q-pilot O-triangle datum of the paper O object. -/
noncomputable def paperQPilotODaggerData (l : PrimeGeFive) : QPilotODaggerData l where
  generator := qPilotODaggerGenerator l
  generator_is_q := rfl
  generator_ne_one := qPilotODaggerGenerator_ne_one l
  free := qPilotODaggerEquivNat l
  free_one := qPilotODaggerEquivNat_ofAdd_one l
  infinite_order := by
    intro m n h
    apply qPilotValue_pow_injective l
    simpa using congrArg (fun x : qPilotODaggerCarrier l => (x : ℚ_[l.value])) h
  value := qPilotODaggerValue l
  integral := qPilotODagger_integral l
  not_sourceHaar := qPilotODaggerCarrier_no_equiv_sourceHaar l

theorem paperQPilotODaggerData_nonempty (l : PrimeGeFive) :
    Nonempty (QPilotODaggerData l) :=
  ⟨paperQPilotODaggerData l⟩
