/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1949NonarchimedeanLogShellActual
import tmp.sheaf.xif.paper.S1958FullLogKummerUQActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.Foundations.Arithmetic.NormLog

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# S1961: the real-valued local-to-global log-shell bridge

Layer: **O** (original Theta-link / q-pilot), consumer of S1949 and S1927.

## The problem

S1949 constructs, at every finite prime place v : FinitePrimePlace 2 7, the
actual nonarchimedean log-shell datum

  actualLocalLogShellDatum v : SourceLogShellDatum

with actual completed local field Completion (QPlace v), actual
G_v-invariant units (CompletionIntegers (QPlace v))ˣ (the fixed-unit
theorem galoisFixedCompletionUnits_eq_top), and the actual analytic p-adic
logarithm completionUnitLogHom (QPlace v) : (CompletionIntegers (QPlace v))ˣ →*
Multiplicative (Completion (QPlace v)).

S1927's finite global packet, on the other hand, is the Q-span over the
one-column index of the reduced norm-log data

  paperLogShellDatum v with K = ℝ, Units = (Completion (QPlace v))ˣ,
  logMap = unitNormLogDegree (Completion (QPlace v)).

Thus S1949 is not a drop-in replacement for S1927's finite packet: the actual
log takes values in the p-adic completion, while the packet is a real vector
space.

## What this file constructs

The real-valued bridge

  realBridge v : Completion (QPlace v) → ℝ,  x ↦ Real.log ‖x‖

(the norm-log functional; Real.log 0 = 0 in Mathlib) applied to the actual
local log-shell (actualLocalLogShellDatum v).logShell.  The bridged local
fiber is

  bridgeFiber v := Submodule.span ℚ (realBridge v '' actualLogShell_v)

and the bridged global finite packet is

  bridgePacket := Submodule.pi Set.univ (fun v => bridgeFiber v).

### Main identifications

* bridgeFiber_eq_paperSpan: at every finite place the Q-span of the
  real bridge image of the actual log-shell equals the Q-span of the reduced
  norm-log shell (paperLogShellDatum v).logShell.
* bridgePacket_eq_paperGlobalLogShellPacket:
  bridgePacket = paperGlobalLogShellPacket, i.e. S1927's finite packet is
  exactly the Q-span of the actual p-adic log-shell under the real-valued
  norm-log bridge.  Consequently every P : S1927FullLogKummerUQ D has
  P.finiteLogShell = bridgePacket (s1961_finiteLogShell_eq_bridge), and
  in particular the actual S1958 package paperFullLogKummerUQ D does.
* bridgePacket_eq_span_actualLogShell: the packet is literally the Q-span of
  the product of the actual log-shell images (the IQ of the paper is a
  Q-span, [IUTchIII, Proposition 3.2, (ii)]).

### Why the identification holds (the actual computation, no fake)

Let m_v := Ideal.absNorm (QPlace v).maximalIdeal.asIdeal, so the canonical
p-adic norm of a nonzero x is m_v ^ n for the integer valuation exponent
n (NumberFieldFinitePlace.logNorm_eq_absNorm_mul).  The real generator is
L_v := Real.log m_v, and 1 < m_v gives L_v ≠ 0.

* Both local Q-spans are contained in ℚ · L_v: every log-norm is an integer
  multiple of L_v (logNorm_eq_absNorm_mul), and the reduced shell only
  multiplies the pre-log-shell by the rational (p*_v)^{-1}.
* Both contain L_v: the completed integer ring
  CompletionIntegers (QPlace v) is a discrete valuation ring
  (IsDiscreteValuationRing.exists_irreducible).  An irreducible π is a
  nonunit, hence Valued.v π < 1, so π lies in the actual compact log-shell
  (S1949's completionIntegers_subset_actualLogShell) and Real.log ‖π‖ is a
  nonzero integer multiple of L_v; dividing by that integer gives L_v in the
  span.  The very same π, as a unit of the completed field, supplies the
  corresponding nonzero element of S1927's reduced pre-log-shell.

## Honest scope (not claimed)

The identification is at the level of the Q-span IQ, exactly the level at
which S1927's finite packet is defined.  It does not assert the levelwise
equality

  realBridge '' actualLogShell_v = (paperLogShellDatum v).logShell

(which is false in general: the actual shell is a subset of the p-adic field,
while the reduced shell is a subset of ℝ), nor does it construct a real-valued
additive functional on the p-adic field.  Such a levelwise realification would
require an additional additive real-valued functional and is not needed for
the S1927 packet.  The actual p-adic log enters through the actual log-shell
set; the bridge is the canonical norm-log readout used by S1927, and the
theorem says that its Q-span is forced by the actual local log-shell.

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant or Nonempty
gate is used.  Axiom probes are at the end of the file.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1961LocalGlobalBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1949NonarchimedeanLogShellActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain

/-! ## 1. The rank-one real generator of the local norm-log -/

/-- The real logarithm of the residue-field cardinality at v: the generator
of the real norm-log lattice at the finite place v. -/
def absNormLog (v : FinitePrimePlace 2 7) : ℝ :=
  Real.log (Ideal.absNorm (QPlace v).maximalIdeal.asIdeal : ℝ)

/-- The norm-log generator is positive: the residue-field cardinality is > 1. -/
theorem absNormLog_pos (v : FinitePrimePlace 2 7) : 0 < absNormLog v := by
  unfold absNormLog
  exact Real.log_pos (by
    have h := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (QPlace v).maximalIdeal
    exact_mod_cast h)

/-- The norm-log generator is nonzero. -/
theorem absNormLog_ne_zero (v : FinitePrimePlace 2 7) : absNormLog v ≠ 0 :=
  (absNormLog_pos v).ne'

/-- An actual uniformizer of the completed integer ring at v. -/
def actualUniformizer (v : FinitePrimePlace 2 7) : CompletionIntegers (QPlace v) :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible
    (CompletionIntegers (QPlace v)))

/-- The chosen completed integer is irreducible. -/
theorem actualUniformizer_irreducible (v : FinitePrimePlace 2 7) :
    Irreducible (actualUniformizer v) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible
    (CompletionIntegers (QPlace v)))

/-- The actual uniformizer is a nonunit. -/
theorem actualUniformizer_not_isUnit (v : FinitePrimePlace 2 7) :
    ¬ IsUnit (actualUniformizer v) :=
  (actualUniformizer_irreducible v).not_isUnit

/-- The actual uniformizer has valuation < 1 in the completed field. -/
theorem actualUniformizer_valued_lt_one (v : FinitePrimePlace 2 7) :
    Valued.v (actualUniformizer v : Completion (QPlace v)) < 1 := by
  have hle : Valued.v (actualUniformizer v : Completion (QPlace v)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (NumberField.RingOfIntegers ℚ) ℚ
      (QPlace v).maximalIdeal).mp (actualUniformizer v).property
  refine lt_of_le_of_ne hle ?_
  intro hval
  exact actualUniformizer_not_isUnit v
    ((HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hval)

/-- The actual uniformizer has norm < 1. -/
theorem actualUniformizer_norm_lt_one (v : FinitePrimePlace 2 7) :
    ‖(actualUniformizer v : Completion (QPlace v))‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  exact actualUniformizer_valued_lt_one v

/-- The actual uniformizer is nonzero in the completed field. -/
theorem actualUniformizer_coe_ne_zero (v : FinitePrimePlace 2 7) :
    (actualUniformizer v : Completion (QPlace v)) ≠ 0 := by
  intro hzero
  have hπ0 : actualUniformizer v = 0 := Subtype.ext (by simpa using hzero)
  exact (actualUniformizer_irreducible v).ne_zero hπ0

/-- The actual uniformizer's log-norm is nonzero. -/
theorem actualUniformizer_logNorm_ne_zero (v : FinitePrimePlace 2 7) :
    Real.log ‖(actualUniformizer v : Completion (QPlace v))‖ ≠ 0 := by
  have hpos : 0 < ‖(actualUniformizer v : Completion (QPlace v))‖ :=
    norm_pos_iff.mpr (actualUniformizer_coe_ne_zero v)
  exact Real.log_ne_zero_of_pos_of_ne_one hpos (ne_of_lt (actualUniformizer_norm_lt_one v))

/-- The actual uniformizer lies in the actual log-shell. -/
theorem actualUniformizer_logNorm_mem_actualLogShell (v : FinitePrimePlace 2 7) :
    (actualUniformizer v : Completion (QPlace v)) ∈
      (actualLocalLogShellDatum v).logShell :=
  completionIntegers_subset_actualLogShell v (actualUniformizer v).property

/-! ## 2. The real-valued bridge and its local Q-span -/

/-- The real-valued norm-log bridge on the actual p-adic completion:
x ↦ log ‖x‖ (Real.log 0 = 0 in Mathlib). -/
def realBridge (v : FinitePrimePlace 2 7) (x : Completion (QPlace v)) : ℝ :=
  Real.log ‖x‖

/-- The real image of the actual local log-shell under the bridge. -/
def realBridgeImage (v : FinitePrimePlace 2 7) : Set ℝ :=
  realBridge v '' ((actualLocalLogShellDatum v).logShell)

/-- The bridged local fiber: the Q-span of the actual log-shell's real image. -/
def bridgeFiber (v : FinitePrimePlace 2 7) : Submodule ℚ ℝ :=
  Submodule.span ℚ (realBridgeImage v)

/-- The reduced S1927 local shell's Q-span, with the real codomain explicit. -/
def paperSpan (v : FinitePrimePlace 2 7) : Submodule ℚ ℝ :=
  Submodule.span ℚ (((paperLogShellDatum v).logShell) : Set ℝ)

/-- The common one-dimensional real span generated by the norm-log. -/
def generatorSpan (v : FinitePrimePlace 2 7) : Submodule ℚ ℝ :=
  Submodule.span ℚ ({absNormLog v} : Set ℝ)

theorem realBridge_zero (v : FinitePrimePlace 2 7) : realBridge v 0 = 0 := by
  simp [realBridge]

/-- Every element of the actual log-shell's real image lands in ℚ · L_v. -/
theorem realBridgeImage_subset_generatorSpan (v : FinitePrimePlace 2 7) :
    realBridgeImage v ⊆ (generatorSpan v : Set ℝ) := by
  rintro y ⟨x, _hx, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    rw [realBridge_zero]
    exact Submodule.zero_mem _
  · let k : ℤ := Multiplicative.toAdd (WithZero.unzero
      (valuation_ne_zero_of_ne_zero (QPlace v) x hx0))
    have hk : Real.log ‖x‖ = (k : ℝ) * absNormLog v := by
      unfold absNormLog
      exact logNorm_eq_absNorm_mul (QPlace v) x hx0
    have hsm : (k : ℚ) • absNormLog v ∈ generatorSpan v :=
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    have hval : realBridge v x = (k : ℚ) • absNormLog v := by
      unfold realBridge
      rw [hk, Rat.smul_def, Rat.cast_intCast]
    rw [hval]
    exact hsm

/-- ℚ · L_v is contained in the bridged local fiber. -/
theorem generatorSpan_le_bridgeFiber (v : FinitePrimePlace 2 7) :
    generatorSpan v ≤ bridgeFiber v := by
  rw [generatorSpan, Submodule.span_le]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  let π := actualUniformizer v
  have hπne : (π : Completion (QPlace v)) ≠ 0 := actualUniformizer_coe_ne_zero v
  have hmem : (π : Completion (QPlace v)) ∈ (actualLocalLogShellDatum v).logShell :=
    actualUniformizer_logNorm_mem_actualLogShell v
  have hz : realBridge v (π : Completion (QPlace v)) ∈ realBridgeImage v :=
    ⟨(π : Completion (QPlace v)), hmem, rfl⟩
  have hzspan : realBridge v (π : Completion (QPlace v)) ∈ bridgeFiber v :=
    Submodule.subset_span hz
  let k : ℤ := Multiplicative.toAdd (WithZero.unzero
    (valuation_ne_zero_of_ne_zero (QPlace v) (π : Completion (QPlace v)) hπne))
  have hk : realBridge v (π : Completion (QPlace v)) = (k : ℝ) * absNormLog v := by
    unfold realBridge absNormLog
    exact logNorm_eq_absNorm_mul (QPlace v) (π : Completion (QPlace v)) hπne
  have hk0 : k ≠ 0 := by
    intro hkz
    have hz0 : realBridge v (π : Completion (QPlace v)) = 0 := by
      rw [hk, hkz]
      norm_num
    have hz0' : Real.log ‖(π : Completion (QPlace v))‖ = 0 := by
      simpa [realBridge] using hz0
    exact (show Real.log ‖(actualUniformizer v : Completion (QPlace v))‖ ≠ 0 from
      actualUniformizer_logNorm_ne_zero v) hz0'
  have hval : absNormLog v =
      ((k : ℚ)⁻¹) • realBridge v (π : Completion (QPlace v)) := by
    rw [hk, Rat.smul_def, Rat.cast_inv, Rat.cast_intCast]
    field_simp
  rw [hval]
  exact Submodule.smul_mem _ _ hzspan

/-- The bridged local fiber is the common norm-log line. -/
theorem bridgeFiber_eq_generatorSpan (v : FinitePrimePlace 2 7) :
    bridgeFiber v = generatorSpan v := by
  apply le_antisymm
  · unfold bridgeFiber
    exact Submodule.span_le.mpr (realBridgeImage_subset_generatorSpan v)
  · exact generatorSpan_le_bridgeFiber v

/-- The reduced S1927 local shell's span is contained in the norm-log line. -/
theorem paperSpan_le_generatorSpan (v : FinitePrimePlace 2 7) :
    paperSpan v ≤ generatorSpan v := by
  unfold paperSpan
  rw [Submodule.span_le]
  intro a ha
  change ((paperLogShellDatum v).pStar : ℝ) * a ∈
    (paperLogShellDatum v).preLogShell at ha
  rcases ha with ⟨u, -, hu⟩
  let u' : (actualLocalField v)ˣ := show (actualLocalField v)ˣ from u
  have hlog : ((paperLogShellDatum v).logMap u).toAdd =
      Real.log ‖(u' : actualLocalField v)‖ := rfl
  have hune : (u' : actualLocalField v) ≠ 0 := Units.ne_zero u'
  let k : ℤ := Multiplicative.toAdd (WithZero.unzero
    (valuation_ne_zero_of_ne_zero (QPlace v) (u' : actualLocalField v) hune))
  have hk : Real.log ‖(u' : actualLocalField v)‖ = (k : ℝ) * absNormLog v := by
    unfold absNormLog
    exact logNorm_eq_absNorm_mul (QPlace v) (u' : actualLocalField v) hune
  have h1 : ((paperLogShellDatum v).pStar : ℝ) * a = (k : ℝ) * absNormLog v := by
    rw [← hu, hlog, hk]
  have hpstar : ((paperLogShellDatum v).pStar : ℝ) ≠ 0 := by
    exact_mod_cast (paperLogShellDatum v).pStar_ne_zero
  have hval : a = ((k : ℚ) / ((paperLogShellDatum v).pStar : ℚ)) • absNormLog v := by
    rw [Rat.smul_def]
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hpstar]
    rw [mul_comm a, h1]
  rw [hval]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- The norm-log line is contained in the reduced S1927 local shell's span. -/
theorem generatorSpan_le_paperSpan (v : FinitePrimePlace 2 7) :
    generatorSpan v ≤ paperSpan v := by
  rw [generatorSpan, Submodule.span_le]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  let π := actualUniformizer v
  have hπne : (π : Completion (QPlace v)) ≠ 0 := actualUniformizer_coe_ne_zero v
  let u : (Completion (QPlace v))ˣ := Units.mk0 (π : Completion (QPlace v)) hπne
  have hpre : Real.log ‖(π : Completion (QPlace v))‖ ∈
      (paperLogShellDatum v).preLogShell := by
    refine ⟨u, Submonoid.mem_top u, ?_⟩
    rfl
  have hshell : Real.log ‖(π : Completion (QPlace v))‖ ∈
      (paperLogShellDatum v).logShell :=
    (paperLogShellDatum v).preLogShell_subset_logShell hpre
  have hzspan : Real.log ‖(π : Completion (QPlace v))‖ ∈ paperSpan v :=
    Submodule.subset_span hshell
  let k : ℤ := Multiplicative.toAdd (WithZero.unzero
    (valuation_ne_zero_of_ne_zero (QPlace v) (π : Completion (QPlace v)) hπne))
  have hk : Real.log ‖(π : Completion (QPlace v))‖ = (k : ℝ) * absNormLog v := by
    unfold absNormLog
    exact logNorm_eq_absNorm_mul (QPlace v) (π : Completion (QPlace v)) hπne
  have hk0 : k ≠ 0 := by
    intro hkz
    have hz0 : Real.log ‖(π : Completion (QPlace v))‖ = 0 := by
      rw [hk, hkz]
      norm_num
    exact (show Real.log ‖(actualUniformizer v : Completion (QPlace v))‖ ≠ 0 from
      actualUniformizer_logNorm_ne_zero v) hz0
  have hval : absNormLog v = ((k : ℚ)⁻¹) •
      Real.log ‖(π : Completion (QPlace v))‖ := by
    rw [hk, Rat.smul_def, Rat.cast_inv, Rat.cast_intCast]
    field_simp
  rw [hval]
  exact Submodule.smul_mem _ _ hzspan

/-- Every log-norm generator is a nonzero integer multiple of L_v. -/
theorem paperSpan_eq_generatorSpan (v : FinitePrimePlace 2 7) :
    paperSpan v = generatorSpan v :=
  le_antisymm (paperSpan_le_generatorSpan v) (generatorSpan_le_paperSpan v)

/-- Both local fibers are the norm-log line. -/
theorem bridgeFiber_eq_paperSpan (v : FinitePrimePlace 2 7) :
    bridgeFiber v = paperSpan v := by
  rw [bridgeFiber_eq_generatorSpan, paperSpan_eq_generatorSpan]

/-! ## 3. The global finite packet -/

/-- The bridged global finite packet: the product of the local Q-spans of the
actual log-shell images. -/
def bridgePacket : Submodule ℚ (FinitePrimePlace 2 7 → ℝ) :=
  Submodule.pi Set.univ (fun v => bridgeFiber v)

/-- The global bridge packet is exactly the Q-span of the product of the
actual local log-shell images. -/
theorem bridgePacket_eq_span_actualLogShell :
    bridgePacket = Submodule.span ℚ
      (Set.pi Set.univ (fun v => realBridgeImage v)) := by
  unfold bridgePacket
  exact (sourceLogShell_span_pi_eq_pi_span (R := ℚ)
    (t := fun v => realBridgeImage v)
    (fun v => by
      refine ⟨(0 : Completion (QPlace v)), (actualLocalLogShellDatum v).zero_mem_logShell, ?_⟩
      exact realBridge_zero v)).symm

/-- S1927's global finite packet is the product of the reduced local Q-spans,
written with the common real codomain. -/
theorem paperGlobalLogShellPacket_eq_pi_paperSpan :
    paperGlobalLogShellPacket = Submodule.pi Set.univ (fun v => paperSpan v) := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_pi]
    intro v _
    have hxv : x v ∈ (paperGlobalLogShellFamily v).IQSpan :=
      (sourceLogShellIQDirectSumPacket_mem_iff paperGlobalLogShellFamily x).mp hx v
    exact hxv
  · intro x hx
    rw [Submodule.mem_pi] at hx
    unfold paperGlobalLogShellPacket
    refine (sourceLogShellIQDirectSumPacket_mem_iff paperGlobalLogShellFamily x).mpr ?_
    intro v
    exact hx v trivial

/-- **Main bridge identity**: S1927's finite packet is the Q-span of the
actual p-adic log-shell under the real-valued norm-log bridge. -/
theorem bridgePacket_eq_paperGlobalLogShellPacket :
    bridgePacket = paperGlobalLogShellPacket := by
  rw [paperGlobalLogShellPacket_eq_pi_paperSpan]
  apply le_antisymm
  · intro x hx
    unfold bridgePacket at hx
    rw [Submodule.mem_pi] at hx
    rw [Submodule.mem_pi]
    intro v _
    rw [← bridgeFiber_eq_paperSpan v]
    exact hx v trivial
  · intro x hx
    rw [Submodule.mem_pi] at hx
    unfold bridgePacket
    rw [Submodule.mem_pi]
    intro v _
    rw [bridgeFiber_eq_paperSpan v]
    exact hx v trivial

/-- The finite packet of any S1927 full log-Kummer package is the bridge
packet.  The structure field already pins the packet to
paperGlobalLogShellPacket; the bridge identity identifies it with the Q-span of
the actual p-adic log data. -/
theorem s1961_finiteLogShell_eq_bridge
    (D : S1895PaperInput) (P : S1927FullLogKummerUQ D) :
    P.finiteLogShell = bridgePacket := by
  rw [P.finiteLogShell_eq]
  exact bridgePacket_eq_paperGlobalLogShellPacket.symm

/-- The actual S1958 package's finite packet is the bridge packet. -/
theorem s1961_paperFullLogKummerUQ_finiteLogShell_eq_bridge
    (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).finiteLogShell = bridgePacket :=
  s1961_finiteLogShell_eq_bridge D (paperFullLogKummerUQ D)

/-- The bridge packet's local fibers are the reduced S1927 fibers; this is the
fiber-level form of the main identity. -/
theorem bridgePacket_local_fiber_eq (v : FinitePrimePlace 2 7) :
    bridgeFiber v = paperSpan v :=
  bridgeFiber_eq_paperSpan v

/-- The actual local log-shell is a subset of the p-adic completion, and its
real bridge image has the same Q-span as the reduced real packet. -/
theorem bridgePacket_uses_actualLogShell :
    bridgePacket = Submodule.span ℚ
      (Set.pi Set.univ (fun v => realBridgeImage v)) :=
  bridgePacket_eq_span_actualLogShell

/-- The finite packet of every S1927 package is literally the Q-span of the
product of the actual local log-shell images. -/
theorem s1961_finiteLogShell_eq_span_actualLogShell
    (D : S1895PaperInput) (P : S1927FullLogKummerUQ D) :
    P.finiteLogShell = Submodule.span ℚ
      (Set.pi Set.univ (fun v => realBridgeImage v)) := by
  rw [s1961_finiteLogShell_eq_bridge, bridgePacket_eq_span_actualLogShell]

/-- The actual S1958 package's finite packet in the same form. -/
theorem s1961_paperFullLogKummerUQ_finiteLogShell_eq_span_actualLogShell
    (D : S1895PaperInput) :
    (paperFullLogKummerUQ D).finiteLogShell = Submodule.span ℚ
      (Set.pi Set.univ (fun v => realBridgeImage v)) :=
  s1961_finiteLogShell_eq_span_actualLogShell D (paperFullLogKummerUQ D)

/-! ## 4. Axiom probes -/

#print axioms paperSpan_eq_generatorSpan
#print axioms bridgeFiber_eq_paperSpan
#print axioms bridgePacket_eq_span_actualLogShell
#print axioms paperGlobalLogShellPacket_eq_pi_paperSpan
#print axioms bridgePacket_eq_paperGlobalLogShellPacket
#print axioms s1961_finiteLogShell_eq_bridge
#print axioms s1961_paperFullLogKummerUQ_finiteLogShell_eq_bridge
#print axioms s1961_finiteLogShell_eq_span_actualLogShell
#print axioms s1961_paperFullLogKummerUQ_finiteLogShell_eq_span_actualLogShell

end LeanFormal.IUT.XiFPaper.S1961LocalGlobalBridgeActual

