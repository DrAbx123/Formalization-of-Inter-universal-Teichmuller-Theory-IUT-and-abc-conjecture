import tmp.sheaf.xif.paper.S2129RootNecessaryActual

/-!
# S2190: the actual paper-source conditions behind the two root divisibilities

S2129 (S2129RootNecessaryActual) proves that a completion 2l-th root of the
paper q_v at the section-designated K-place forces

* l ∣ eSource (S2129LDivRamification), where eSource is the ramification
  index of S1413's section lift sectionKPlace T b over its F-shadow, and
* 2 ∣ (sectionQ T b).order (S2129TwoDivOrder),

and that the recorded order law ord(q_v) = eSource * ord(shadowQ) with
Coprime ord(shadowQ) l (S1413) does not by itself imply either condition
(S467's counterexample; S2129 section 3).

This file audits the same two conditions against the actual paper source
data named in the task: S1413 (section K-place and q comparison), S2032
(local O^◃/Q_5 model), S2040 (paper O^tri/q_v/O^×μ attachment), S2057
(finite root-stack Theta-pilot object), and the six clauses of
SourceNativeInitialThetaData.

## Audit result

The current source data do not provide either condition.  What they do
provide at the section place is the exact package proved below
(current_source_arithmetic):

* 0 < eSource, 0 < ord(shadowQ), Coprime ord(shadowQ) l,
* ord(q_v) = eSource * ord(shadowQ),
* 0 < ord(q_v) and eSource ∣ ord(q_v).

None of the clauses mentions the parity of ord(shadowQ), the parity of
eSource, or the l-divisibility of eSource.  Clause (b)'s Tate comparison
supplies order_coprime only; clause (c) supplies the rational 2*3-torsion
and the kernel-field identification K = F(E[l]), but the tree has no
Tate-torsion bridge from those data to a square root or an l-th root of
q_v (S2092 and S472 record the same gap at the qVFamily place).

## The exact new paper source conditions

The paper's own derivation of q_v^(1/2l) (IUT I, Example 3.2(iv); corpus
lines 3701--3726) uses two intermediate facts which are not formalized in
the tree:

1. S2190QSquareSource: q_v is a square in the completion at
   sectionKPlace T b.  The paper derives it from the rationality of the
   2*3-torsion (Definition 3.1(b)) via the Tate uniformization.  This
   condition implies 2 ∣ ord(q_v) (hence S2129TwoDivOrder).
2. S2190QLthPowerSource: q_v is an l-th power in that completion.  The
   paper derives it from K = F(E[l]) (Definition 3.1(c)) via the Tate
   uniformization.  This condition implies l ∣ eSource.

A completion 2l-th root of q_v implies both conditions
(squareRootSource_of_paperRoot, lthPowerSource_of_paperRoot), so they are
intermediate consequences of the paper's root construction; this file does not
construct the root from them.  Conversely, the two half roots imply the two divisibility
conditions (rootNecessary_of_halfRootSource) and hence 2l ∣ ord(q_v).

The minimal arithmetic form of the missing source data is literally the pair
(S2129LDivRamification T b, S2129TwoDivOrder T b); the paper-faithful
sufficient form is S2190HalfRootSource T b.  Both are recorded as Props
without inhabitants: this file asserts no root and no divisibility.

## What each audited file supplies

| file | supplies | does not supply |
|---|---|---|
| S1413 | sectionQ, order law, Coprime ord(shadowQ) l, positivity, root obstruction | no value or divisibility of eSource; no parity of ord(shadowQ) |
| S2032 | local Q_5 model q_v = 5^m with only 0 < m; exact 2l-root criterion 2l ∣ m | no divisibility of the actual paperQVOrder |
| S2040 | paper O^tri/q_v/O^×μ; root field = paperOtriRootMissing | no arithmetic field; the root is still the missing datum |
| S2057 | finite root-stack root of the F-side qVFamily; real scalar 2l-th root | not a completion root; no statement about sectionQ.order |
| clauses (a)--(f) | degree F/Fmod coprime to l; bad-place q order coprime to l; torsion rationality; K = F(E[l]) | Tate-torsion bridge; no parity/divisibility of eSource |

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
assumption-only gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.style.longLine false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2092PaperOtriActual
open LeanFormal.IUT.XiFPaper.S2040PaperOtriFromS2092Actual
open LeanFormal.IUT.XiFPaper.S2040S2057InterfaceActual
open LeanFormal.IUT.XiFPaper.S2032R6GeneratorActual
open LeanFormal.IUT.XiFPaper.S2057RootStackThetaPilotActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S2129RootNecessaryActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

local instance s2190FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The exact arithmetic package supplied by the current source -/

/-- The section-place ramification index is positive: it is the ramification
index of an actual extension of finite places. -/
theorem eSource_pos : 0 < eSource T b := by
  apply Nat.pos_of_ne_zero
  exact NumberFieldFinitePlace.ramificationIdx_ne_zero (k := T.arithmetic.F)
    (place := sectionKPlace T b)

/-- The F-side clause-(b) order is positive. -/
theorem shadowQ_order_pos : 0 < (shadowQ T b).order :=
  (shadowQ T b).order_pos

/-- The K-side q-order is positive. -/
theorem sectionQ_order_pos : 0 < (sectionQ T b).order :=
  (sectionQ T b).order_pos

/-- The source ramification index divides the K-side q-order: this is the
order law read as a divisibility.  It is the only divisibility relation
recorded by the source. -/
theorem eSource_dvd_sectionQ_order : eSource T b ∣ (sectionQ T b).order :=
  ⟨(shadowQ T b).order, sectionQ_order T b⟩

/-- The exact package of arithmetic data supplied by S1413 at the section
place.  These are all the unconditional arithmetic facts about eSource,
ord(shadowQ) and ord(q_v) that the current source provides. -/
theorem current_source_arithmetic :
    0 < eSource T b ∧ 0 < (shadowQ T b).order ∧
      Nat.Coprime (shadowQ T b).order l.value ∧
      (sectionQ T b).order = eSource T b * (shadowQ T b).order ∧
      0 < (sectionQ T b).order :=
  ⟨eSource_pos T b, shadowQ_order_pos T b, shadowQ_order_coprime T b,
    sectionQ_order T b, sectionQ_order_pos T b⟩

/-- The l-part of the K-side order is exactly the source ramification: since
the F-side order is prime to l, l ∣ ord(q_v) is equivalent to
l ∣ eSource. -/
theorem l_dvd_ramification_of_l_dvd_order
    (h : l.value ∣ (sectionQ T b).order) : S2129LDivRamification T b := by
  have her : l.value ∣ eSource T b * (shadowQ T b).order := by
    rw [← sectionQ_order]
    exact h
  exact (shadowQ_order_coprime T b).symm.dvd_of_dvd_mul_right her

/-- The 2-part splits into the two actual source-level alternatives: an even
ramification index, or an even F-side shadow order. -/
theorem two_dvd_order_iff_source_split :
    S2129TwoDivOrder T b ↔ 2 ∣ eSource T b ∨ 2 ∣ (shadowQ T b).order := by
  rw [S2129TwoDivOrder, sectionQ_order, Nat.prime_two.dvd_mul]

/-! ## 2. Power roots force order divisibility

The following general lemma is the section-place form of S1413's
two_l_dvd_order_of_root: an n-th root of the completion q-parameter forces n
to divide its order.  It is used below for n = 2, n = l and n = 2l. -/

theorem order_dvd_of_pow_eq
    {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : FinitePlaceQCandidate place)
    (root : Completion place) (n : Nat) (hn : 0 < n)
    (hroot : root ^ n = parameter.q) :
    n ∣ parameter.order := by
  have hroot_ne : root ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hroot
    exact parameter.q_ne_zero hroot.symm
  have hpow : elementExponent (root ^ n) (pow_ne_zero n hroot_ne) =
      (n : Int) * elementExponent root hroot_ne :=
    elementExponent_pow (place := place) root hroot_ne n
  have hcongr : elementExponent parameter.q parameter.q_ne_zero =
      elementExponent (root ^ n) (pow_ne_zero n hroot_ne) :=
    elementExponent_congr (place := place) hroot.symm _ _
  have hexp : parameter.exponent = (n : Int) * elementExponent root hroot_ne := by
    calc parameter.exponent = elementExponent parameter.q parameter.q_ne_zero := rfl
      _ = elementExponent (root ^ n) (pow_ne_zero n hroot_ne) := hcongr
      _ = (n : Int) * elementExponent root hroot_ne := hpow
  have hpos : (0 : Int) < (n : Int) * elementExponent root hroot_ne := by
    rw [← hexp]
    exact parameter.exponent_pos
  have hnpos : (0 : Int) < (n : Int) := by exact_mod_cast hn
  have hAle : 0 ≤ elementExponent root hroot_ne := by nlinarith
  refine ⟨(elementExponent root hroot_ne).toNat, ?_⟩
  show Int.toNat parameter.exponent = n * (elementExponent root hroot_ne).toNat
  rw [hexp, Int.toNat_mul (le_of_lt hnpos) hAle, Int.toNat_natCast]

/-! ## 3. The two new paper source conditions, by name -/

/-- New paper source condition (square).  q_v admits a square root in the
completion K_v at the paper's section K-place.  The paper obtains this from
the rationality of the 2*3-torsion (IUT I, Definition 3.1(b)) through the
Tate uniformization; that bridge is not in the tree. -/
def S2190QSquareSource : Prop :=
  ∃ s : Completion (sectionKPlace T b), s ^ 2 = (sectionQ T b).q

/-- New paper source condition (l-th power).  q_v admits an l-th root in the
completion at the paper's section K-place.  The paper obtains this from
K = F(E[l]) (IUT I, Definition 3.1(c)) through the Tate uniformization; that
bridge is not in the tree. -/
def S2190QLthPowerSource : Prop :=
  ∃ r : Completion (sectionKPlace T b), r ^ l.value = (sectionQ T b).q

/-- The two new paper source conditions together. -/
def S2190HalfRootSource : Prop :=
  S2190QSquareSource T b ∧ S2190QLthPowerSource T b

/-- The exact missing bridge from Definition 3.1(b) to the square source
condition: 2*3-torsion rationality implies that q_v is a square at the
section place.  The clause data supply the antecedent
(T.clauseC.torsion23_rational); the Tate-torsion bridge is the missing
content. -/
def S2190TwoTorsionToQSqrtBridge : Prop :=
  PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve →
    S2190QSquareSource T b

/-- The exact missing bridge from Definition 3.1(c) to the l-th power
source condition: for every actual torsion basis and every actual
identification of K with the l-torsion kernel field, q_v is an l-th power at
the section place.  The clause data supply the basis and the identification
(T.clauseC.torsion_basis, T.clauseC.kernel_field_identification); the
Tate-torsion bridge is the missing content. -/
def S2190KernelFieldToQLthPowerBridge : Prop :=
  ∀ (basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      T.arithmetic.curve.LTorsion l),
    (T.arithmetic.K ≃ₐ[T.arithmetic.F]
      T.arithmetic.curve.galoisLTorsionKernelField l basis) →
      S2190QLthPowerSource T b

/-- The actual clause data present in the source: Definition 3.1(b)'s
2*3-torsion rationality and the bad-place q-order coprimality. -/
theorem actual_clause_data :
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve ∧
      Nat.Coprime (shadowQ T b).order l.value :=
  ⟨T.clauseC.torsion_spec, shadowQ_order_coprime T b⟩

/-- The actual clause-(c) kernel-field identification present in the source.
This is the antecedent of the missing l-th power bridge. -/
def actual_kernel_field_data :
    T.arithmetic.K ≃ₐ[T.arithmetic.F]
      T.arithmetic.curve.galoisLTorsionKernelField l T.clauseC.torsion_basis :=
  T.clauseC.kernel_field_identification

/-- Square source gives the 2-part. -/
theorem two_dvd_order_of_squareSource (h : S2190QSquareSource T b) :
    S2129TwoDivOrder T b := by
  obtain ⟨s, hs⟩ := h
  exact order_dvd_of_pow_eq (sectionQ T b) s 2 (by norm_num) hs

/-- l-th power source gives the l-part of the order. -/
theorem l_dvd_order_of_lthPowerSource (h : S2190QLthPowerSource T b) :
    l.value ∣ (sectionQ T b).order := by
  obtain ⟨r, hr⟩ := h
  exact order_dvd_of_pow_eq (sectionQ T b) r l.value l.prime.pos hr

/-- l-th power source gives the ramification divisibility. -/
theorem l_dvd_ramification_of_lthPowerSource (h : S2190QLthPowerSource T b) :
    S2129LDivRamification T b :=
  l_dvd_ramification_of_l_dvd_order T b (l_dvd_order_of_lthPowerSource T b h)

/-- The two paper source conditions imply the two root divisibilities. -/
theorem rootNecessary_of_halfRootSource (h : S2190HalfRootSource T b) :
    S2129RootNecessary T b :=
  ⟨l_dvd_ramification_of_lthPowerSource T b h.2,
    two_dvd_order_of_squareSource T b h.1⟩

/-- The two paper source conditions imply 2l ∣ ord(q_v). -/
theorem twoLDivOrder_of_halfRootSource (h : S2190HalfRootSource T b) :
    S2129TwoLDivOrder T b :=
  (twoL_dvd_order_iff_order_and_two T b).mpr
    ⟨l_dvd_order_of_lthPowerSource T b h.2,
      two_dvd_order_of_squareSource T b h.1⟩

/-- The exact bridge form: the missing 2-torsion-to-square bridge, together
with the l-th power source condition, gives the two S2129 statements. -/
theorem rootNecessary_of_torsion23_bridge_and_lth
    (h2 : S2190TwoTorsionToQSqrtBridge T b)
    (hl : S2190QLthPowerSource T b) :
    S2129RootNecessary T b :=
  rootNecessary_of_halfRootSource T b
    ⟨h2 T.clauseC.torsion23_rational, hl⟩

/-- **The exact missing source bridges, consumed on the actual clause data.**
The 2-torsion bridge is applied to clause (c)'s rational 2*3-torsion; the
l-th power bridge is applied to clause (c)'s torsion basis and kernel-field
identification.  The conclusion is exactly the two S2129 divisibility
statements. -/
theorem rootNecessary_of_source_bridges
    (h2 : S2190TwoTorsionToQSqrtBridge T b)
    (hl : S2190KernelFieldToQLthPowerBridge T b) :
    S2129RootNecessary T b :=
  rootNecessary_of_halfRootSource T b
    ⟨h2 T.clauseC.torsion23_rational,
      hl T.clauseC.torsion_basis T.clauseC.kernel_field_identification⟩

/-! ## 4. The paper root implies both source conditions

The two conditions are intermediate statements of the paper's construction:
from a completion 2l-th root of q_v, the l-th power of the root is a square
root of q_v, and its square is an l-th root. -/

theorem squareRootSource_of_paperRoot (h : paperOtriRootMissing T b) :
    S2190QSquareSource T b := by
  obtain ⟨r, hr⟩ := (paperOtriRootMissing_iff (T := T) (b := b)).mp h
  refine ⟨(r : Completion (sectionKPlace T b)) ^ l.value, ?_⟩
  rw [← pow_mul, Nat.mul_comm l.value 2, hr]

theorem lthPowerSource_of_paperRoot (h : paperOtriRootMissing T b) :
    S2190QLthPowerSource T b := by
  obtain ⟨r, hr⟩ := (paperOtriRootMissing_iff (T := T) (b := b)).mp h
  refine ⟨(r : Completion (sectionKPlace T b)) ^ 2, ?_⟩
  rw [← pow_mul]
  exact hr

/-- The paper root supplies the two new source conditions. -/
theorem halfRootSource_of_paperRoot (h : paperOtriRootMissing T b) :
    S2190HalfRootSource T b :=
  ⟨squareRootSource_of_paperRoot T b h, lthPowerSource_of_paperRoot T b h⟩

/-! ## 5. The recorded source arithmetic does not force the conditions

The envelope below is exactly the arithmetic content recorded by S1413: two
positive factors e, m with m prime to l, of which ord(q_v) is the product.
Both divisibility conditions fail inside this envelope, so they are genuine
additional source inputs (this is the section-place form of S467).  These are
countermodels for the recorded order arithmetic; no formal independence from
the full clause structure is claimed. -/

/-- The recorded order-law envelope: e = eSource, m = ord(shadowQ). -/
def S2190OrderEnvelope (e m : Nat) : Prop :=
  0 < e ∧ 0 < m ∧ Nat.Coprime m l.value

/-- The envelope does not force l ∣ e: e = m = 1 satisfies it. -/
theorem orderEnvelope_not_force_l :
    ∃ e m : Nat, S2190OrderEnvelope (l := l) e m ∧ ¬ l.value ∣ e := by
  refine ⟨1, 1, ⟨by norm_num, by norm_num, Nat.coprime_one_left _⟩, ?_⟩
  exact l.prime.not_dvd_one

/-- The envelope does not force 2l ∣ e * m, even after l ∣ e:
e = l, m = 1 gives ord = l. -/
theorem orderEnvelope_not_force_twoL :
    ∃ e m : Nat, S2190OrderEnvelope (l := l) e m ∧ l.value ∣ e ∧
      ¬ 2 * l.value ∣ e * m := by
  refine ⟨l.value, 1, ⟨l.prime.pos, by norm_num, Nat.coprime_one_left _⟩,
    dvd_rfl, ?_⟩
  simp only [mul_one]
  intro h
  have hle : 2 * l.value ≤ l.value := Nat.le_of_dvd l.prime.pos h
  have hge : 5 ≤ l.value := l.ge_five
  omega

/-- The envelope does not force l ∣ e from the 2-part: e = 1, m = 2 has even
e * m but odd e. -/
theorem orderEnvelope_two_not_force_l :
    ∃ e m : Nat, S2190OrderEnvelope (l := l) e m ∧ 2 ∣ e * m ∧
      ¬ l.value ∣ e := by
  refine ⟨1, 2, ⟨by norm_num, by norm_num, ?_⟩, by norm_num, ?_⟩
  · exact Nat.coprime_two_left.mpr l.odd
  · exact l.prime.not_dvd_one

/-! ## 6. The S2032 local model: the conditions are exact divisibility

S2032's Q_5 model has q_v = 5 ^ paperQVOrder and records only
0 < paperQVOrder.  In that model, an n-th root of 5 ^ m exists exactly when
n ∣ m; in particular the square condition is 2 ∣ m, the l-th power condition
is l ∣ m, and the 2l-th root condition is 2l ∣ m.  Thus the proposed source
conditions are substantive divisibility conditions, not a weakness of the
formulation. -/

/-- In the Q_5 model, 5 ^ m has an n-th root exactly when n ∣ m. -/
theorem padic_five_pow_root_iff (n m : Nat) (hn : 0 < n) :
    (∃ r : ℚ_[5], r ^ n = (5 : ℚ_[5]) ^ m) ↔ n ∣ m := by
  constructor
  · rintro ⟨r, hr⟩
    have hn0 : n ≠ 0 := hn.ne'
    have hfive : (5 : ℚ_[5]) ≠ 0 := by norm_num
    have hfivepow : (5 : ℚ_[5]) ^ m ≠ 0 := pow_ne_zero _ hfive
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hn0] at hr
      exact hfivepow hr.symm
    have hnorm := congrArg norm hr
    have hnormR : ‖(5 : ℚ_[5]) ^ m‖ = (5 : ℝ) ^ (-(m : ℤ)) := by
      rw [show (5 : ℚ_[5]) = ((5 : ℕ) : ℚ_[5]) by norm_num, Padic.norm_p_pow]
      norm_num
    rw [hnormR] at hnorm
    rw [norm_pow, Padic.norm_eq_zpow_neg_valuation hr0] at hnorm
    rw [show ((5 : ℕ) : ℝ) = (5 : ℝ) by norm_num] at hnorm
    have hpow : ((5 : ℝ) ^ (-r.valuation)) ^ (n : ℕ) =
        (5 : ℝ) ^ ((-r.valuation) * (n : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
    rw [hpow] at hnorm
    have hexp := (zpow_right_inj₀ (a := (5 : ℝ)) (by norm_num) (by norm_num)).mp hnorm
    have hprod : r.valuation * (n : ℤ) = (m : ℤ) := by linarith
    have hdvd : (n : ℤ) ∣ (m : ℤ) :=
      ⟨r.valuation, by simpa [mul_comm] using hprod.symm⟩
    exact_mod_cast hdvd
  · rintro ⟨k, hk⟩
    refine ⟨(5 : ℚ_[5]) ^ k, ?_⟩
    rw [← pow_mul, Nat.mul_comm k n, ← hk]

/-- In the S2032 model the square condition is exactly 2 ∣ m. -/
theorem s2032_q5_square_iff (m : Nat) :
    (∃ r : ℚ_[5], r ^ 2 = (5 : ℚ_[5]) ^ m) ↔ 2 ∣ m :=
  padic_five_pow_root_iff 2 m (by norm_num)

/-- In the S2032 model the l-th power condition is exactly l ∣ m. -/
theorem s2032_q5_lthPower_iff (m : Nat) :
    (∃ r : ℚ_[5], r ^ l.value = (5 : ℚ_[5]) ^ m) ↔ l.value ∣ m :=
  padic_five_pow_root_iff l.value m l.prime.pos

/-- In the S2032 model the 2l-th root condition is exactly 2l ∣ m. -/
theorem s2032_q5_twoL_iff (m : Nat) :
    (∃ r : ℚ_[5], r ^ (2 * l.value) = (5 : ℚ_[5]) ^ m) ↔
      2 * l.value ∣ m :=
  padic_five_pow_root_iff (2 * l.value) m
    (Nat.mul_pos (by norm_num) l.prime.pos)

/-- S2032's actual model order is only known to be positive; the model's
square condition is the divisibility 2 ∣ paperQVOrder. -/
theorem s2032_model_square_condition (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    0 < paperQVOrder D b ∧
      ((∃ r : ℚ_[5], r ^ 2 = (5 : ℚ_[5]) ^ paperQVOrder D b) ↔
        2 ∣ paperQVOrder D b) :=
  ⟨paperQVOrder_pos D b, s2032_q5_square_iff (paperQVOrder D b)⟩

/-! ## 7. S2040 and S2057 do not add the missing arithmetic -/

/-- The S2040 root field is exactly the missing paper completion root (rfl). -/
theorem s2040_root_attachment_is_paperRoot :
    (s2040PaperOtriAttachmentActual (l := l) T b).qv_root_attachment =
      paperOtriRootMissing T b := rfl

/-- If the S2040 attachment's root field were supplied, it would give the two
new source conditions; otherwise S2040 contributes no arithmetic. -/
theorem s2040_attachment_forces_halfRootSource
    (h : (s2040PaperOtriAttachmentActual (l := l) T b).qv_root_attachment) :
    S2190HalfRootSource T b := by
  rw [s2040_root_attachment_is_paperRoot] at h
  exact halfRootSource_of_paperRoot T b h

/-- The S2057 Theta-pilot root is a root in the finite root-stack extension:
its 2l-th power is the finite q-section, not an element of the completion at
sectionKPlace. -/
theorem s2057_finite_root_pow :
    (s2057RootStackThetaPilotObject (l := l) T b).root ^ (2 * l.value) =
      (s2057RootStackThetaPilotObject (l := l) T b).qSection :=
  (s2057RootStackThetaPilotObject (l := l) T b).root_pow

/-- Its real scalar is a 2l-th root of the F-side q-norm; this is a real
scalar equation, not a completion root of the K-side sectionQ. -/
theorem s2057_real_root_pow :
    (s2057RootStackThetaPilotObject (l := l) T b).rootStackTheta ^ (2 * l.value) =
      paperQNorm (l := l) T b :=
  (s2057RootStackThetaPilotObject (l := l) T b).rootStackTheta_pow

/-- The F-side qVFamily has order prime to l, so it cannot be the paper q_v
with the required l-divisibility; S2057's finite root therefore cannot supply
either source condition for sectionQ. -/
theorem s2057_fside_order_coprime :
    Nat.Coprime (qVFamily T b).order l.value :=
  qVFamily_order_coprime T b

/-- S342/S2092: the F-side qVFamily has no completion 2l-th root at all. -/
theorem s2057_no_completionRoot :
    ¬ Nonempty (TwoLthRootData T b) :=
  s2057_completion_root_impossible T b

/-! ## 8. The missing source conditions, and the minimal arithmetic form -/

/-- The exact new paper source conditions.  This is the paper-faithful
sufficient input: the two half roots of q_v which Example 3.2(iv) derives
from clauses (b) and (c) through the Tate uniformization. -/
def S2190NewPaperSourceConditions : Prop := S2190HalfRootSource T b

/-- With the new paper source conditions, both S2129 divisibility conditions
hold. -/
theorem s2190_source_conditions_suffice
    (h : S2190NewPaperSourceConditions T b) : S2129RootNecessary T b :=
  rootNecessary_of_halfRootSource T b h

/-- With the new paper source conditions, 2l ∣ ord(q_v). -/
theorem s2190_source_conditions_suffice_twoL
    (h : S2190NewPaperSourceConditions T b) : S2129TwoLDivOrder T b :=
  twoLDivOrder_of_halfRootSource T b h

/-- The minimal arithmetic form of the missing source data: the two
divisibility conditions themselves.  This definition adds no hypothesis and
changes no target; it records what must be supplied if one does not formalize
the half roots. -/
def S2190MinimalArithmeticSource : Prop :=
  S2129LDivRamification T b ∧ S2129TwoDivOrder T b

/-- The minimal arithmetic form is definitionally the S2129 necessary
condition. -/
theorem minimalArithmeticSource_iff_rootNecessary :
    S2190MinimalArithmeticSource T b ↔ S2129RootNecessary T b := Iff.rfl

/-! ## 9. Axiom audit (in-file, so that one run is the verification) -/

#print axioms eSource_pos
#print axioms current_source_arithmetic
#print axioms l_dvd_ramification_of_l_dvd_order
#print axioms two_dvd_order_iff_source_split
#print axioms order_dvd_of_pow_eq
#print axioms two_dvd_order_of_squareSource
#print axioms l_dvd_order_of_lthPowerSource
#print axioms l_dvd_ramification_of_lthPowerSource
#print axioms rootNecessary_of_halfRootSource
#print axioms twoLDivOrder_of_halfRootSource
#print axioms rootNecessary_of_torsion23_bridge_and_lth
#print axioms actual_clause_data
#print axioms actual_kernel_field_data
#print axioms rootNecessary_of_source_bridges
#print axioms squareRootSource_of_paperRoot
#print axioms lthPowerSource_of_paperRoot
#print axioms halfRootSource_of_paperRoot
#print axioms orderEnvelope_not_force_l
#print axioms orderEnvelope_not_force_twoL
#print axioms orderEnvelope_two_not_force_l
#print axioms padic_five_pow_root_iff
#print axioms s2032_q5_square_iff
#print axioms s2032_q5_lthPower_iff
#print axioms s2032_q5_twoL_iff
#print axioms s2032_model_square_condition
#print axioms s2040_root_attachment_is_paperRoot
#print axioms s2040_attachment_forces_halfRootSource
#print axioms s2057_finite_root_pow
#print axioms s2057_real_root_pow
#print axioms s2057_fside_order_coprime
#print axioms s2057_no_completionRoot
#print axioms s2190_source_conditions_suffice
#print axioms s2190_source_conditions_suffice_twoL

end LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual
end