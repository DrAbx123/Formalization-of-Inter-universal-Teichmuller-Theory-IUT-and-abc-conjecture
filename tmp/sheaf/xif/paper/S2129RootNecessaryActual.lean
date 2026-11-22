import tmp.sheaf.xif.paper.S2092PaperOtriActual
import tmp.sheaf.xif.paper.S2040PaperOtriFromS2092Actual
import tmp.sheaf.xif.paper.S2032R6GeneratorActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

/-!
# S2129: the divisibility conditions forced by the paper completion root, and
what the current source data actually supply

S2092 proves the two necessary conditions for the paper root
q_v^{1/(2l)} in O^⊿(T_{X_v}) ≅ O^⊿_{K_v} (IUT I, Example 3.2(iv)):

* l ∣ eSource, where eSource is the ramification index of the
  section-designated K-place over its F-shadow (S1413);
* 2l ∣ ord(q_v), where q_v = sectionQ is the completion image of the
  clause-B q-parameter at that place.

This file audits whether the current source data already imply those
divisibility conditions.  It does not construct a root, does not add an
axiom, and does not change the target: the missing datum remains exactly
S1413's SectionTwoLRoot / S2092's paperOtriRootMissing, which is also the
qv_root_attachment field of S2040's actual paper carrier.

## The audit result

The current source data do not prove either condition.  The audit of the
concrete files is:

1. eSource is fkDescentSectionRamificationIndex, the ramification index of
   the restriction-section lift sectionFiniteLift at the bad moduli place.
   SourcePlaceSelection supplies only V_mod_bad, its odd residue
   characteristic and nonemptiness; the section itself is the canonical
   restriction section.  The source clauses (a)--(f) constrain residue
   characteristics, q-orders, the l-torsion kernel field and the Tate
   comparisons, but none of them constrains the ramification index of the
   selected K-place over its F-shadow.  The only unconditional arithmetic
   theorem linking eSource to the q-order is the order law
   ord(q_v) = eSource * ord(shadowQ) (S1413); ord(shadowQ) is only known
   to be coprime to l, and the only other theorem producing l ∣ eSource is
   the root-forcing implication itself (l_dvd_ramification_of_root).  S467
   proves that the factorization plus coprimality does not imply 2l ∣ ord;
   S472 names the analogous missing inputs TwoTorsionToQOrderParityGap and
   KLocalRamificationDivisibleByLGap for the qVFamilyK lift.  For the
   section place the corresponding inputs are 2 ∣ ord(shadowQ) and
   l ∣ eSource.

2. 2l ∣ ord(q_v) is *not* a consequence of the recorded order law.  In fact
   l ∣ eSource ↔ l ∣ ord(q_v) (because ord(shadowQ) is coprime to l), so
   the l-part is exactly l ∣ eSource; the factor 2 is a genuinely
   separate parity input.  It can come from 2 ∣ eSource or from
   2 ∣ ord(shadowQ); neither is proved.  S1284 already proves the analogous
   exact reduction for the qVFamilyK lift, and S1281 proves the
   root-forcing/refutation there; the present file is the section-place
   version at the paper's designated K-place.

3. The S2032 / Theta data do not supply the conditions either.  S2032's
   local model only proves 0 < paperQVOrder and q_v = 5 ^ paperQVOrder;
   positivity does not imply 2l ∣ paperQVOrder.  In that concrete model, a
   2l-th root of 5 ^ m in Q_5 exists exactly when 2l ∣ m (proved
   below), showing the divisibility is a real obstruction and not a defect of
   the formulation.  The Theta-side root hodgeTwoLthRoot is an
   algebraic-closure root of the F-side qVFamily at qVPlace; S342/S2092
   prove that this F-side q has *no* completion root, so it cannot be the
   paper root at sectionKPlace.

4. S2040 does not add a proof: s2040PaperOtriAttachmentActual stores
   exactly paperOtriRootMissing in its root field (proved by rfl below).

### What each audited file supplies

| file | supplies | does not supply |
|---|---|---|
| S1413 | sectionFPlace/sectionKPlace, sectionQ, order law, valuation/norm laws, root obstruction | no value or divisibility of eSource; no parity of shadowQ.order |
| S2032 | local O^◃ model, q_v = 5 ^ paperQVOrder, realified value | only 0 < paperQVOrder; no divisibility by 2l |
| S2092 | paperOtri/paperQV/O^×mu attachment; root implies l ∣ eSource and 2l ∣ ord | no root, no source divisibility |
| S2040 | root field = paperOtriRootMissing | no proof of that field |
| Theta (hodgeTwoLthRoot) | algebraic-closure root of the F-side qVFamily at qVPlace | not a completion root; S342 excludes one at that place |

The clause-C 2*3-torsion rationality is actual, but no theorem in the tree
turns it into a parity statement for the q-order; S472 records exactly this
missing implication for the qVFamily lift.

## Exact source conditions that would make the root reachable

The root target can only be reachable if both

* l ∣ eSource (the local ramification divisibility at the paper's designated
  section K-place), and
* 2 ∣ ord(q_v) (equivalently 2 ∣ eSource or 2 ∣ ord(shadowQ))

hold.  If either fails, the root target is *refutable*, not merely unproved
(not_root_of_not_l_dvd, not_root_of_not_twoL_dvd).  Even when both hold,
the completion root itself is still missing: order divisibility is necessary
but not sufficient (S472, S1449).  The paper's actual existence assertion for
q_v^{1/(2l)} (IUT I, Example 3.2(iv)) is a separate source input, not
derivable from the current clauses.

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
assumption-only gate is used.
-/

namespace LeanFormal.IUT.XiFPaper.S2129RootNecessaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2092PaperOtriActual
open LeanFormal.IUT.XiFPaper.S2040PaperOtriFromS2092Actual
open LeanFormal.IUT.XiFPaper.S2040S2057InterfaceActual
open LeanFormal.IUT.XiFPaper.S2032R6GeneratorActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual

universe u

local instance s2129FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The two necessary conditions, by name -/

/-- The l-part of the root obstruction at the paper's designated K-place:
l divides the source section's ramification index. -/
def S2129LDivRamification : Prop := l.value ∣ eSource T b

/-- The 2-part of the root obstruction: the K-side order is even. -/
def S2129TwoDivOrder : Prop := 2 ∣ (sectionQ T b).order

/-- The full order obstruction 2l ∣ ord(q_v). -/
def S2129TwoLDivOrder : Prop := 2 * l.value ∣ (sectionQ T b).order

/-- The two arithmetic conditions that a completion root forces. -/
def S2129RootNecessary : Prop :=
  S2129LDivRamification T b ∧ S2129TwoDivOrder T b

/-- A completion root forces l ∣ eSource (S2092/S1413). -/
theorem root_forces_l_dvd (h : paperOtriRootMissing T b) :
    S2129LDivRamification T b := by
  rcases (paperOtriRootMissing_iff (T := T) (b := b)).mp h with ⟨r, hr⟩
  exact paperOtriRoot_forces_l_dvd_ramification T b r hr

/-- A completion root forces 2l ∣ ord(q_v) (S2092/S1413). -/
theorem root_forces_twoL_dvd (h : paperOtriRootMissing T b) :
    S2129TwoLDivOrder T b := by
  rcases (paperOtriRootMissing_iff (T := T) (b := b)).mp h with ⟨r, hr⟩
  exact paperOtriRoot_forces_twoL_dvd_order T b r hr

/-- A completion root forces the 2-part separately. -/
theorem root_forces_two_dvd (h : paperOtriRootMissing T b) :
    S2129TwoDivOrder T b :=
  Nat.dvd_trans ⟨l.value, by ring⟩ (root_forces_twoL_dvd T b h)

/-- **The root target forces exactly the two arithmetic conditions.** -/
theorem root_forces_necessary (h : paperOtriRootMissing T b) :
    S2129RootNecessary T b :=
  ⟨root_forces_l_dvd T b h, root_forces_two_dvd T b h⟩

/-! ## 2. The exact arithmetic reduction of 2l ∣ ord(q_v) -/

/-- Since ord(shadowQ) is prime to l, the l-divisibility of the K-side
order is exactly the l-divisibility of eSource. -/
theorem l_dvd_order_iff_l_dvd_ramification :
    l.value ∣ (sectionQ T b).order ↔ S2129LDivRamification T b := by
  constructor
  · intro h
    have her : l.value ∣ eSource T b * (shadowQ T b).order := by
      rwa [sectionQ_order] at h
    exact (shadowQ_order_coprime T b).symm.dvd_of_dvd_mul_right her
  · intro h
    rw [sectionQ_order]
    exact dvd_mul_of_dvd_left h _

/-- 2l ∣ ord is exactly l ∣ ord together with 2 ∣ ord, because 2 and l
are coprime. -/
theorem twoL_dvd_order_iff_order_and_two :
    S2129TwoLDivOrder T b ↔
      l.value ∣ (sectionQ T b).order ∧ S2129TwoDivOrder T b := by
  constructor
  · intro h
    exact ⟨Nat.dvd_trans ⟨2, by ring⟩ h, Nat.dvd_trans ⟨l.value, by ring⟩ h⟩
  · rintro ⟨hl, h2⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.coprime_two_left.mpr l.odd) h2 hl

/-- The 2-part splits into the two source-level alternatives: the
ramification index is even, or the F-side shadow order is even. -/
theorem two_dvd_order_iff :
    S2129TwoDivOrder T b ↔
      2 ∣ eSource T b ∨ 2 ∣ (shadowQ T b).order := by
  rw [S2129TwoDivOrder, sectionQ_order]
  exact Nat.prime_two.dvd_mul

/-- **The exact source conditions.**  2l ∣ ord(q_v) holds iff the section
ramification index is divisible by l and either the ramification index or the
F-side q-order is even.  This is the precise content the current source data
must supply. -/
theorem twoL_dvd_order_iff_ramification_and_two :
    S2129TwoLDivOrder T b ↔
      S2129LDivRamification T b ∧
        (2 ∣ eSource T b ∨ 2 ∣ (shadowQ T b).order) := by
  rw [twoL_dvd_order_iff_order_and_two, two_dvd_order_iff,
    l_dvd_order_iff_l_dvd_ramification]

/-- The two named conditions are equivalent to the single condition
2l ∣ ord(q_v). -/
theorem rootNecessary_iff_twoL :
    S2129RootNecessary T b ↔ S2129TwoLDivOrder T b := by
  rw [S2129RootNecessary, twoL_dvd_order_iff_order_and_two,
    l_dvd_order_iff_l_dvd_ramification]

/-! ## 3. The recorded order data alone do not imply the conditions

The only source-level arithmetic of the section place recorded in S1413 is

ord(q_v) = eSource * ord(shadowQ) with Coprime ord(shadowQ) l.

The next two witnesses show that this data is satisfied both when the
conclusions fail and when the 2-part fails.  Hence the two divisibility
conditions are genuine additional source conditions, not consequences of the
recorded order law.  (The witnesses are abstract in e m; e stands for
eSource and m for ord(shadowQ).) -/

/-- The recorded order data do not force l ∣ eSource: e = m = 1 satisfies
the coprimality and violates the conclusion. -/
theorem order_law_counterexample_l_not_dvd (l : PrimeGeFive) :
    ∃ e m : Nat, Nat.Coprime m l.value ∧ ¬ l.value ∣ e := by
  refine ⟨1, 1, Nat.coprime_one_left _, ?_⟩
  exact l.prime.not_dvd_one

/-- Even after l ∣ eSource, the recorded order data do not force the 2-part:
e = l, m = 1 gives ord = l, which is not divisible by 2l. -/
theorem order_law_counterexample_l_dvd_not_twoL (l : PrimeGeFive) :
    ∃ e m : Nat, Nat.Coprime m l.value ∧ l.value ∣ e ∧
      ¬ 2 * l.value ∣ e * m := by
  refine ⟨l.value, 1, Nat.coprime_one_left _, dvd_rfl, ?_⟩
  simp only [mul_one]
  intro h
  have hle : 2 * l.value ≤ l.value := Nat.le_of_dvd l.prime.pos h
  have hge : 5 ≤ l.value := l.ge_five
  omega

/-- The abstract implication is false even with m coprime to l (the S467
counterexample, restated here for the section-place order law). -/
theorem not_uniform_twoL_dvd_factorization :
    ¬ (∀ e m : Nat, Nat.Coprime m l.value → (2 * l.value) ∣ e * m) := by
  intro h
  have hd : (2 * l.value) ∣ (1 : Nat) * 1 :=
    h 1 1 (Nat.coprime_one_left l.value)
  have hone : 2 * l.value = 1 := Nat.dvd_one.mp (by simpa only [mul_one] using hd)
  have hge : 5 ≤ l.value := l.ge_five
  omega

/-! ## 4. The S2032 local model: positivity is not divisibility -/

/-- The only order fact S2032 records for its local q_v is positivity. -/
theorem s2032_order_pos (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    0 < paperQVOrder D b :=
  paperQVOrder_pos D b

/-- Positivity of the local order does not imply 2l-divisibility. -/
theorem s2032_order_divisibility_not_forced (l : PrimeGeFive) :
    ∃ m : Nat, 0 < m ∧ ¬ 2 * l.value ∣ m := by
  refine ⟨1, by norm_num, ?_⟩
  have hge : 5 ≤ l.value := l.ge_five
  intro h
  have hle : 2 * l.value ≤ 1 := Nat.le_of_dvd (by norm_num) h
  omega

/-- In the Q_5 model, if 2l ∣ m then 5 ^ m has a 2l-th root. -/
theorem s2032_q5_root_of_twoL_dvd (m : Nat) (h : 2 * l.value ∣ m) :
    ∃ r : ℚ_[5], r ^ (2 * l.value) = (5 : ℚ_[5]) ^ m := by
  obtain ⟨k, hk⟩ := h
  refine ⟨(5 : ℚ_[5]) ^ k, ?_⟩
  rw [← pow_mul, hk]
  ring

/-- Valuation obstruction in the Q_5 model: if 2l does not divide m,
then 5 ^ m has no 2l-th root in Q_5.  This is the concrete arithmetic
behind the necessary condition. -/
theorem padic_five_pow_no_twoL_root (m : Nat) (h : ¬ 2 * l.value ∣ m) :
    ¬ ∃ r : ℚ_[5], r ^ (2 * l.value) = (5 : ℚ_[5]) ^ m := by
  rintro ⟨r, hr⟩
  have h2l : 0 < 2 * l.value := Nat.mul_pos (by norm_num) l.prime.pos
  have hfive : (5 : ℚ_[5]) ≠ 0 := by norm_num
  have hfivepow : (5 : ℚ_[5]) ^ m ≠ 0 := pow_ne_zero _ hfive
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow h2l.ne'] at hr
    exact hfivepow hr.symm
  have hnorm := congrArg norm hr
  have hnormR : ‖(5 : ℚ_[5]) ^ m‖ = (5 : ℝ) ^ (-(m : ℤ)) := by
    rw [show (5 : ℚ_[5]) = ((5 : ℕ) : ℚ_[5]) by norm_num, Padic.norm_p_pow]
    norm_num
  rw [hnormR] at hnorm
  rw [norm_pow, Padic.norm_eq_zpow_neg_valuation hr0] at hnorm
  rw [show ((5 : ℕ) : ℝ) = (5 : ℝ) by norm_num] at hnorm
  have hpow : ((5 : ℝ) ^ (-r.valuation)) ^ (2 * l.value : ℕ) =
      (5 : ℝ) ^ ((-r.valuation) * (2 * l.value : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
    push_cast
    ring
  rw [hpow] at hnorm
  have hexp := (zpow_right_inj₀ (a := (5 : ℝ)) (by norm_num) (by norm_num)).mp hnorm
  have hprod : r.valuation * (2 * l.value : ℤ) = (m : ℤ) := by linarith
  have hdvd : (2 * l.value : ℤ) ∣ (m : ℤ) :=
    ⟨r.valuation, by simpa [mul_comm] using hprod.symm⟩
  have hdvdNat : 2 * l.value ∣ m := by exact_mod_cast hdvd
  exact h hdvdNat

/-- In the Q_5 model the 2l-th root exists exactly when 2l divides the
exponent. -/
theorem s2032_q5_root_iff_twoL_dvd (m : Nat) :
    (∃ r : ℚ_[5], r ^ (2 * l.value) = (5 : ℚ_[5]) ^ m) ↔
      2 * l.value ∣ m := by
  constructor
  · intro h
    by_contra hnot
    exact padic_five_pow_no_twoL_root (l := l) m hnot h
  · exact s2032_q5_root_of_twoL_dvd (l := l) m

/-- S2032's actual local q_v = 5 ^ paperQVOrder has no 2l-th root coming
from the model field Q_5 when 2l does not divide paperQVOrder.  The
algebraic-closure root always exists; this theorem concerns precisely the
Q_5-rational (hence model-field) root, i.e. the analogue of the paper's
requirement that the root lie in the specified completion. -/
theorem s2032_no_q5_root_of_not_twoL_dvd
    (D : S1895PaperInput) (b : (paperInput D).initial.badPlaces)
    (h : ¬ 2 * l.value ∣ paperQVOrder D b) :
    ¬ ∃ r : ℚ_[5],
        (algebraMap ℚ_[5] (AlgebraicClosure ℚ_[5]) r) ^ (2 * l.value) =
          (localOFieldQParameter D b : AlgebraicClosure ℚ_[5]) := by
  rintro ⟨r, hr⟩
  have hmap5 : algebraMap ℚ_[5] (AlgebraicClosure ℚ_[5]) (5 : ℚ_[5]) =
      (5 : AlgebraicClosure ℚ_[5]) := by
    rw [show (5 : ℚ_[5]) = ((5 : ℕ) : ℚ_[5]) by norm_num]
    rw [map_natCast]
    norm_num
  have hr' : algebraMap ℚ_[5] (AlgebraicClosure ℚ_[5]) (r ^ (2 * l.value)) =
      algebraMap ℚ_[5] (AlgebraicClosure ℚ_[5])
        ((5 : ℚ_[5]) ^ paperQVOrder D b) := by
    rw [map_pow, hr, localOFieldQParameter_coe, map_pow, hmap5]
  have hroot : r ^ (2 * l.value) = (5 : ℚ_[5]) ^ paperQVOrder D b :=
    (algebraMap ℚ_[5] (AlgebraicClosure ℚ_[5])).injective hr'
  exact padic_five_pow_no_twoL_root (l := l) (paperQVOrder D b) h ⟨r, hroot⟩

/-! ## 5. The Theta-side root is not the paper root -/

/-- The Theta-side hodgeTwoLthRoot is an algebraic-closure root of the
F-side qVFamily at qVPlace, not a completion root at the paper's
sectionKPlace. -/
theorem theta_root_is_algebraicClosure_root :
    hodgeTwoLthRoot T b ^ (2 * l.value) = qVAlgClosedUnit T b :=
  hodgeTwoLthRoot_pow T b

/-- The same F-side q has no completion root (S342/S2092).  Hence the
Theta-side algebraic-closure root cannot be substituted for
paperOtriRootMissing without changing the place and the target. -/
theorem theta_side_no_completionRoot :
    ¬ Nonempty (TwoLthRootData T b) :=
  no_Fside_completionRoot T b

/-! ## 6. S2040's target is unchanged -/

/-- The root field of S2040's actual paper carrier is exactly the missing
S2092/S1413 completion root. -/
theorem s2040_root_attachment_eq :
    (s2040PaperOtriAttachmentActual (l := l) T b).qv_root_attachment =
      paperOtriRootMissing (l := l) T b := rfl

/-- The S2040 root field is equivalent to the unchanged target. -/
theorem s2040_root_attachment_iff :
    (s2040PaperOtriAttachmentActual (l := l) T b).qv_root_attachment ↔
      paperOtriRootMissing (l := l) T b := Iff.rfl

/-! ## 7. Unreachability criteria

If either necessary condition fails, the root target is not merely unproved:
it is refutable.  These are the exact criteria for "the root is unreachable on
the current source data". -/

theorem not_root_of_not_l_dvd (h : ¬ S2129LDivRamification T b) :
    ¬ paperOtriRootMissing T b :=
  fun hroot => h (root_forces_l_dvd T b hroot)

theorem not_root_of_not_twoL_dvd (h : ¬ S2129TwoLDivOrder T b) :
    ¬ paperOtriRootMissing T b :=
  fun hroot => h (root_forces_twoL_dvd T b hroot)

theorem not_root_of_not_two_dvd (h : ¬ S2129TwoDivOrder T b) :
    ¬ paperOtriRootMissing T b :=
  fun hroot => h (root_forces_two_dvd T b hroot)

theorem not_root_of_not_necessary (h : ¬ S2129RootNecessary T b) :
    ¬ paperOtriRootMissing T b :=
  fun hroot => h (root_forces_necessary T b hroot)

/-! ## 8. Axiom audit (in-file, so that one run is the verification) -/

#print axioms root_forces_l_dvd
#print axioms root_forces_twoL_dvd
#print axioms root_forces_necessary
#print axioms l_dvd_order_iff_l_dvd_ramification
#print axioms twoL_dvd_order_iff_order_and_two
#print axioms twoL_dvd_order_iff_ramification_and_two
#print axioms rootNecessary_iff_twoL
#print axioms not_uniform_twoL_dvd_factorization
#print axioms s2032_order_pos
#print axioms s2032_q5_root_of_twoL_dvd
#print axioms padic_five_pow_no_twoL_root
#print axioms s2032_q5_root_iff_twoL_dvd
#print axioms s2032_no_q5_root_of_not_twoL_dvd
#print axioms theta_root_is_algebraicClosure_root
#print axioms theta_side_no_completionRoot
#print axioms s2040_root_attachment_eq
#print axioms not_root_of_not_l_dvd
#print axioms not_root_of_not_twoL_dvd
#print axioms not_root_of_not_necessary

end LeanFormal.IUT.XiFPaper.S2129RootNecessaryActual
end