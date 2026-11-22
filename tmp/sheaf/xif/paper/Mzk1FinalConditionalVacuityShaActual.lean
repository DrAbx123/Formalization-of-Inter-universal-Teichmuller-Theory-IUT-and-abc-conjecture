import tmp.sheaf.xif.paper.Mzk1FinalConditionalABCActual
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

/-!
# A703 CORRECTION (shehdd Sha): `hfull` is UNSATISFIABLE — `final_conditional_ABC` RETRACTED/VACUOUS

User audit (A703): at fixed `T` the hypothesis
`hfull : ∀ a b c, IsABCTriple a b c → a+b+c+1 = ∏_{b∈Bad} q_b^{e b}`
is **unsatisfiable**: `a+b+c+1` runs over all odd integers ≥ 5, and for a prime `P ∉ Bad`
with `P ≥ 5`, taking `a = 1`, `b = (P-3)/2`, `c = (P-1)/2` gives an ABC triple with
`a+b+c+1 = P`; the right-hand side only involves primes of the finite bad set, so `P`
would be one of them — contradiction.

Consequently the conditional chain `final_conditional_ABC` /
`natRadicalWeightBound_iff_ABC` is **RETRACTED as vacuous**, and the `N = a+b+c+1`
scaling is not the paper structure (paper bad primes are the primes of `abc`).  Old
files are kept as history; this file only ADDS the machine-checked vacuity theorem.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuityShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalABCActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- **Vacuity of `hfull`**: for fixed `T` and ANY exponent choice `eN`, the full-support
identity cannot hold for all ABC triples. -/
theorem hfull_unsatisfiable
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
      a + b + c + 1 = ∏ bBad : Bad (nativePlaceSelection T),
        (qVFamTensorP T bBad) ^ (eN a b c bBad)) := by
  intro hfull
  let S : Finset Nat :=
    Finset.univ.image (fun b : Bad (nativePlaceSelection T) => qVFamTensorP T b)
  obtain ⟨P, hPge, hPprime⟩ := Nat.exists_infinite_primes (max 5 (S.sum id + 1))
  have hP5 : 5 ≤ P := le_trans (le_max_left _ _) hPge
  have hPgtS : S.sum id < P := by
    have h1 : S.sum id + 1 ≤ P := le_trans (le_max_right _ _) hPge
    omega
  have hPnotS : P ∉ S := by
    intro hmem
    obtain ⟨b, -, hbEq⟩ := Finset.mem_image.mp hmem
    have hmemS : qVFamTensorP T b ∈ S :=
      Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
    have hb_le : qVFamTensorP T b ≤ S.sum id :=
      Finset.single_le_sum (s := S) (f := id) (fun i _ => Nat.zero_le i) hmemS
    rw [hbEq] at hb_le
    omega
  have hPne2 : P ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hPprime.odd_of_ne_two hPne2
  have hb_eq : (P - 3) / 2 = k - 1 := by omega
  have hc_eq : (P - 1) / 2 = k := by omega
  have hbpos : 0 < (P - 3) / 2 := by omega
  have htriple : IsABCTriple 1 ((P - 3) / 2) ((P - 1) / 2) := by
    refine ⟨by norm_num, hbpos, ?_, Nat.coprime_one_left _⟩
    rw [hb_eq, hc_eq]
    omega
  have hN : 1 + (P - 3) / 2 + (P - 1) / 2 + 1 = P := by
    rw [hb_eq, hc_eq]
    omega
  have hEq := hfull 1 ((P - 3) / 2) ((P - 1) / 2) htriple
  have hEqP : P = ∏ bBad : Bad (nativePlaceSelection T),
      (qVFamTensorP T bBad) ^ (eN 1 ((P - 3) / 2) ((P - 1) / 2) bBad) :=
    (hEq.symm.trans hN).symm
  have hdvd : P ∣ ∏ bBad : Bad (nativePlaceSelection T),
      (qVFamTensorP T bBad) ^ (eN 1 ((P - 3) / 2) ((P - 1) / 2) bBad) := by
    refine ⟨1, ?_⟩
    rw [mul_one]
    exact hEqP.symm
  obtain ⟨b0, -, hb0⟩ :=
    (hPprime.prime.dvd_finsetProd_iff
      (fun bBad => (qVFamTensorP T bBad) ^ (eN 1 ((P - 3) / 2) ((P - 1) / 2) bBad))).mp hdvd
  have hpq : P ∣ qVFamTensorP T b0 := hPprime.dvd_of_dvd_pow hb0
  have hqprime : Nat.Prime (qVFamTensorP T b0) := Fact.out
  have hPeq : P = qVFamTensorP T b0 :=
    (Nat.prime_dvd_prime_iff_eq hPprime hqprime).mp hpq
  exact hPnotS (Finset.mem_image.mpr ⟨b0, Finset.mem_univ b0, hPeq.symm⟩)

structure VacuityRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def vacuityRows : List VacuityRow :=
  [ ⟨"hfull unsatisfiable", "hfull_unsatisfiable (machine proof)", "GREEN"⟩
  , ⟨"final_conditional_ABC", "RETRACTED/VACUOUS (hypothesis hfull unsatisfiable)", "RETRACTED"⟩
  , ⟨"N = a+b+c+1 scaling", "not the paper structure (paper bad primes = primes of abc)", "RETRACTED"⟩
  , ⟨"old files", "kept as history; not changed", "HISTORY"⟩
  ]

theorem vacuityRows_length : vacuityRows.length = 4 := rfl

theorem vacuityRows_statuses_ok :
    vacuityRows.all (fun r =>
      r.status ∈ ["GREEN", "RETRACTED", "HISTORY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuityShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalVacuityShaActual.hfull_unsatisfiable
