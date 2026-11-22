import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Tactic

/-!
# A772 scaled θ-hull construction on the actual S1902 carrier (shehdd)

Real construction (no toy carrier): for a capsule scale `k` the scaled θ-hull is
the product of the actual S1915 full-region balls divided by `p_b^k`:

`scaledHullRadius T b k = rootImageRadius T b / p_b^k`,
`scaledThetaHull T k = ⊓_b closedBall 0 (scaledHullRadius T b k)`,

on the actual carrier `S1902Carrier T`, with the real Haar `rootExtensionProductHaar`.

Proved here (pure arithmetic/region level):
1. `scaledThetaHull_zero`: `k=0` is the actual `fullRegion`;
2. `scaledHullRadius_pos/le`: positivity and containment in the full region;
3. `scaledClosedForm_eq`:
   `1 + Σ_b d_b·log(rootImageRadius_b/p_b^k) = s1915ClosedForm - k·Σ_b d_b·log p_b`;
4. procession average over capsules `i ↦ (i+1)^2`:
   `average_i scaledClosedForm((i+1)^2) = s1915ClosedForm - sFactorFin(n)·Σ_b d_b log p_b`
   (`sFactorFin n = (Σ_{i<n}(i+1)^2)/n`).

Remaining analytic input (listed, NOT assumed): the iterated Haar scaling law
`rootExtensionProductHaar (scaledThetaHull k) = (∏_b primeFactor_b^k) · rootExtensionProductHaar fullRegion`
and its log form; this needs the iterated `rootPrime_smul_measure`/`prime_smul_closedBall`
lemmas and is the exact gap for the paper θ-hull volume.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Scaled θ-hull radius: `rootImageRadius_b / p_b^k`. -/
noncomputable def scaledHullRadius (b : Bad (nativePlaceSelection T)) (k : ℕ) : ℝ :=
  (rootImageRadius T b : ℝ) / (qVFamTensorP T b : ℝ) ^ k

theorem scaledHullRadius_pos (b : Bad (nativePlaceSelection T)) (k : ℕ) :
    0 < scaledHullRadius T b k := by
  unfold scaledHullRadius
  have hp : (0 : ℝ) < (qVFamTensorP T b : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
  exact div_pos (s1915_rootImageRadius_pos T b) (pow_pos hp k)

theorem scaledHullRadius_le_rootImageRadius (b : Bad (nativePlaceSelection T)) (k : ℕ) :
    scaledHullRadius T b k ≤ (rootImageRadius T b : ℝ) := by
  unfold scaledHullRadius
  apply div_le_self (s1915_rootImageRadius_pos T b).le
  have hp : (1 : ℝ) ≤ (qVFamTensorP T b : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt.le
  exact one_le_pow₀ hp

/-- The actual scaled θ-hull region on the S1902 product carrier. -/
noncomputable def scaledThetaHull (k : ℕ) : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (0 : rootNormedExtension T b)
    (scaledHullRadius T b k))

theorem scaledThetaHull_zero : scaledThetaHull T 0 = fullRegion T := by
  unfold scaledThetaHull fullRegion scaledHullRadius
  simp

theorem scaledThetaHull_subset_full (k : ℕ) : scaledThetaHull T k ⊆ fullRegion T := by
  intro x hx b _
  have hx' := hx b (Set.mem_univ b)
  rw [Metric.mem_closedBall] at hx' ⊢
  exact le_trans hx' (scaledHullRadius_le_rootImageRadius T b k)

/-- Where `d_b = [K_b:Q_p]`, the q-side sum `S = Σ_b d_b log p_b`. -/
noncomputable def qLogSum : ℝ :=
  ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : ℝ) * Real.log (qVFamTensorP T b : ℝ)

/-- The scaled closed form: `1 + Σ_b d_b·log(rootImageRadius_b/p_b^k)`. -/
noncomputable def scaledClosedFormR (k : ℝ) : ℝ :=
  1 + ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : ℝ) *
      (Real.log (rootImageRadius T b : ℝ) - k * Real.log (qVFamTensorP T b : ℝ))

/-- **Scaled closed form identity**: `s1915ClosedForm - k·S`. -/
theorem scaledClosedFormR_eq (k : ℝ) :
    scaledClosedFormR T k = s1915ClosedForm T - k * qLogSum T := by
  unfold scaledClosedFormR s1915ClosedForm qLogSum
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      (s1915LocalDegree T b : ℝ) *
        (Real.log (rootImageRadius T b : ℝ) - k * Real.log (qVFamTensorP T b : ℝ)) =
      (s1915LocalDegree T b : ℝ) * Real.log (rootImageRadius T b : ℝ) -
        k * ((s1915LocalDegree T b : ℝ) * Real.log (qVFamTensorP T b : ℝ)) := by
    intro b; ring
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- The procession factor `(Σ_{i<n}(i+1)^2)/n` (the lana capsule average). -/
noncomputable def sFactorFin (n : ℕ) : ℝ :=
  (∑ i : Fin n, (((i : ℝ) + 1) ^ 2)) / (n : ℝ)

/-- **Procession average of the scaled closed form**: for `n` capsules with
scale `(i+1)^2`, the uniform average is `s1915ClosedForm - sFactorFin n · S`. -/
theorem processionAverage_scaledClosedForm (n : ℕ) (hn : 0 < n) :
    (∑ i : Fin n, scaledClosedFormR T (((i : ℝ) + 1) ^ 2)) / (n : ℝ) =
      s1915ClosedForm T - sFactorFin n * qLogSum T := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hterm : ∀ i : Fin n, scaledClosedFormR T (((i : ℝ) + 1) ^ 2) =
      s1915ClosedForm T - (((i : ℝ) + 1) ^ 2) * qLogSum T := by
    intro i; rw [scaledClosedFormR_eq]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  unfold sFactorFin
  rw [← Finset.sum_mul]
  field_simp [hnR]

structure ScaledRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def scaledRows : List ScaledRow :=
  [ ⟨"carrier", "S1902Carrier T (actual product carrier)", "REAL_CARRIER"⟩
  , ⟨"region", "scaledThetaHull k = product of closedBall(rootImageRadius_b/p_b^k)", "DEF"⟩
  , ⟨"k=0", "scaledThetaHull 0 = fullRegion", "PROVED"⟩
  , ⟨"closed form", "scaledClosedFormR k = s1915ClosedForm - k*S", "PROVED"⟩
  , ⟨"procession average", "avg_i scaledClosedForm((i+1)^2) = s1915ClosedForm - sFactorFin(n)*S", "PROVED"⟩
  , ⟨"analytic missing", "iterated Haar scaling law for scaledThetaHull (rootPrime_smul_measure^m / prime_smul_closedBall^m)", "SINGLE_GAP"⟩
  , ⟨"scope", "no toy carrier; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem scaledRows_length : scaledRows.length = 7 := rfl

theorem scaledRows_has_gap :
    scaledRows.any (fun r => r.status = "SINGLE_GAP") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual.scaledThetaHull_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual.scaledClosedFormR_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual.processionAverage_scaledClosedForm
