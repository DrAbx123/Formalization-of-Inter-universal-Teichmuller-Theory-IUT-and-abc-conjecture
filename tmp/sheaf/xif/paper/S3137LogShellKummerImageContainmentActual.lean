import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse

/-!
# S3137: both Kummer images lie in the actual integral log-shell

IUT III, Definition 1.1, (i), (ii) (pp. 23--28), Proposition 1.2, (v), (bnon),
(cnon) (pp. 31--32), and Remark 1.2.2, (i), (ii) (p. 36):
the log-shell

  I_v = (p*_v)^(-1) * log_v(O^×_{K_v})  subset  K_v

contains the images of the Kummer isomorphisms associated to both the domain
and the codomain of the log-link, i.e. the integral monoid O^tri and the
logarithmic image log_v(O^×_{K_v}); this is what makes the log-shell a
container for both sides of the log-link (Proposition 1.2, (v), p. 55).

At the actual local field this file proves the second containment as a theorem
about the constructed analytic image:

  unitLog u ∈ integralLogShell K p  for every u : (O_K)^×,

using only the proved logarithm laws unitLog_pow and the actual shell
definition with the paper's factor logShellScale p (p for odd p, p^2 at p=2).
The first containment (O_K inside the shell) is the existing theorem
integers_subset_integralLogShell of LogarithmLocalInverse; the bundle below
states both containments together with the actual compactness of the shell and
of the logarithm image.  No arbitrary carrier, no surrogate, no sorry, no
axiom.  WRITE-ONLY; no local compile.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137LogShellKummerImageContainmentActual

open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K]
  {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

/-- The paper's factor logShellScale p is nonzero in the local field. -/
theorem logShellScale_cast_ne_zero : (logShellScale p : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := p)))

/-- The paper's factor is p for odd p and p^2 at p = 2 (Definition 1.1, (i)). -/
theorem logShellScale_eq_prime_or_prime_sq :
    logShellScale p = p ∨ logShellScale p = p ^ 2 := by
  unfold logShellScale
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- IUT III, Proposition 1.2, (v), (cnon) (pp. 31--32): the actual logarithm of
every integral unit lies in the actual integral log-shell. -/
theorem unitLog_mem_integralLogShell (u : (Integers K)ˣ) :
    unitLog (K := K) u ∈ integralLogShell (K := K) (p := p) := by
  change ∃ v : (Integers K)ˣ,
    (logShellScale p : K)⁻¹ * unitLog (K := K) v = unitLog (K := K) u
  refine ⟨u ^ logShellScale p, ?_⟩
  rw [unitLog_pow (p := p) u (logShellScale p)]
  exact inv_mul_cancel_left₀ (logShellScale_cast_ne_zero (K := K) (p := p))
    (unitLog (K := K) u)

/-- The whole actual logarithm image of the integral units is contained in the
actual integral log-shell. -/
theorem range_unitLog_subset_integralLogShell :
    Set.range (fun u : (Integers K)ˣ => unitLog (K := K) u) ⊆
      (integralLogShell (K := K) (p := p) : Set K) := by
  rintro _ ⟨u, rfl⟩
  exact unitLog_mem_integralLogShell (K := K) (p := p) u

/-- **IUT III, Proposition 1.2, (v), (bnon), (cnon), and Remark 1.2.2, (i),
(ii): the log-shell contains both Kummer images.**  The actual integer ring O_K
and the actual logarithm image log(O^×) of the integral units are both contained
in the actual integral log-shell.  Compactness of the shell and of the logarithm
image are the production facts isCompact_integralLogShell and
isCompact_unitLog_range; they are cited, not reproved here. -/
theorem logShell_contains_both_kummer_images :
    (Integers K : Set K) ⊆ (integralLogShell (K := K) (p := p) : Set K) ∧
      Set.range (fun u : (Integers K)ˣ => unitLog (K := K) u) ⊆
        (integralLogShell (K := K) (p := p) : Set K) :=
  ⟨integers_subset_integralLogShell (K := K) (p := p),
    range_unitLog_subset_integralLogShell (K := K) (p := p)⟩
end LeanFormal.IUT.XiFPaper.S3137LogShellKummerImageContainmentActual