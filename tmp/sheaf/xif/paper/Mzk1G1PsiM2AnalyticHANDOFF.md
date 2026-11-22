# HANDOFF — B1 analytic h (route §4.3 L298–334), M2 recursion

Owner of this design: henry (lane hull). **Status of code:** `Mzk1G1PsiM2AnalyticActual`
DONE 22:26:58 (three axioms, no sorry):

- `M2AnalyticTarget (Branch : Finset ℂ) : Prop`
  = `∃ q : Polynomial ℚ, 0 < q.natDegree ∧
       (∀ z ∈ Branch, aeval z q ∈ ({0,1} : Set ℂ)) ∧
       (∀ z, aeval z (derivative q) = 0 → aeval z q ∈ ({0,1} : Set ℂ)) ∧
       aeval (0:ℂ) q ∉ ({0,1} : Set ℂ)`.
  Polynomials over ℚ; ∞ is automatically a branch value for a nonconstant polynomial
  (total ramification at ∞), hence no separate conjunct).
- `m2AnalyticTarget_empty : M2AnalyticTarget ∅` — the rational base case, obtained
  unconditionally from `Mzk1G1PsiM2ProducerActual.mzk1Lemma24Target_of_zero`
  (which is `Consumer24AdapterUnconditionalActual.finiteBetaCorrectedBase_proved`).
- `aeval_zero_eq`, `polyEvalP1_ofFinite_mem_specialSet_iff` — the ℂ/ℚ evaluation bridges.

Convention fixed by Lead: `phi = psiFixed ≫ hPoly h hh` with
`psiFixed = inv ∘ psi` (`Mzk1G1PsiFixedActual`, DONE 22:20:10), hence
`Branch(psiFixed) = inv '' Branch(psi)` (P¹ involution λ ↦ λ⁻¹). The inversion
transport is the CALLER's job: supply `Branch : Finset ℂ` and, if needed,
`h(α) ∈ {0,1} ↔ h(α⁻¹) ∈ {0,1}` is handled by rewriting the branch set, not by changing
`M2AnalyticTarget`.

## What remains: the §4.3 recursion (to be produced by kurt; design here)

### Step producer shape (suggested declarations)

```lean
-- algebraic points: Mzk1G1PsiM2ProducerActual.AlgPoint (minpoly + Monic)
-- measure: (max redDeg, total redDeg) lexicographic
structure M2StepData (S : List AlgPoint) (β : AlgPoint) where
  f₀ : Polynomial ℚ                        -- monic minpoly of the max-degree point α₀
  hf₀monic : f₀.Monic
  hf₀deg : 0 < f₀.natDegree
  α₀ : AlgPoint                            -- the chosen max-degree point (f₀ = α₀.minpoly)
  S' : List AlgPoint                       -- new branch set (image of S ∪ roots f₀')
  β' : AlgPoint                            -- f₀(β)
  hS' : ∀ p ∈ S, (minpoly of f₀(p)) ∈ S'   -- values are the new algebraic points
  hβ' : β'.minpoly = (minpoly of f₀(β))
  hdec : Prod.Lex (· < ·) (· < ·) (muMeasure S' β') (muMeasure S β)
```

### Descent interface (already DONE, reuse)

`Mzk1G1PsiM2CoreActual` (DONE 22:11:45):
- `muList`, `muMeasure_eq_muList`, `muList_eq_map`,
- `muList_lex_of_entry_dec`, `muMeasure_lex_of_entry_dec` (one entry decreases, lists equal),
- `muMeasure_lex_of_beta_dec` (β decreases at equal measure),
- `lex_max_sum_of_single_dec` (max/sum decrease helper),
- `isRatPoint`, `isRatPoint_iff_deg_eq_one`, `ratVal`, `ratToP1` — AlgPoint → P1Point ℚ at degree 1.
  Also `Mzk1G1PsiM2ProducerActual.muMeasure_wf : WellFounded (Prod.Lex (·<·) (·<·))`.

### Termination and composition

1. Recursion on `Prod.Lex` well-founded measure: pick max reduced-degree α₀, replace
   `(S, β)` by `(S', β')` with `hdec`; at measure `(0,0)`/all degrees 1 transport to
   `P1Point ℚ` via `isRatPoint/ratToP1` and apply
   `Mzk1G1PsiM2ProducerActual.mzk1Lemma24Target_of_finite`.
2. Unwind: given a target polynomial `h'` for `(S', β')`, set `h := h' ∘ f₀` (or the
   Möbius-scaled `f₀`, see below). Needed composition laws:
   - critical values: `critValues_comp_subset` in
     `Mzk1Lemma22FullShapeHelpersActual` (fresh olean 12:48:20):
     `criticalValuesOverC (r.comp q) ⊆ aeval '' criticalValuesOverC q ∪ criticalValuesOverC r`;
   - special set preservation: `Mzk1BetaAvoidingBelyiRationalActual.critIn01_comp`
     (fresh olean 13:56:54) and `RestatedLemma24InterfaceActual.SpecialSetPreservationStatement`
     (target form; corollary of `belyi`-style values in {0,1}).
3. Möbius step (route §4.3 step 2–4): before building `f₀`, move β by a rational Möbius
   transformation `M_c` (pole chosen with a finite-separation bound;
   `Mzk1BetaAvoidingBelyiRationalActual.exists_betaAvoiding_card_le_two` and
   `BetaAvoidingStep` are the available finite-separation machinery), scale so that all
   finite α ∈ S satisfy ‖α‖ ≤ 1 and ‖β‖ is larger than the bound `B(d₀)`; the composition
   of Möbius maps is again rational, so the final `h` stays in ℚ[X] and the target
   statements only need the resulting polynomial.

### Analytic estimates needed (batch plan agreed with Lead; kurt owns code)

- batch 1: `norm_eval_prod_bound : p.Monic → (∀ z ∈ p.roots, ‖z‖ ≤ 1) → ‖α‖ ≤ 1 →
  ‖p.eval α‖ ≤ 2 ^ p.natDegree`; root product via
  `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C` (Algebra/Polynomial/Roots.lean:842)
  with `Polynomial.card_roots'` and splitting over ℂ; evaluation product via
  `Polynomial.eval_multiset_prod`; bound by multiset induction (each `‖α − r‖ ≤ 2`).
- batch 2: `cauchy_root_bound` for monic `p : ℂ[X]` and `z` with `p.derivative.eval z = 0`:
  `‖z‖ ≤ 1 + max_i ‖p.coeff i‖`; geometric-series proof (no existing Mathlib lemma).
  Also `norm_eval_derivative_bound` using batch-1 product bound and batch-2 root bound.
- batch 3: instantiate to `AlgPoint`: monic minpoly with all conjugates in the unit disk has
  coefficients `‖a_i‖ ≤ Nat.choose d i` (needs the general coefficient formula
  `prod_X_sub_C_coeff`, absent in Mathlib; build it with `Finset.prod` expansion and
  `Finset.sum_powerset`), then explicit `B(d₀)`.
- batch 4: `M2StepData` producer (choose α₀, Möbius, f₀, S', β', `hdec`).
- batch 5: well-founded recursion + composition ⇒
  `m2AnalyticTarget_of_branch (Branch : Finset ℂ) : M2AnalyticTarget Branch` (general
  finite branch set).

## Consumption convention of `M2AnalyticTarget` (B1 wiring)

Given `q` from `M2AnalyticTarget Branch` with `Branch = inv '' Branch(ψ)` (or the
caller-supplied presentation of `Branch(psiFixed)`):
- `q ≠ 0` follows from `0 < q.natDegree`;
- `phi := psiFixed ≫ hPoly q hq` (`hPoly` in `Mzk1G1PsiHPolyFinalActual`, DONE 22:12:58,
  names `hPoly`, `hPoly_ι_c0/c1/c2`, `hPoly_compat`);
- `T`-avoidance: `psiFixed` sends `D_T` to `0` (B2, route L273–278), so
  `phi(D_T) = q(0) ∉ {0,1}` gives `T`-avoidance (∞ not attained by a polynomial);
- finiteness of `phi.base ⁻¹' boundarySetGlued`: reduce to the three point fibres; use
  `Mzk1G1PsiFiniteFiberActual.finite_preimage_singleton/finset` and the chart formulas of
  `hPoly`/`psiFixed`; `Mzk1G1PsiB1Actual.boundaryPreimage_finite_of_each` is the reducer;
- branch condition: `hPoly`'s critical values are the polynomial `q`'s (DONE 22:09), and
  `h(Branch(ψFixed)) ⊆ {0,1}` is exactly the second conjunct of `M2AnalyticTarget`.

## Notes / risks

- Do NOT modify `Mzk1G1PsiM2AnalyticActual` statements: `M2AnalyticTarget` is the frozen
  interface consumed by B1.
- The old Lemma-2.4 corpus (`Mzk1BetaAvoidingBelyiRationalActual`,
  `Mzk1Rational24TargetBottomActual`, `Mzk1Lemma22FullShapeHelpersActual`,
  `Mzk1BelyiCanonicalActual`, `Mzk1GChoiceAvoidCanonicalActual`,
  `RestatedLemma24InterfaceActual`) has FRESH oleans; import them, do not edit them.
- The Cauchy coefficient formula is the single largest item; if it stalls, the fallback is
  to bound `‖f₀(α)‖` and `‖f₀(root f₀')‖` directly by a product estimate over conjugates
  (avoids symmetric functions but still needs the derivative-root bound).
