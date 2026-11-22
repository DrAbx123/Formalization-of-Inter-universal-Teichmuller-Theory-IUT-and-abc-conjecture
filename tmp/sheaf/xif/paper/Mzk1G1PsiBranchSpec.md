# SPEC — `Branch(psiFixed) : Finset ℂ` and the §4.3 review checklist

Owner: henry (hull). Companion of `Mzk1G1PsiM2AnalyticHANDOFF.md`. Non-Lean design doc.

## 1. The chart coordinates of `psiFixed` (all DONE, three axioms)

`Mzk1G1PsiFixedActual` (andrew, DONE 22:20:10):
- `psiFixed (n) (T) : fermatCurveScheme n ⟶ projectiveLineGlued`
  = `(psiOpenCover n T).glueMorphisms (psiFunFixed n T) (glueMorphisms_compat_fixed n T)`;
- `psiFunFixed` (swapped charts): piece `⟨false⟩` ↦
  `chartMorphism0 (R := R n) (psiChart0Coord n T)` (lambda-coordinate);
  piece `⟨true⟩` ↦ `chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
  (psiChartInfCoord n T)` (t-coordinate);
- `psiFixed_ι_false/true` are the chart-level composites;
- `affine_compat_swapped` uses `chartMorphism_transition (R := overlapRing n T)
  ((psiUnit n T)⁻¹)` — i.e. on the overlap `lambda = u`, `t = u⁻¹`.

P¹ chart conversion (`Mzk1G1ProjectiveLineTransitionActual`):
- `chartMorphism0 (R) a = Spec.map (ofHom (evalAt a)) ≫ localChart0` (target lambda = a);
- `chartMorphismInf (R) a = Spec.map (ofHom (evalAt a)) ≫ localChartInf` (target t = a);
- `chartMorphism_transition (u : Rˣ) : chartMorphism0 (R) (↑u) = chartMorphismInf (R) (↑u⁻¹)`.

## 2. Analytic branch values of `psiFixed` (canonical, ℚ-coefficients)

Let `u := protectedToZeroPolynomial T = ∏_{t∈T} (X − C t)` (the polynomial whose image in
`R n` is `psiChart0Coord n T`; see `Mzk1G1PsiChartMapsActual` / `Mzk1G1BelyiCVCompositionActual`).
On the lambda chart `psiFixed` is `Spec.map (evalAt u) ≫ localChart0`, so its finite
critical values in that chart are exactly

    Branch(psi) := criticalValuesOverC u   -- Set ℂ, from `RestatedLemma24InterfaceActual`

(definition: `{c | ∃ z, ¬ u.natDegree = 0 ∧ aeval z u' = 0 ∧ aeval z u = c}`).
This is the *canonical* complex set: `u ∈ ℚ[X]`, so it does not depend on a choice of
embedding σ : K → ℂ (the route's `K_V`/σ bookkeeping is thereby bypassed on the branch
side; σ would only be needed for a scheme-level ramification statement, see §4).
Existing donor statements (value level, DONE):
- `Mzk1G1NoncriticalPsiActual.phi_branch_values`: for `q : ℚ[X]`,
  `(∀ c ∈ criticalValuesOverC u, aeval c q ∈ {0,1}) → criticalValuesOverC q ⊆ {0,1} →
  criticalValuesOverC (q.comp u) ⊆ {0,1}`
  (so the *composite* `q ∘ psi` has critical values in {0,1} once q maps `Branch(psi)` to {0,1});
- `Mzk1G1NoncriticalPsiActual.psi_unramified_over_zero`, `psi_simple_zero` (B2: 0 is not a
  critical value of psi; T-fibres are exactly ψ⁻¹(0));
- `Mzk1G1BelyiCVCompositionActual.comp_criticalValues_subset` (the composition law).

## 3. `Branch(psiFixed)` in the M2 target

`psiFixed = inv ∘ psi` (`Mzk1G1PsiFixedActual` is exactly the swapped-chart version, so the
formula holds definitionally at the level of chart coordinates). Therefore the finite part
of `Branch(psiFixed)` is the inversion image of the finite part of `Branch(psi)` possibly
minus `{0}` (a branch value 0 of psi maps to `∞` under inv; `∞` is automatically allowed by
`M2AnalyticTarget`, since for a nonconstant polynomial `h(∞) = ∞ ∈ {0,1,∞}`). Concretely,
the spec for the `Finset ℂ` passed to `M2AnalyticTarget` is

```lean
-- u := protectedToZeroPolynomial T
-- branchPoly := derivative u
noncomputable def branchValuesFinite (T : Finset ℚ) : Finset ℂ :=
  ((derivative (protectedToZeroPolynomial T)).roots.attach).map
      (fun r => Polynomial.aeval r.1 (protectedToZeroPolynomial T))

noncomputable def branchFixedFinite (T : Finset ℚ) : Finset ℂ :=
  (branchValuesFinite T).filter (fun z => z ≠ 0) |>.image (fun z => z⁻¹)
```

Wanted companion lemmas (NOT yet in the repository — these are the gaps):
1. `coe_branchValuesFinite (T) (hT : 2 ≤ T.card)` :
   `↑(branchValuesFinite T) = criticalValuesOverC (protectedToZeroPolynomial T)`
   (needs: `derivative u` splits over ℂ, `u.natDegree = T.card ≥ 1`, and the multiset
   `Polynomial.roots` API; no scheme theory needed).
2. `coe_branchFixedFinite (T) (hT : 2 ≤ T.card)` :
   `↑(branchFixedFinite T) = (fun z => z⁻¹) '' (criticalValuesOverC u \ {0})`.
3. (scheme level, LARGER GAP; not hull's lane) a statement identifying the scheme
   ramification image of `psiFixed` with `(fun z => z⁻¹) '' (criticalValuesOverC u)`;
   this is route §4.4's B3 differential computation (`dt/du` orders) and is currently
   only available in *value* form (`phi_branch_values`). Until it lands, `M2AnalyticTarget`
   consumes the *analytic* set from §3 directly — which is exactly what B1 needs, because
   the B1 statement `h(Branch psiFixed) ⊆ {0,1,∞}` is tested on the analytic branch values.

## 4. What must NOT be faked

- Do not define `Branch` as an arbitrary finite set: use `criticalValuesOverC u` (or its
  Finset form above) so the set is *the* branch set of the concrete map.
- Do not add hypotheses such as "all branch values are known"; the branch set is a
  definition, not an input.
- The inversion `z ↦ z⁻¹` must be applied on the finite part only; the `∞` image of 0 is
  handled by the polynomial-`∞` convention.

## 5. Review checklist for kurt's §4.3 output (fill in when his files land)

| route §4.3 step | required content | check in kurt's file |
|---|---|---|
| 1. Galois closure; lex measure (max reduced degree, sum of reduced degrees) | `AlgPoint` list closed under conjugation; `muMeasure`/`muList` decrease | |
| 2. Max-degree α₀; rational Möbius pole with explicit finite-separation bound; |α|≤1, |β| large | `betaAvoiding`/`exists_betaAvoiding_card_le_two` instance; concrete bound on |β| | |
| 3. Monic minpoly f₀ of α₀; coefficient bound |a_i| ≤ C(d₀,i) | `prod_X_sub_C_coeff` + `norm_eval_prod_bound` + coefficient bound lemma | |
| 4. Derivative roots: Cauchy root bound R(d₀); bound B(d₀) on |f₀(S₁)| and |f₀(roots f₀')|; |f₀(β)| > B(d₀) | `cauchy_root_bound` + `norm_eval_derivative_bound` + B(d₀) | |
| 5. S₂ = f₀(S₁) ∪ f₀(roots f₀') ∪ {∞}, β₂ = f₀(β); strict lex decrease | `M2StepData` with `hdec : Prod.Lex ...` | |
| 6. Termination + reverse composition; final `M2AnalyticTarget` | `m2AnalyticTarget_of_branch` (general finite Branch), composition via `critValues_comp_subset`/`critIn01_comp` | |

Consistency checks: (i) no new hypotheses in the final producer; (ii) `#print axioms` =
[propext, Classical.choice, Quot.sound]; (iii) no `sorry`/`admit`/`axiom`; (iv) M1 base case
reached through `mzk1Lemma24Target_of_finite` (not re-assumed); (v) the final statement is
exactly `M2AnalyticTarget Branch` for arbitrary finite `Branch` (no restriction).
