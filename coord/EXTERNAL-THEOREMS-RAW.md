# EXTERNAL-THEOREMS-RAW — exact signatures from local external trees

Source: `tmp/external/flt-lean` (commit `6e837e75`, lean-toolchain `v4.33.1`).
Read-only transcription. These are **upstream statements**, not ported code and not
green evidence for our project. Upstream files use `p2m_exact_reverting` and the FLT
repo's own axioms; nothing here may be cited as a proved theorem of ours.

## 1. Frey / modularity

Path: `tmp/external/flt-lean/Theorems/Thm_FreyPackage_frey_isModular.lean`
```lean
theorem FreyPackage.frey_isModular (P : FreyPackage) : P.freyCurve.IsModular := by
```

Path: `tmp/external/flt-lean/Theorems/Thm_FreyPackage_atPNewLowering.lean`
```lean
theorem atPNewLowering (P : FreyPackage) : P.AtPNewLowering := by
```

## 2. Ribet–Takahashi

**No declaration or file matching `RibetTakahashi` / `Ribet–Takahashi` exists in
`tmp/external/flt-lean`.** The closest modularity/level-lowering material is the
Ribet-Irr and Ribet-LevelLowering families below; the RT ratio `h(E)=½logδ−log‖f‖+O(1)`
is NOT in this tree.

## 3. Ribet-Irr (2 signatures)

Path: `tmp/external/flt-lean/Theorems/Thm_RibetIrr_irreducible_of_point_of_not_dvd.lean`
```lean
theorem RibetIrr.irreducible_of_point_of_not_dvd
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ)
    (_hpS : p ∈ S) (_hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')]
    [CharZero 𝒪'] (_hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (hpN : ¬ p ∣ N)
    (ρ : GaloisRepAdic 𝒪')
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪'))) :
    Submodule.span K (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ.ρ σ).baseChange K) = ⊤ := by
```

Path: `tmp/external/flt-lean/Theorems/Thm_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.lean`
```lean
theorem RibetIrr.line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt (p : ℕ) [Fact p.Prime]
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ : GaloisRepAdic 𝒪') (hflat : ρ.IsFlatAt p) (hdet : ρ.DetIsCyclotomic p)
    (W : Submodule K (K ⊗[𝒪'] ρ.V)) (hW : Module.finrank K W = 1)
    (hWstab : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ w ∈ W,
      (ρ.ρ σ).baseChange K w ∈ W) :
    (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, (ρ.ρ σ).baseChange K w = w) ∨
    (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : K ⊗[𝒪'] ρ.V, (ρ.ρ σ).baseChange K v - v ∈ W) := by
```

## 4. Taylor–Wiles (2 signatures)

Path: `tmp/external/flt-lean/Theorems/Thm_TaylorWiles_exists_isTaylorWilesPrime.lean`
```lean
theorem TaylorWiles.exists_isTaylorWilesPrime
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    (ρ : TaylorWiles.ResidualRep L 𝕜) (p n : ℕ)
    {S : Finset ℕ} (seed : TaylorWiles.Seed ρ p n S) (T : Finset ℕ) :
    ∃ q : ℕ, q ∉ S ∧ q ∉ T ∧ TaylorWiles.IsTaylorWilesPrime ρ p n q := by
```

Path: `tmp/external/flt-lean/Theorems/Thm_TaylorWiles_exists_isEigenIdempotent_of_isUnit.lean`
```lean
theorem TaylorWiles.exists_isEigenIdempotent_of_isUnit {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hu : IsUnit (a - b)) :
    ∃ e, TaylorWiles.IsEigenIdempotent M a b e := by
```

## 5. Newform (1 signature)

Path: `tmp/external/flt-lean/Theorems/Thm_CuspForm_IsNewform_eq_of_forall_qCoeff_eq.lean`
```lean
theorem CuspForm.IsNewform.eq_of_forall_qCoeff_eq
    {M R : ℕ} [NeZero M]
    {g g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (hR : R ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ) :
    g = g' := by
```

## 6. Cerednik–Drinfeld / Shimura curve model (1 signature)

Path: `tmp/external/flt-lean/Theorems/Thm_CerednikDrinfeld_exists_shimuraCurveModel_goodReduction_and_periodUniformization_pair_of_six_mul_dvd_of_neZero.lean`
```lean
theorem CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_periodUniformization_pair_of_six_mul_dvd_of_neZero
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

    {a₂ b₂ : ℚ} (hdef₂ : IsDefiniteRamifiedExactlyAt (a := a₂) (b := b₂) q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    {a₁ b₁ : ℚ} (hdef₁ : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ q)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * q))
    (hnorm₁ : Submodule.conjByFiniteIdele (meetOrder R₁ n₁) n₁ = meetOrder R₁ n₁)
    (hsq₁ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)),
      classSetShift _ n₁ (classSetShift _ n₁ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    (hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ (Λ : Submodule ℤ ℍ[ℚ, a, b]) (_ : IsMaximalOrder Λ) (_ : R ≤ Λ),
    ∃ M : ShimuraCurveModel R ι (fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
      ∃ ε : Nat.Primes → ℤˣ, (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q → (ℓ : ℕ) ≠ q' → ε ℓ = 1) ∧
      (∀ p : ℕ, p.Prime → M.GoodReductionOutside p (D * p)) ∧
      Nonempty (Mumford.PeriodUniformization q' (classSetDegeneracyData R₂ n₂) (classSetHeckeData N q' Λ₂ R₂ n₂)
        A₁ hA₁ M.J (M.heckeJSigned ε) M.galJ) ∧
      Nonempty (Mumford.PeriodUniformization q (classSetDegeneracyData R₁ n₁) (classSetHeckeData N q Λ₁ R₁ n₁)
        A₂ hA₂ M.J (M.heckeJSigned ε) M.galJ) := by
```

## 7. Heights (2 signatures; absLogHeight on algebraic curve roots)

Path: `tmp/external/flt-lean/Theorems/Thm_AlgebraicCurve_absLogHeight_root_le_coeff.lean`
```lean
theorem AlgebraicCurve.absLogHeight_root_le_coeff {p : Polynomial (AlgebraicClosure ℚ)}
    (hmonic : p.Monic) {z : AlgebraicClosure ℚ} (hroot : p.eval z = 0) :
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) := by
```

Path: `tmp/external/flt-lean/Theorems/Thm_AlgebraicCurve_absLogHeight_coeff_le_sum_roots.lean`
```lean
theorem AlgebraicCurve.absLogHeight_coeff_le_sum_roots {ι : Type*} (t : Finset ι)
    (α : ι → AlgebraicClosure ℚ) (m : ι → ℕ) {n : ℕ} (hdeg : ∑ i ∈ t, m i ≤ n) :
    absLogHeight (fun k : Fin (n + 1) =>
        (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k)
      ≤ ∑ i ∈ t, (m i : ℝ) * absLogHeight ![α i, 1] + n * Real.log 2 := by
```

## 8. Pasten abstracts (E7 route; external literature, not Lean)

### Pasten 2018
H. Pasten, *Shimura curves and the abc conjecture*, arXiv:1705.09251v4 (2018). **UNVERIFIED**: arXiv 页面本环境不可达；版本/日期/发表状态未 original-level 核验。
Abstract (verbatim key sentence): “We develop a general framework to study Szpiro's
conjecture and the abc conjecture by means of Shimura curves and their maps to elliptic
curves ... Our main applications ... include improved effective bounds for the Faltings
height of elliptic curves over Q in terms of the conductor, bounds for products of p-adic
valuations of the discriminant of elliptic curves over Q which are polynomial on the
conductor, and results that yield a modular approach to Szpiro's conjecture over totally
real number fields ...”
Source: <https://arxiv.org/abs/1705.09251>.

### Pasten 2026
H. Pasten, *Improved bounds for Szpiro's conjecture*, arXiv:2609.17390 (2026). **UNVERIFIED**: arXiv 页面本环境不可达；版本/日期/同行评审状态未核。
Abstract: for all elliptic curves E/Q, current best bound `log Δ ≪ N log N`; this paper proves
`log Δ ≪ N log log N` unconditionally, and for semistable E proves `log Δ ≪ N`.
Source: <https://arxiv.org/abs/2609.17390>.
Status: literature statements only; not formalized, not green.

## 9. Draft mapping to our Prop layer (A856; 3–5 items)

These are **interface names only**, no Lean definitions yet; every one is PENDING and
must be connected to real objects before use.

| external signature | proposed our-side Prop | status |
|---|---|---|
| `FreyPackage.frey_isModular` | `FreyModularityInput : Prop` (quantifies ABC+Frey curve; object mapping PENDING) | PENDING |
| `RibetIrr.irreducible_of_point_of_not_dvd` | `ResidualIrreducibilityInput : Prop` | PENDING |
| `TaylorWiles.exists_isTaylorWilesPrime` | `TaylorWilesPrimeSelection : Prop` | PENDING |
| `CuspForm.IsNewform.eq_of_forall_qCoeff_eq` | `NewformMultiplicityOne : Prop` | PENDING |
| `AlgebraicCurve.absLogHeight_root_le_coeff` | `HeightRootBound : Prop` | PENDING |

No fake instances, no axioms added, no port claimed.

## 10. Upstream sorry/axiom/knownin1980s note

Read-only scan of `tmp/external/flt-lean`: no `axiom` declaration and no
`knownin1980s` hit in this snapshot; only 3 `sorry` occurrences under
`verification/comparator/Challenge.lean`. The historical ported FLT tree
(`tmp/external/ported/flt`) came from a different snapshot and has 18 `sorry` +
16 `knownin1980s`; that tree remains scaffolding only and must not enter evidence.
