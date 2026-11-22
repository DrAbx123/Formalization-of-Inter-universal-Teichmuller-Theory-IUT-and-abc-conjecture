import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidSkeletonCards
import LeanFormal.IUT.IUTII.Kummer.RootRealization
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Value-group rationality at one nonarchimedean place (MOD-R, rationality half)

This module proves the rationality half of the frozen MOD-R card
`PadicNormImageCard p` (`PrimeStripFrobenioidSkeletonCards.lean:245`): the
norm image of `(Qbar_p)^x` is exactly `p^Q`.  The arithmetic-surjectivity half
is the earlier theorem `padicAlgClNormImage_surjective`; the two halves are
combined here as `padicNormImageCard_proved`.

## Frozen contents (source anchors and Lean statements)

* Lower bound (IUT I, section 0, txt 1645-1660: a pseudo-monoid is "divisible"
  if every element of the ambient group possesses an n-th root; IUT I,
  Example 3.3, (i), txt 4151-4179: the pv-adic Frobenioids `C^dash_v <= Cv`
  with `Phi_Cv : Spec(L) |-> ord(O_L)^pf` and
  `Phi_C^dash_v : Spec(L) |-> ord(Z_pv)`; the "pf" (perfection) is the source
  of the rational value group).  Lean:
  `exists_padicAlgClUnit_logVal_eq_inv`: for every `m > 0` there is a unit `u`
  of `Qbar_p` with normalized log value `1/m`, namely a root of `X^m - p`.
* Upper bound (every norm is a rational power of `p`; same source passage,
  `ord(O_L)^pf` made rational by the perfection).  Lean:
  `padicAlgCl_norm_eq_rpow_rat`: every nonzero `x : Qbar_p` has `||x|| = p^q`
  for some `q : Q`.
* Combined: `padicNormImageCard_proved` (the card `PadicNormImageCard p`),
  `padicAlgCl_unit_logVal_range_eq_rat` (normalized log-value image `= Q`),
  and `frobenioidLinkUnitStrip_degreeImage_eq_ratLog` (degree image of the
  unit strip `= Q * log p`, upgrading the inclusion
  `frobenioidLinkUnitStrip_degreeImage_ratLog` of the skeleton file).

Source route vs this route: the source builds the value group through the
perfected ord monoid `ord(O_L)^pf` of the pv-adic Frobenioid (IUT I,
Example 3.3, (i); Frobenioids II, Example 1.1); this module works in the norm
arithmetic layer instead (Mathlib `spectralNorm` / `minpoly` /
`Padic.norm_eq_zpow_neg_valuation`), since neither the tree nor Mathlib
exposes a valuation-group quotient on `AlgebraicClosure`.  The formalized
statement is the same arithmetic content `v((Qbar_p)^x) = Q` up to the
`log_p` normalization of `padicAlgClUnitLogVal`.  No Frobenioid structure, no
torsor/fractional-ideal representation, and no multi-place statement is
claimed here.

## Consumer-side interface requests (CAT-R cards, for dispatch)

The three items below are the remaining CAT-R inputs at the link layer,
stated as minimal requests: object / quantifiers / hypotheses / conclusion /
consumers.  No source-level construction is attempted in this module.

* REQ-1 (etale pi_1).  Object: a geometric fundamental group `pi_1` of the
  D-prime-strip base with a surjection `proj : pi_1 -> Gal(Kv)` onto the local
  absolute Galois group and nontrivial kernel.  Quantifiers: every `v` in
  `V^non`, every D-prime-strip.  Hypotheses: etale-covering/pi_1 data on the
  base categories `Dv`, `D^dash_v`.  Conclusion: `Ker(proj)` nontrivial (the
  current carrier has `proj = MonoidHom.id`).  Consumers:
  `VerticalLogKummer:70`, `SourceFaithfulBoundary:1725`.
* REQ-2 (V_K transport / rho_v normalization).  Object: number-field place
  carriers `K_v` of `K = Fmod` with the `V_K` transport, and the comparison
  `rho_v : Phi(C^sqcap_mod),v = Phi^rlf(C^dash_v)`,
  `log(C^dash_mod)(pv) |-> 1/[Kv:(Fmod)v] * log(Phi(pv))` (IUT I,
  Example 3.5, (i), txt 4569ff).  Quantifiers: all places `v` of `K`.
  Hypotheses: completion / ramification-index data.  Conclusion: the
  normalized comparison isomorphism.  Consumers: `SourceOriginalInput`, the
  K2 boundary (`SourceK1K2Construction:676-679`).
* REQ-3 (arithmetic Frobenius).  Object: Frobenius dynamics (power morphisms
  with Frobenius degree) on the value/divisor monoid and its log-shell
  compatibility (Frobenioids I, Definition 1.2/1.3).  Quantifiers: elemental
  morphisms of the Frobenioid structure.  Hypotheses: a Frobenioid instance
  on the carriers (blocked by the missing sharp divisorial monoid; see
  `PrimeStripFrobenioidSkeletonCards`).  Conclusion: Frobenius degree and
  log-shell compatibility.  Consumers:
  `VerticalLogKummerCorrespondence.upperSemi`, `Ind3`.

## Consumers

The Theorem 3.11 source chain, in particular the K2 boundary
(`IUTIII/Theorem311/SourceK1K2Construction.lean:676-679`: local/global
Frobenioids, MOD/mod maps, degree), and `SourceHodgeTheaterBridge`.
-/

namespace LeanFormal.IUT
/-- Normalized log-absolute value on the units of `Qbar_p`,
`u |-> -log_p ||u||`, as a monoid homomorphism to the additive reals.
The normalization makes the prime unit `p` have value `1`, so a root of
`X^m - p` gets value `1/m`. -/
noncomputable def padicAlgClUnitLogVal (p : ℕ) [Fact (Nat.Prime p)] :
    (PadicAlgCl p)ˣ →* Multiplicative ℝ where
  toFun u := Multiplicative.ofAdd (-(Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : ℝ)))
  map_one' := by
    apply Multiplicative.ext
    simp
  map_mul' u v := by
    apply Multiplicative.ext
    rw [Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Units.ne_zero u))
        (norm_ne_zero_iff.mpr (Units.ne_zero v))]
    rw [← ofAdd_add, ← neg_add, ← add_div]

/-- The normalized log value of the prime unit `p` is `1`. -/
theorem padicAlgClUnitLogVal_primeUnit (p : ℕ) [Fact (Nat.Prime p)] :
    (padicAlgClUnitLogVal p (padicAlgClPrimeUnit p)).toAdd = 1 := by
  change -(Real.log ‖((padicAlgClPrimeUnit p : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ /
    Real.log (p : ℝ)) = 1
  have hcoe : ((padicAlgClPrimeUnit p : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((p : ℚ_[p]) : PadicAlgCl p) := rfl
  rw [hcoe, PadicAlgCl.norm_extends, Padic.norm_p, Real.log_inv]
  have hL : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt))
  rw [show -((-Real.log (p : ℝ)) / Real.log (p : ℝ)) =
      Real.log (p : ℝ) / Real.log (p : ℝ) from by ring]
  exact div_self hL

/-- Abstract lower-bound form: if `u^m = p` then the normalized log value
of `u` is `1/m`. -/
theorem padicAlgClUnitLogVal_eq_inv_of_pow_eq_primeUnit (p : ℕ) [Fact (Nat.Prime p)]
    (u : (PadicAlgCl p)ˣ) (m : ℕ) (hm : 0 < m) (h : u ^ m = padicAlgClPrimeUnit p) :
    (padicAlgClUnitLogVal p u).toAdd = 1 / (m : ℝ) := by
  have hval_pow : (padicAlgClUnitLogVal p u) ^ m =
      padicAlgClUnitLogVal p (padicAlgClPrimeUnit p) := by
    rw [← map_pow, h]
  have htoAdd : ((padicAlgClUnitLogVal p u).toAdd) * m = 1 := by
    have h1 := congrArg Multiplicative.toAdd hval_pow
    rw [padicAlgClUnitLogVal_primeUnit] at h1
    rw [toAdd_pow, nsmul_eq_mul] at h1
    rw [mul_comm] at h1
    exact h1
  rw [eq_div_iff (by exact_mod_cast hm.ne')]
  exact htoAdd

/-- Lower bound `1/m` of `v((Qbar_p)^x) = Q`: for every `m > 0` there is a
unit of `Qbar_p` with normalized log value `1/m`, realized by a root of the
Eisenstein polynomial `X^m - p` (the `localKummerRootRealizationFor`
kernel). -/
theorem exists_padicAlgClUnit_logVal_eq_inv (p : ℕ) [Fact (Nat.Prime p)]
    (m : ℕ) (hm : 0 < m) :
    ∃ u : (PadicAlgCl p)ˣ, (padicAlgClUnitLogVal p u).toAdd = 1 / (m : ℝ) := by
  let R := localKummerRootRealizationFor p m hm
  have hy_ne : R.root ≠ 0 := R.root_ne_zero
  refine ⟨Units.mk0 R.root hy_ne, ?_⟩
  refine padicAlgClUnitLogVal_eq_inv_of_pow_eq_primeUnit p _ m hm ?_
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  change R.root ^ m = ((p : ℚ_[p]) : PadicAlgCl p)
  simpa only [localKummerPolynomialFor] using R.root_pow_eq

/-- Upper bound (rationality of norms): every nonzero element of `Qbar_p`
has norm `p^q` for a rational `q`.  Proof: Mathlib's spectral norm computes
`||x||` as the maximal `spectralValueTerms` entry of `minpoly Q_[p] x`,
whose value is a coefficient norm `p^(-v)` raised to the rational exponent
`1/(natDegree - n0)`. -/
theorem padicAlgCl_norm_eq_rpow_rat (p : ℕ) [Fact (Nat.Prime p)]
    (x : PadicAlgCl p) (hx : x ≠ 0) :
    ∃ q : ℚ, ‖x‖ = (p : ℝ) ^ (q : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hspec : ‖x‖ = spectralValue (minpoly ℚ_[p] x) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    rfl
  have hne : (Set.range (spectralValueTerms (minpoly ℚ_[p] x))).Nonempty :=
    ⟨spectralValueTerms (minpoly ℚ_[p] x) 0, Set.mem_range_self 0⟩
  obtain ⟨b, hb_mem, hb_max⟩ :=
    Set.exists_max_image (Set.range (spectralValueTerms (minpoly ℚ_[p] x))) id
      (spectralValueTerms_finite_range _) hne
  obtain ⟨n₀, hn₀⟩ := hb_mem
  have hsup : spectralValue (minpoly ℚ_[p] x) =
      spectralValueTerms (minpoly ℚ_[p] x) n₀ := by
    rw [spectralValue]
    refine le_antisymm (ciSup_le (fun n => ?_))
      (le_ciSup (spectralValueTerms_bddAbove _) n₀)
    have h := hb_max (spectralValueTerms (minpoly ℚ_[p] x) n) (Set.mem_range_self n)
    rwa [← hn₀] at h
  rcases lt_or_ge n₀ (minpoly ℚ_[p] x).natDegree with hlt | hge
  · by_cases hc : (minpoly ℚ_[p] x).coeff n₀ = 0
    · exfalso
      have hsubR : (0 : ℝ) <
          ((minpoly ℚ_[p] x).natDegree : ℝ) - (n₀ : ℝ) :=
        sub_pos.mpr (by exact_mod_cast hlt)
      have hzero : spectralValue (minpoly ℚ_[p] x) = 0 := by
        rw [hsup, spectralValueTerms_of_lt_natDegree _ hlt, hc, norm_zero,
          Real.zero_rpow (one_div_ne_zero (ne_of_gt hsubR))]
      have : ‖x‖ = 0 := by rw [hspec, hzero]
      exact hx (norm_eq_zero.mp this)
    · have hnorm : ‖(minpoly ℚ_[p] x).coeff n₀‖ =
          (p : ℝ) ^ (-((minpoly ℚ_[p] x).coeff n₀).valuation) :=
        Padic.norm_eq_zpow_neg_valuation hc
      refine ⟨(-((minpoly ℚ_[p] x).coeff n₀).valuation : ℚ) /
        (((minpoly ℚ_[p] x).natDegree : ℚ) - (n₀ : ℚ)), ?_⟩
      rw [hspec, hsup, spectralValueTerms_of_lt_natDegree _ hlt, hnorm,
        ← Real.rpow_intCast, ← Real.rpow_mul (le_of_lt hp0)]
      congr 1
      push_cast
      ring
  · exfalso
    have hzero : spectralValue (minpoly ℚ_[p] x) = 0 := by
      rw [hsup, spectralValueTerms_of_natDegree_le _ hge]
    have : ‖x‖ = 0 := by rw [hspec, hzero]
    exact hx (norm_eq_zero.mp this)

/-- The rationality half of the frozen MOD-R card `PadicNormImageCard`:
every norm of a unit of `Qbar_p` is a rational power of `p`. -/
theorem padicNormImage_rational (p : ℕ) [Fact (Nat.Prime p)] :
    PadicNormImageRational p := by
  intro r hr
  obtain ⟨u, rfl⟩ := hr
  obtain ⟨q, hq⟩ := padicAlgCl_norm_eq_rpow_rat p (u : PadicAlgCl p) (Units.ne_zero u)
  exact ⟨q, hq.symm⟩

/-- The frozen MOD-R card `PadicNormImageCard p`
(`padicAlgClNormImage p = padicPowSet p`), combining the rationality half
proved here with the surjectivity half `padicAlgClNormImage_surjective` of
`PrimeStripFrobenioidSkeletonCards`. -/
theorem padicNormImageCard_proved (p : ℕ) [Fact (Nat.Prime p)] :
    PadicNormImageCard p :=
  (padicNormImageCard_iff p).mpr
    ⟨padicNormImage_rational p, padicAlgClNormImage_surjective p⟩

/-- The normalized log values realize every element of `Z * (1/m)` inside
`(Qbar_p)^x`, by raising the `1/m`-value unit to integer powers. -/
theorem padicAlgCl_unit_logVal_range_int_div_subset (p : ℕ) [Fact (Nat.Prime p)]
    (m : ℕ) (hm : 0 < m) :
    Set.range (fun k : ℤ => (k : ℝ) / (m : ℝ)) ⊆
      Set.range (fun u : (PadicAlgCl p)ˣ => (padicAlgClUnitLogVal p u).toAdd) := by
  intro r hr
  obtain ⟨k, rfl⟩ := hr
  obtain ⟨u, hu⟩ := exists_padicAlgClUnit_logVal_eq_inv p m hm
  refine ⟨u ^ k, ?_⟩
  change (padicAlgClUnitLogVal p (u ^ k)).toAdd = (k : ℝ) / (m : ℝ)
  rw [map_zpow, toAdd_zpow, zsmul_eq_mul, hu, mul_one_div]

theorem padicAlgCl_unit_logVal_range_eq_rat (p : ℕ) [Fact (Nat.Prime p)] :
    Set.range (fun u : (PadicAlgCl p)ˣ => (padicAlgClUnitLogVal p u).toAdd) =
      Set.range (fun q : ℚ => (q : ℝ)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro r hr
    obtain ⟨u, rfl⟩ := hr
    obtain ⟨q, hq⟩ := padicAlgCl_norm_eq_rpow_rat p (u : PadicAlgCl p) (Units.ne_zero u)
    refine ⟨-q, ?_⟩
    change ((-q : ℚ) : ℝ) = -((Real.log ‖(u : PadicAlgCl p)‖) / Real.log (p : ℝ))
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).pos
    have hL : Real.log (p : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt))
    rw [hq, Real.log_rpow hp0, mul_div_cancel_right₀ ((q : ℚ) : ℝ) hL]
    push_cast
    ring
  · intro r hr
    obtain ⟨q, rfl⟩ := hr
    refine padicAlgCl_unit_logVal_range_int_div_subset p q.den q.den_pos ?_
    simp [Rat.cast_def]

theorem frobenioidLinkUnitStrip_degreeImage_eq_ratLog (v : RationalPrimePlace) :
    Set.range (fun u : frobenioidLinkUnitStrip.Mon v =>
      (frobenioidLinkUnitStrip.degree v u).toAdd) =
    Set.range (fun q : ℚ => (q : ℝ) * Real.log (v.1 : ℝ)) := by
  refine Set.Subset.antisymm ?_ (frobenioidLinkUnitStrip_degreeImage_ratLog v)
  intro r hr
  obtain ⟨u, rfl⟩ := hr
  letI : Fact (Nat.Prime v.1) := Fact.mk v.2
  let u' : (AlgebraicClosure ℚ_[v.1])ˣ := u
  obtain ⟨q, hq⟩ :=
    padicAlgCl_norm_eq_rpow_rat v.1 (u' : AlgebraicClosure ℚ_[v.1]) (Units.ne_zero u')
  refine ⟨q, ?_⟩
  change ((q : ℝ) * Real.log (v.1 : ℝ)) =
    Real.log ‖(u' : AlgebraicClosure ℚ_[v.1])‖
  rw [hq, Real.log_rpow (by exact_mod_cast (Fact.out : Nat.Prime v.1).pos)]

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- MOD-R rationality half of `IUT-I-II.prime-strips-frobenioids`: the value
group of `(Qbar_p)^x` is rational, proved at the norm-arithmetic layer. -/
def primeStripFrobenioidValueGroupRationality : Obligation :=
  { id := "IUT-II.prime-strips-frobenioid-value-group-rationality"
    source :=
      "IUT I, section 0 (divisible pseudo-monoids, txt 1645-1660); " ++
        "Example 3.3, (i) (txt 4151-4179); Example 3.5, (i) (txt 4569ff); " ++
        "IUT III, Example 3.6, (i) (txt 6181ff); Frobenioids II, Example 1.1"
    status := VerificationStatus.provedKernel
    note :=
      "The rationality half of the frozen MOD-R card `PadicNormImageCard p` " ++
        "is PROVED (`padicNormImage_rational`, `padicNormImageCard_proved`): " ++
        "the norm image of `(Qbar_p)^x` is exactly `p^Q`. Lower bound: roots " ++
        "of `X^m - p` give normalized log value `1/m` " ++
        "(`exists_padicAlgClUnit_logVal_eq_inv`); upper bound: " ++
        "`padicAlgCl_norm_eq_rpow_rat` via the spectral norm of `minpoly` " ++
        "and coefficient valuations. Corollaries: the normalized log-value " ++
        "image is `Q` (`padicAlgCl_unit_logVal_range_eq_rat`) and the " ++
        "unit-strip degree image equals `Q * log p` " ++
        "(`frobenioidLinkUnitStrip_degreeImage_eq_ratLog`). This is a proved " ++
        "arithmetic kernel with no source realization: the Frobenioid " ++
        "structure, the torsor/fractional-ideal representations of IUT III, " ++
        "Example 3.6, and the CAT-R boundary items (REQ-1/2/3 in the module " ++
        "header) remain open."
    dependsOn :=
      [ "IUT-II.prime-strips-frobenioid-skeleton-cards",
        "IUT-II.adjoin-root-local-embedding" ] }

end LeanFormal.IUT.Audit
