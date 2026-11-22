# R1: P5 comparison in the common container (q_P5 <= theta_P5) - guidance for kurt/grace

Status: paper-dictionary guidance (sophie, 2026-11-18). No Lean code here; the Lean
names below are the current realizations.

## 1. Paper: the two pilots (III.txt)

- **q-pilot** (III L872-877): "arithmetic divisor determined by the zero locus of the
  elements 'q_v' at v ∈ V^bad as a q-pilot object. The log-volume of the q-pilot object
  will be denoted by **−|log(q)| ∈ R**" (so |log(q)| > 0, cf. Cor 3.12/Thm B).
- **Θ-pilot** (III L883-891): "arithmetic divisor determined by the zero locus of the
  collection of theta values '{q_v^{j^2}}_{j=1,...,l^*} at v ∈ V^bad as a Θ-pilot object.
  The log-volume of the **holomorphic hull ... of the union of the collection of possible
  images** of the Θ-pilot object in the multiradial representation — subject to
  (Ind1),(Ind2),(Ind3) — will be denoted by **−|log(Θ)| ∈ R ∪ {+∞}**".
- signs (III L901-906): `|log(Θ)| := −(−|log(Θ)|) ∈ R ∪ {−∞}`; the content of
  Cor 3.12/Thm B is "negativity of the Θ-pilot log-volume |log(Θ)|" (III L901-906).
- two computations (III L929-943): the multiradial representation yields "two
  tautologically equivalent ways to compute the q-pilot log-volume −|log(q)|"
  (Fig. I.8; Step (xi) of Cor 3.12).

## 2. Paper: the common container (III.txt L5245-5260)

- "(vi) ... If one starts from M = Pic(*C^⊩), then the resulting collection of data
  (*C^⊩, Prime(*C^⊩) →~ V) **yields a common container, namely, the Frobenioid *C^⊩** ...,
  in which **distinct choices of the [negative!] pilot element ∈ M = Pic(*C^⊩)** — hence
  also the data ... — **may be compared with one another**."
- L5261-5273: positive/negative pilot elements can only be compared inside such a common
  container (the comparison is of arithmetic degrees/heights of line bundles); embedding
  in a larger ambient category would make all objects isomorphic and the comparison
  meaningless. ⇒ the P5 comparison is a **degree comparison in Pic(*C^⊩)**, NOT a
  cross-domain (F→K) field transport.

## 3. Paper: normalizations

- IV L1359-1364: `|log q| := (1/(2l))·log(q)` (M-scale of the q-pilot log-volume).
- IV L1704-1741 (Step (v)): theta values are weighted by the local degrees
  `λ_v = [(Fmod)_v : Q_p]`; the outer Step (viii) sum over v_Q has no extra weight
  (IV L1860-1878).
- Def 1.9 (IV L1206-1235): normalized degree `deg(a) = (1/[K:Q])Σ_v c_v log q_v`;
- IV L1411-1425: S_ar layer difference F vs Ftpd <= 21 (absorbed in the 56 constant).

## 4. The precise statement R1 must prove

In Lean (current names):

```lean
-- q side (paper q_P5 = −|log q|):
qP5 := - (Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (l := l) T)
-- theta side (paper theta_P5 = |log Θ|, K-side lambda-weighted theta hull):
thetaP5 := Mzk1URThetaKSideActual.ksThetaHullLogRoot_lam (T := T)
-- R1 target:
theorem R1_p5 : qP5 <= thetaP5   -- i.e.  -M_paper_v2 <= ksThetaHullLogRoot_lam
```

Content of the proof (paper route):
1. **q-root lattice** `J_b`: the q-pilot element refines, on the K-side theta packet,
   to the q-root lattice (the q_v and their 2l-th roots, cf. the J1 Kummer-mass route
   in route §5.3 and IV L1359-1364); its log-volume is the M-scale `-M_paper_v2`.
2. **theta side full-fiber weighting**: the K-side theta hull log-volume
   `ksThetaHullLogRoot_lam = Σ_b (lamWeight b / dModF) * ksThetaHullLog b`
   (KSide:218 definitional) with the full-fiber weighting of the q-divisor; the
   F-side full-fiber realization is `qPilotMagnitudePaper_v2` and
   `M_paper_v2 = qPilotMagnitudePaper_v2 / (2l)`.
3. **common-container comparison**: both are (negative) pilot elements of
   `Pic(*C^⊩)`; the comparison is the arithmetic-degree comparison, giving
   `-M_paper_v2 <= ksThetaHullLogRoot_lam` up to the Ind1-3 indeterminacies which
   are part of the theta hull definition (possible images).

## 5. Our definitions realizing the three letters

| letter | Lean realization | note |
|---|---|---|
| q_P5 | `qP5 = -M_paper_v2`; `Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 = qPilotMagnitudePaper_v2/(2l)` | qPilotMagnitudePaper_v2 = (1/[F:Q])Σ_{P∈badFPrimeSet} f_P·c_P·log p_P, c_P = order |
| theta_P5 | `Mzk1URThetaKSideActual.ksThetaHullLogRoot_lam` (= Σ_b lamWeight/dModF · ksThetaHullLog) | K-side lambda-weighted theta hull, possible images |
| H_pkt | `Mzk1URThetaKSideActual.ucWeightedHpkt` with weight `lambda/dMod` (K-side packet hull) | kurt's `ksThetaHullLogRoot_le_ucWeightedHpkt` gives theta <= H_pkt |
| q-pilot object | q_v zero divisor; F-side realization via `qVFamTensorPlaces`/`qVFamAt` | log-volume M-scale |
| theta-pilot object | `{q_v^{j^2}}` zero divisor; K-side realization via `ksPlaces`/`ksBlock` | possible images subject to Ind1-3 |
| M_paper_v2 | `Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2` | = (1/2l)·log(q) per IV L1359-1364 |

## 6. What NOT to use

- F-side `PaperLevelXiFTargetActual.actualThetaHullLogRoot` (gamma-weighted
  possible-images hull) is NOT the paper theta_P5: it is an F-side internal hull;
  using it for C2 would be the wrong field/side (see `coord/C2-CALIBER-AUDIT.md`).
- `p6SandwichChain_neg_M_le_HTheta` / `ur_negM_le_Htheta` / Node09 P5 are F-side
  narrative results; not the paper theta_P5 for R1.
- `actualQPilotMagnitudeClassical` (gamma single-lift mixed weight) is NOT the paper
  q_pilot: the paper q-pilot log-volume is the F full-fiber degree (v2).

## 7. Two-sided consumption

- R1 lower bound for C2: `-M_paper_v2 <= ksThetaHullLogRoot_lam` (this doc).
- R1 upper bound (C3): `ksThetaHullLogRoot_lam <= ucWeightedHpkt` (kurt; lambda-weight
  Step(viii) version, Q=v2/M=M_paper_v2).
- Both are needed before `uc_c4_of_hthetaKSide` can consume the C2ThetaInputK with
  `M := MpaperV2`, `theta := ksThetaHullLogRoot_lam`.

## ADDENDUM 2026-11-18: R1 q-lattice paper-faithfulness check

Paper (IV L1359-1364): "the quantity |log(q)| ∈ R_{>0} defined in [IUTchIII], Corollary 3.12,
is equal to **(1/(2l))·log(q) ∈ R**" — i.e. the q-pilot log-volume is **exactly
(1/2l)·log(q)**; this is a fixed normalization, NOT a root/general scaling of the P5 object.

Consequences for the R1 q-lattice route:
- the q-root lattice `J_b` must have log-volume/mass **exactly `-M_paper_v2`** (q_P5), with
  `M_paper_v2 = qPilotMagnitudePaper_v2/(2l)`;
- the 2l-th root `r` (with `(1/2l)log|q| = log|r|`, IV L1360-1362) is internal to the Kummer
  mass computation; it must NOT be used to rescale q_P5 or to change the (1/2l) factor;
- no additional root/general scaling claim is licensed by the paper; any Lean lemma that
  rescales -M by a root index or by a general factor would be a misreading of IV L1359-1364.
Check when reviewing the q-lattice files: `nu(J_b) = -M_paper_v2` and the R1 target
`-M_paper_v2 <= ksThetaHullLogRoot_lam` (common-container comparison) stay in the
(1/2l)-normalized M scale.


## ADDENDUM 2026-11-18b: per-b normalization identity MpaperB_b = -qPilotMass(cP_b)

Source reads:
- `Mzk1ULOrdFiberTowerActual.MpaperB b = (1/(2l))·(1/[F:Q])·Σ_{P∈fiber_b} f_P·order_P·log p_P`
  (`orderAtFPlace`; log of `underIntGen` = log p_P; all P|b give the same rational p_b);
- `Mzk1URRootNuOnePlaceActual.qPilotMass cP = (1/(2l))·(-cP·log(qVFamTensorP T b))`,
  so `-qPilotMass cP = (1/(2l))·cP·log p_b`;
- `Mzk1URThetaHullInclusionActual.neg_Mpaper_v2_eq_sum_qPilotMass (cP)
  (h : ∀ b, MpaperB b = -qPilotMass (cP b)) : -M_paper_v2 = Σ_b qPilotMass (cP b)`
  — i.e. the per-b identity is an EXPLICIT HYPOTHESIS of the summation theorem.

Verification:
- signs and the 1/(2l) factor are consistent: MpaperB_b ≥ 0 and qPilotMass < 0 for cP > 0,
  so `MpaperB b = -qPilotMass (cP b)` ⇔ `MpaperB b = (1/(2l))·cP_b·log p_b`;
- no double e-division: neither side divides by e again (the M-scale is (1/2l) only;
  the raw v_P is inside `order_P` of MpaperB and inside cP via R0.1);
- **OPEN**: the per-b identity itself is NOT proved in the tree; it asserts
  `(1/[F:Q])·Σ_{P|b} f_P·order_P = cP_b`, i.e. exactly the R0.2/R0.1 per-b crosswalk
  `(1/[F:Q])Σ_{P|b} f_P v_P = ([Fmod_b:Q_p]/[Fmod:Q])·c_P` (route R0.2 formula).
  It holds when cP_b is *defined* as the fiber average; with cP = v_P/e_abs (route §2.1)
  it is a genuine crosswalk obligation (unramified/full-fiber normalization needed).
- paper anchor: IV L1359-1364 (`|log q| = (1/2l)log q`) confirms the (1/2l) M scale; it
  does NOT license a further root/general rescaling or a second /e.

=> Recorded as: signs/1/(2l)/no-double-e all **correct**; identity is currently a hypothesis
(`h`), to be discharged by the R0.2 per-b crosswalk — report to kurt/david.


### CORRECTION to ADDENDUM 2026-11-18b (Lead clarification, 2026-11-18)

With `cPFullFiber b := (1/[F:Q])·Σ_{P|b} f_P·orderAtFPlace(T,b,P)` (the paper full-fiber
coefficient), the per-b identity
  **`MpaperB b = -qPilotMass (cPFullFiber b)`**
is **DEFINITIONAL, not a crosswalk obligation** (`MpaperB` is (1/(2l)) times the same
full-fiber sum, and `qPilotMass` is (1/(2l))·(−cP·log p_b)).  The `hper : ∀ b, ...`
hypothesis in `Mzk1URThetaHullInclusionActual.neg_Mpaper_v2_eq_sum_qPilotMass` is discharged
by taking `cP := cPFullFiber`.

The REAL remaining dictionary item belongs to **R0.1/R0.2** and stays an explicit
hypothesis there (not in R1):
  **`cPFullFiber_b = ([Fmod_b:Q_p]/[Fmod:Q])·cP_local`**, with `cP_local = v_P/e_P^abs`
(route §2.1 R0.1) and the R0.2 full-fiber formula
`(1/[F:Q])Σ_{P|b} f_P v_P = ([Fmod_b:Q_p]/[Fmod:Q])·c_P`.

No double e-division: `cP_local` carries the single /e_abs; `cPFullFiber` is a weighted
average with no further /e; the M scale is only the 1/(2l) factor (IV L1359-1364).
Paper anchors unchanged: IV L1359-1364 (q-pilot log-volume = (1/(2l))log q).


## ADDENDUM 2026-11-18c: hperB verification vs IV L1359-1364 / R0.2

Read: `Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt (packetV)
(hperB : ∀ b, actualLocalHullLog T b <= packetV b) :
actualThetaHullLogRoot T <= ucWeightedHpkt (nativeBadLocalWeight T) packetV`,
and `Mzk1UCHthetaWiringActual.htheta_of_hperB` / `uc_c4` consumers.

Findings:
- `hperB` is a **per-b local hull bound on the F-side** `actualLocalHullLog`, weighted by
  `nativeBadLocalWeight` (gamma = 1/[K_w:Q_p]); the conclusion is about
  `actualThetaHullLogRoot` (F-side gamma-weighted possible-images hull).
- Paper (IV L1359-1364): the (1/2l) scale belongs to the **q-pilot log-volume**
  `|log q| = (1/2l) log q`; theta_P5 in the paper is the **K-side** theta hull
  (III L883-891; common container Pic(*C^⊩), III L5245-5260).  The F-side gamma-weighted
  `actualThetaHullLogRoot` is NOT the paper theta_P5 (see C2-CALIBER-AUDIT addendum).
- No double e-division: `hperB` contains no /e; gamma is a local-degree weight, not an
  e-division.  `hperB` itself carries NO (1/2l) factor (it is a raw local hull comparison);
  the (1/2l) enters the q side only through `M_paper_v2`.
⇒ `hperB` is a legitimate F-side per-b bound, but it **cannot serve as the paper θ_P5
comparison for C2**; the paper-faithful htheta input is kurt's K-side
`ksThetaHullLogRoot_le_ucWeightedHpkt` (lambda/d_mod weights).  Recorded as a
side/semantic mismatch for the C2 chain (kurt/david informed).


## ADDENDUM 2026-11-18d: hperB direction RESOLVED (hcoef' route) - arithmetic check

Lead/kurt resolution: `hperB` is provable via
  **`hcoef' : thetaLamWeight_b * urCeilC_b >= cPFullFiber_b / (2l)`**
(i.e. per b, θλ·ceil dominates cPFullFiber/(2l)), together with the DONE
`ksThetaHullLog_lower`; the old rootCoeff-based `hcoef` was wrong.

Arithmetic verification (no new Lean claimed here; names to be confirmed by kurt/david):
1. R0.2 per-b: `cPFullFiber_b = v_sel/d_mod`; `orderAtFPlace = e_P * v_sel`;
   `Σ_{P|b} f_P e_P = [F:Fmod]`; hence
   `(1/[F:Q])·Σ_{P|b} f_P·order_P = (1/([F:Fmod]·d_mod))·[F:Fmod]·v_sel = v_sel/d_mod
   = cPFullFiber_b`, so `MpaperB b = (1/(2l))·cPFullFiber_b·log p_b` (this is the
   definitional identity of ADDENDUM 2026-11-18b, now with the fiber sum evaluated).
2. Multiplying `hcoef'` by `log p_b > 0`:
   `thetaLamWeight_b·urCeilC_b·log p_b >= (cPFullFiber_b/(2l))·log p_b = MpaperB b`.
3. `ksThetaHullLog_lower` supplies the lower bound of the K-side theta hull log in the
   same weighted form, giving the per-b comparison and, summing with
   `thetaLamWeight_b >= 0`, the R1 target `-M_paper_v2 <= ksThetaHullLogRoot_lam`.

Checks:
- **no double e**: the e_P enters exactly once through `orderAtFPlace = e_P·v_sel` and the
  sum `Σ f_P e_P = [F:Fmod]`; `cPFullFiber` is then a pure v_sel/d_mod term with no
  further /e; the (1/2l) factor is the only scale beyond d_mod;
- **θλ >= 0**: `thetaLamWeight = λ/d_mod` with λ = local degree >= 0 and d_mod > 0, so the
  weighted sums preserve inequalities;
- **log p > 0**: needed for step 2 and valid for every bad rational prime p >= 2.
⇒ The direction conflict is resolved: use `hcoef'` + `ksThetaHullLog_lower`; do not use the
old rootCoeff-based hcoef.  kurt/david should cite the exact declaration names.


## ADDENDUM 2026-11-18e: FINAL R1 formulation = container / L_w root-extension (Lead decision)

Final R1 statement (supersedes the proxy-based presentation):
- **θ side = the O-saturation region of the SAME root generator** in the container/L_w
  root-extension formulation, **without any ceil**;
- **equality `Σ_b θλ_b · ν(Θ_b) = M_paper_v2`** (the container mass equals the paper
  q-pilot-full-fiber M magnitude), hence `-M_paper_v2 <= θ` (R1 target);
- the K-side `Mzk1URThetaKSideActual.ksThetaHullLogRoot_lam` is kept only as a **separate
  proxy** with an **explicit ceil discrepancy** (absorbed by the R2 packet/exceptional
  terms); it is **NOT the paper θ_P5 itself**.

Consistency with the common-container paper lines:
- III L872-877 (q-pilot object zero locus of q_v, log-volume -|log q|);
- III L883-891 (Θ-pilot object zero locus of {q_v^{j^2}}, log-volume of the holomorphic
  hull of the union of possible images, subject to (Ind1)-(Ind3));
- III L901-906 (sign convention |log Θ| := -(-|log Θ|));
- III L5245-5260 (common container = Frobenioid *C^⊩; distinct [negative] pilot elements
  in Pic(*C^⊩) may be compared with one another);
- IV L1359-1364 (|log q| = (1/2l) log q, the M scale used by the equality).
=> The container/L_w root-extension formulation is the paper-consistent one: both pilots
are elements of the same Pic(*C^⊩), the comparison is a degree comparison, the O-saturation
region of the root generator gives the θ side with no ceil, and the equality to M_paper_v2
uses exactly the (1/2l) normalization.

Consequences to record:
1. do not present `ksThetaHullLogRoot_lam` as the paper θ_P5; it is a proxy whose ceil
   discrepancy must be absorbed (R2 packet / exceptional terms);
2. the final R1 proof must produce `-M_paper_v2 <= θ_container` from the container equality
   `Σ_b θλ_b ν(Θ_b) = M_paper_v2`, with no ceil on the θ side;
3. the earlier K-side-only reading (Addenda 2026-11-18/18b/18c) is retained as the proxy
   analysis but is not the final R1 statement.


## ADDENDUM 2026-11-18f: per-b qPilotMass exact name

`Mzk1ULR1QPilotMassBasicActual.qPilotMass (cP : ℝ) := (1/(2l))·(−cP·log p)`;
`qPilotMass_eq : qPilotMass cP = −(cP/(2l))·log p` — the per-b paper mass used by
`MpaperB b = -qPilotMass (cPFullFiber b)` (definitional; ADDENDA 18b/18d).  With
`cPFullFiber = v_sel/d_mod` and the (1/2l) scale, this is IV L1359-1364 consistent;
no second /e (cP carries the unique e_abs).


## UPDATE 2026-11-18 18:04 batch: RootNu / CPrimeFiber / KHP5Bridge / Compositum

### R1 per-b identity tools (DONE)
- `Mzk1ULR1CPrimeFiberActual` **DONE 18:04:00**: `cPFullFiber (b) : ℝ` = (1/[F:Q])Σ f_P order_P;
  **`Qb_eq_cPFullFiber_mul_logp (b) (hprime : ∀ x∈fiber_b, underIntGen = qVFamTensorP T b) :
  Qb b = cPFullFiber b * log (qVFamTensorP T b)`** — this is the per-b Qb/cPFullFiber relation
  (R0.2 shape, conditional on the fiber-prime identity hprime).
- `Mzk1URRootNuOnePlaceActual` **DONE 18:04:01**: `qLatticeMass`, `qPilotMass`,
  `qPilotMass_eq`, `norm_eq_rpow_of_localNormOrder` (root-mass (1/2l) scale; no double e).
- `Mzk1URThetaKHP5BridgeActual` **DONE 18:04:18**:
  `neg_MpaperV2_le_thetaLam_of_bridge (hbridge : Σ_b θλ_b·(urCeilC_b·log p_b) ≤ M_paper_v2) :
  −M_paper_v2 ≤ ksThetaHullLogRoot_lam` — conditional terminal reduction (hbridge explicit).
  **FLAGS (mismatch)**: (i) the file docstring is internally inconsistent: lines 5-8 say the
  sufficient comparison is `S ≤ M_paper_v2` (matching the actual statement), while lines 9-10
  state `hbridge : M_paper_v2 ≤ Σ ...` (opposite direction); (ii) direction vs the corrected
  hcoef' route (ADDENDUM 18d: θλ·urCeilC ≥ cPFullFiber/(2l) ⇒ S ≥ M) differs: the bridge
  uses `S ≤ M` + hull lower bound `−S ≤ θ`, while the hcoef' route uses `S ≥ M` + `θ ≥ S`;
  kurt/Lead must confirm which hull bound is available (this determines the valid chase).

### R3 Compositum (DONE)
- `Mzk1G1F2ThetaCompositumActual` **DONE 18:04:57** (source clean, docstring says no sorry):
  `lTorsionX (lam l)`, **`ThetaCompositum (lam l) : IntermediateField ℚ ℂ`**,
  `Ftpd_le_ThetaCompositum`, `I_mem_ThetaCompositum`,
  `threeTorsionX_subset_ThetaCompositum`, `fiveTorsionX_subset_ThetaCompositum`.
- Note: this gives the compositum CONTAINMENT tower (Ftpd/I/3-/5-torsion x-coords ⊆ K),
  which addresses R3's field-construction layer; it does NOT prove the torsion-coordinate
  zero criteria ③ or enumeration ④ for n=5/l, and does not prove field EQUALITY ⑤.


## CLARIFICATION 2026-11-18g: KHP5Bridge direction resolved (Lead ruling)

- The KHP5Bridge statement is CORRECT as-is:
  `neg_MpaperV2_le_thetaLam_of_bridge
    (hbridge : Σ_b θλ_b·(urCeilC_b·log p_b) ≤ M_paper_v2) :
    -M_paper_v2 ≤ ksThetaHullLogRoot_lam`,
  because the hull lower bound `ksThetaHullLogRoot_lam_lower : −S ≤ θ` gives
  `−M_paper_v2 ≤ −S ≤ θ` (S := Σ_b θλ_b·urCeilC_b·log p_b).
- ONLY the docstring lines 9-10 of `Mzk1URThetaKHP5BridgeActual` are wrong (they state the
  reverse `hbridge : M_paper_v2 ≤ Σ ...`); fix the docstring to `S ≤ M_paper_v2`.
  **No code change, no new obligation.**
- The ADDENDUM 2026-11-18d direction (`hcoef' : θλ·urCeilC ≥ cPFullFiber/(2l)` ⇒ S ≥ M,
  used with `θ ≥ S`) is a DIFFERENT, NON-VIABLE chase for the container route; it should
  NOT be used for R1's container comparison.  (It remains at most a proxy-side note; the
  container route uses S ≤ M + `ksThetaHullLogRoot_lam_lower : −S ≤ θ`.)

### 2026-11-18 18:08 batch audit: KHP5Bridge docstring lines 9-10 now FIXED (reads hbridge : S <= M_paper_v2 => -M <= theta); statement unchanged; source newer than DONE 18:04:18 -> recompile in flight (olean stale at audit). RootNu/CPrimeFiber DONE 18:04:00-01 clean.
### 2026-11-18 18:12: KHP5Bridge re-DONE 18:12:16 with CORRECTED docstring (hbridge : S <= M_paper_v2 => -M <= theta via -M <= -S <= theta); mtime 18:08:44 < DONE, consistent. Infra wave 18:13-18:15 (heavy URThetaK*/G1* retries) is memory-spike, not code.

### 2026-11-18 18:52 BridgeQPaperM: FALSE auxiliary lemma removed (semantic mismatch record)

- `Mzk1ULBridgeActualQPaperMActual.actualQTerm` uses the SPECTRAL coefficient
  `QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient` (exponent·degree −
  normRatio correction, S121).
- The removed lemma `actualQTerm_eq_inv_degree_mul_order` claimed this equals
  `(1/[K_b:Q_p])·order(qVFamily b)·log p_b` — i.e. it silently identified the spectral
  coefficient with the RAW order, which holds only when `qVFamNormRatio = 1` (S121 iff).
  The lemma was therefore FALSE as stated (this is exactly the R0.1 spectral-vs-order
  mismatch); it was removed and replaced by a documented TODO: either use
  `QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient` (order coefficient) or carry
  the norm-ratio bridge as a hypothesis.
- The remaining main theorem `actualQ_eq_two_l_MpaperV2_of_per_b` is axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, latest print); its verdict is being
  recompiled after the edit.


## 2026-11-18 19:25 QPaperM DONE（R0 bridge）

- `Mzk1ULBridgeActualQPaperMActual` **DONE 19:25:29**; declarations:
  `noncomputable def actualQTerm (b)`, **`actualQ_eq_two_l_MpaperV2_of_per_b
  (hper : ∀ b, actualQTerm b = 2*l*MpaperB b) : actualQPilotMagnitudeClassical =
  2*l*M_paper_v2`**;
- axiom print latest: `[propext, Classical.choice, Quot.sound]` (clean); the log also contains
  STALE lines from earlier attempts (failed `unfold` on the spectral coefficient + an
  `INTERNAL PANIC: out of memory` infra line) - not the current verdict;
- the earlier FALSE auxiliary lemma `actualQTerm_eq_inv_degree_mul_order` was removed
  (spectral = order only when qVFamNormRatio = 1), per ADDENDUM 2026-11-18.

### 2026-11-18 19:40 MpaperBWeight DONE 19:40:56: Mzk1ULR1MpaperBWeightActual.{cPFullFiber, MpaperB_eq_neg_qPilotMass} clean trio (fiber-prime lemma natAbs(underIntGen P)=qVFamTensorP used).
### 2026-11-18 20:01 CanonicalLift file exists (Mzk1URCanonicalLiftActual, START 20:01:13): decls nativeBadLiftCanonical / _comap (rfl per source) / _comap_Fmod / canonicalLift_alignment (rfl) / canonicalQFamTensorPlace / _eq_contraction (rfl); claims NativeBadLiftAlignment becomes rfl - NOT yet kernel-verified; no lift_comap identifier.
### 2026-11-18 20:04 TensorQVFamAlignment file START 20:04:14 (pending): decls thetaTensorQVFamAlignmentOfActual (coefficients = gaussExponent*actualRootCoeff), _apply (rfl ksThetaCoeff), thetaTensorQVFamAlignmentObstruction_actual (Nonempty proof). Non-vacuous on Bad-indexed packet; specific tensor place alignment remains separate. No axioms yet.

## AUDIT 2026-11-18 20:1x: R1/R2 handoff (exact verdicts)

### R1 handoff: no hidden field
- `Mzk1URThetaHullInclusionActual.neg_Mpaper_v2_eq_sum_qPilotMass` (PROVED equality):
  `-M_paper_v2 = Σ_b qPilotMass (b) (cPFullFiber b)`;
- `negM_le_thetaLam_of_perB (cP) (hM : -M = Σ qPilotMass) (hperB : ∀ b, qPilotMass b ≤
  thetaLamWeight_b * ksThetaHullLog_b) : -M ≤ ksThetaHullLogRoot_lam` (sum assembly);
- `def hperB_target : Prop := ∀ b, qPilotMass (cPFullFiber b) ≤ thetaLamWeight_b * ksThetaHullLog_b`;
- `negM_le_thetaLam_of_hperB (h : hperB_target) : -M ≤ ksThetaHullLogRoot_lam`.
=> The target inequality is NOT hidden inside a new structure/field: the only hypothesis is
the PER-B inequality (strictly more granular than the sum target), and the final inequality is
obtained by `Finset.sum_le_sum`. `hperB_target` is the documented single R1 OPEN.

### Root extension / Theta inclusion names (RootExtension DONE 2026-11-16 12:41:43)
- `urRootAlpha`, `urRootAlpha_eq_unit` (rfl), `urRootAlpha_ne_zero`, `urRootAlpha_pow`;
- `urRootTheta (j)`, `urRootTheta_order`, `urRootTheta_order_base`, `urRootTheta_ne_zero`,
  `urRootTheta_log_norm_eq_neg_order`, `urRootTheta_log_norm_eq_neg_shift`,
  `urRootTheta_log_norm_eq_q`;
- printed axioms clean tri (`urRootTheta_log_norm_eq_neg_shift`, `urRootTheta_log_norm_eq_q`).

### IV:1585 per-row bounds (quoted)
- IV L1573: `≤ 2 d_mod (log d_Ftpd + log f_Ftpd) + 5 + log l`;
- IV L1575-1577: `(4/l)·log(s^Q) ≤ (8 d_mod/l)(log d_Ftpd+log f_Ftpd) + 6`;
- IV L1580-1584: `(1+4/l)·log(d_K) + (4/l)·log(s^Q) ≤ (1+12 d_mod/l)(log d_Ftpd+log f_Ftpd)
  + 2 log l + 52`;
- IV L1585-1598: (iv) upper bound for the procession-normalized mono-analytic log-volume of
  the holomorphic hull of possible images of a Θ-pilot, estimated at each vQ ∈ VQ.

### Step XI degree line
- Step (xi) of Cor 3.12 is referenced in III at L933/L1044 (two tautologically equivalent
  computations of q-pilot log-volume; Fig. I.8), L11009 (generalized Θ×μ discussion), L11166;
- the IV degree estimate used per row is the L1580-1584 display above.  No separate IV line
  labelled 'Step (xi) degree' exists in the repo text.

### 2026-11-18 20:30 FiberPrimeF DONE 20:30:00: qVFamTensorPlace_under / fiber_prime_consistency_F clean trio. RootExchangeSquare DONE 20:28:04: rootMass_eq_half_blockMass / thetaMass_eq_gauss_mul_alphaMass / thetaSum_eq_gaussSum_mul_alphaMass clean trio. BoxR2 DONE 20:27:15: actual_weightedAverage_le_of_distinguished clean trio.
### 2026-11-18 20:36 regressions: BoxR2 FAIL 20:34:53 code (43:1 unexpected token *; sorryAx in print); FiberCrosswalk FAIL 20:35:42 code (unsolved goal; sorryAx); BadPlace FAIL 20:30:01 code (unknown nativeBaseContractionFPlace); Protected FAIL 20:35:39 infra OOM (bad_alloc).

## DONOR STATEMENTS 2026-11-18 20:41 (S2746/S2796/S2797; verdict = NO-EVENT, source-only)

All five files are **NO-EVENT** (no watchdog verdict); statements from source:
- `S2746C3NormalizedHaarActual` (`tmp/sheaf/xif/paper/S2746C3NormalizedHaarActual.lean`):
  `noncomputable def c3TensorLatticeCompacts : TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3)` (:41);
  `noncomputable def c3NormalizedTensorHaar : Measure (C3LogShellTensorBlock C3) := Measure.addHaarMeasure (c3TensorLatticeCompacts …)` (:56);
  `theorem c3TensorLattice_self_measure : c3NormalizedTensorHaar (tensorLattice …) = 1` (:60);
  `theorem tensorLattice_subset_C3RegionAll (hρ : ∀ i, 0 ≤ C3PerPlaceUpdateRho …) : tensorLattice … ⊆ …` (:66);
  `theorem c3NormalizedTensorHaar_region_lt_top` (:85); `c3NormalizedTensorHaar_hge1` (:93).
- `S2796CoordinateLatticeSubsetAllRegionActual`: `theorem coordinateLattice_subset_regionAll (rho : ι → ℝ)
  (hρ : ∀ i, 0 ≤ rho i) : padicIntegerCoordinateLattice ⊆ {y | ∀ x : ι, Real.log ‖y x‖ ≤ ∑ i, rho i}` (:13).
- `S2796SupportAbsNormLeRadSqActual`: `theorem S2796_absNorm_supportIdeal_le_radSq {a b c} (habc : IsABCTriple a b c) :
  Ideal.absNorm (supportIdeal (K := GaussianField) (abcRationalPoint a c)) <= (natRadical (a*b*c))^2` (:25).
- `S2797ClauseA37ConditionalActual`: `noncomputable def S2797FieldOfModuli : SourceFieldOfModuli S2786Arithmetic` (:25)
  (with `jModuli := (110592/37 : GaussianField)`); `noncomputable def S2797ClauseA (S …) (hstable : ∀ p, …HasStableReductionAt p) : …` (:35).
- `S2797TensorLatticeSubsetAllRegionActual`: `theorem tensorLattice_subset_regionAll (rho : ι → ℝ)
  (hρ : ∀ i, 0 ≤ rho i) : tensorLattice (p := p) M ⊆ S2726PerPlaceUpdateRegionAll (p := p) M rho` (:22).

### 2026-11-18 20:50 DONE: BadPlaceActualMap re-DONE 20:46:17 (badPlaceCoeff/_norm/badPlaceQRegion/_nu clean trio); BoxR2PerRow 20:49:28 perRow_eq_collectionBound trio; FractionalLatticeNorm 20:49:32 padicFractionalLattice_log_norm_le trio; AlphaMassConnector 20:50:17 urRootAlpha_mass_eq_badPlaceQRegion_nu + urRootAlpha_pow_eq trio (Done variant START 20:49:28 duplicate pending).

## AUDIT 2026-11-18 21:0x: prior DONE chain vs R1 target (closure or mismatch)

### Exact statements (source)
- `PaperLevelXiFTargetProofActual` (DONE 2026-11-14 12:05:19):
  `perBQPilotLog b := qPilotClassicalLog (qVFamTensorPlaces T b) qVFamTensorTuple
   Measure.addHaar (rootNormCoefficient T b) (rootNormScalingData T b)`;
  `perBThetaHullLog b := rootThetaHullLog (qVFamTensorPlaces T b) qVFamTensorTuple
   Measure.addHaar (rootHalfCoefficient T b)`;
  **`perBQPilotLog_le_perBThetaHullLog (b) : perBQPilotLog b ≤ perBThetaHullLog b`**
  (via `RootNormalizedContainmentActual.qPilotNormLog_le_rootNormHullLog`, itself from
  `qPilotNormRegion ⊆ rootNormHull` = `qPilotClassicalRegion_subset_rootHull` using
  `rootHalfCoefficient_le_norm`);
  `globalQPilotLog := Σ_b nativeBadLocalWeight_b · perBQPilotLog_b`,
  `globalThetaHullLog := Σ_b nativeBadLocalWeight_b · perBThetaHullLog_b`,
  **`globalQPilotLog_le_globalThetaHullLog`**;
  `nativeBadLocalWeight_nonneg`.
- `Mzk1URThetaHullActual` (DONE 2026-11-16 13:02:55):
  **`ur_negM_le_Htheta : -actualQPilotMagnitudeClassical ≤ actualThetaHullLogRoot`**
  (via `p6_neg_M_le_HTheta2`); `ur_perB_containment` = re-export of the per-b inequality
  (axiom print clean tri: `[propext, Classical.choice, Quot.sound]`).
- `Mzk1MinimalAcceptanceActual` (DONE 2026-11-12 20:44:49):
  `LambdaG := arithmeticTupleFractionalLattice(...paperRootCoefficientFamily) *
   arithmeticTupleHolomorphicLattice(...)`;
  `LambdaG_eq_paperLambdaORegion` (rfl);
  **`LambdaG_subset_paperRootThetaImageNZ : (LambdaG : Set _) ⊆ paperRootThetaImageNZ`**
  (actual containment, j = 1 non-zero label);
  `LambdaG_subset_paperFaithfulThetaHullNZ`.
- `Mzk1PaperFaithfulHullActual` (DONE 2026-11-12 23:10:58):
  `paperFaithfulThetaImage := scaledRegion`, `paperFaithfulThetaImage_eq_scaledRegion`,
  **`paperFaithfulThetaHull_eq_closure_scaledRegion`**, `ind3OutputHull_measure_pos_lt_top`.

### Verdict: substantive F-side closure, but MISMATCH with the route's current R1
- The chain proves a **genuine actual-paper F-side containment and per-b/global weighted
  inequality**: qPilot region ⊆ root hull ⊆ paperFaithful hull, hence
  `perBQPilotLog ≤ perBThetaHullLog` and `globalQPilotLog ≤ globalThetaHullLog`, plus
  `-actualQPilotMagnitudeClassical ≤ actualThetaHullLogRoot`.
- It is **NOT** a closure of the route's current R1 target `-M_paper_v2 ≤ ν(Θ_paper)`
  (nor of the K-side proxy `-M ≤ ksThetaHullLogRoot_lam`), because:
  (i) the M side is `actualQPilotMagnitudeClassical` / `globalQPilotLog` (legacy
      gamma-weighted qPilotClassicalLog), not `M_paper_v2`;
  (ii) the Theta side is the F-side `actualThetaHullLogRoot` (gamma weights), not the
      container `ν(Θ_paper)` nor K-side `ksThetaHullLogRoot_lam` (lambda/d_mod);
  (iii) the weights are `nativeBadLocalWeight` (gamma), not route lambda/d_mod.
=> If R1 is *re-scoped* to the F-side legacy C2/P6 pair, this chain **closes it**;
   otherwise it supplies the F-side containment STEP and still needs the normalization
   bridge (gamma <-> lambda/d_mod, actualQ <-> M_paper_v2).

### Axiom verification
- `ur_perB_containment` -> `[propext, Classical.choice, Quot.sound]` (log print).
- Other three files' sources have NO `#print axioms` lines and their logs are not present;
  probe `_ProbeR1PriorChainAxiomsActual` (queued, NO-EVENT yet) will print them.


## VERDICT 2026-11-18 21:05: prior R1 chain axioms + rootNormHull vs paper Θ

### Probes DONE
- `_ProbePriorR1ChainActual` **DONE 21:05:45**: `perBQPilotLog_le_perBThetaHullLog`,
  `globalQPilotLog_le_globalThetaHullLog`, `ur_perB_containment`, `ur_negM_le_Htheta`,
  `LambdaG_subset_paperRootThetaImageNZ`, `LambdaG_subset_paperFaithfulThetaHullNZ` -> all
  `[propext, Classical.choice, Quot.sound]`.
- `_ProbeR1PriorChainAxiomsActual` **DONE 21:05:48**: also `nativeBadLocalWeight_nonneg`,
  `paperFaithfulThetaHull_eq_closure_scaledRegion`, `ind3OutputHull_measure_pos_lt_top` ->
  all `[propext, Classical.choice, Quot.sound]` (total 9/9 trio).

### rootNormHull = paper Θ? **NOT confirmed (deliberately not asserted)**
- `RootNormalizedContainmentActual.rootNormHull` is defined as
  `rootThetaHull (qVFamTensorPlaces T b) qVFamTensorTuple (rootHalfCoefficient)` with
  `rootHalfCoefficient := rootNormCoefficient / (2l)` and
  `rootNormCoefficient := qVFamNormalizedCoefficientFamily` (the SPECTRAL coefficient).
- The paper hull in `Mzk1PaperFaithfulHullActual` is
  `paperFaithfulThetaHull = closure (thetaTensorScaledRegion places tuple
   (fun _ => qVFamPaperRootCoefficient T b))` with
  `qVFamPaperRootCoefficient := ((qVFamily T b).order : ℝ) / (2*l.value)` (RAW order /2l).
- `RootNormalizedContainmentActual` file header explicitly states: **"No root hull equality
  is asserted."**; there is no `rootNormHull = paperFaithfulThetaHull` (nor vs
  `paperRootThetaImageNZ`) lemma in the tree.
- Coefficient gap: `rootHalfCoefficient = c_norm/(2l)` vs `qVFamPaperRootCoefficient =
  v/(2l)`; they coincide only when `qVFamNormRatio = 1` (S121), i.e. spectral = order.
=> Verdict: the prior chain proves the per-b/global inequality and containment for the
  NORMALIZED (spectral) coefficients, but it does **not** identify `rootNormHull` with the
  paper Θ hull; that identification is exactly the missing norm-ratio bridge.


## CORRECTION 2026-11-18 21:1x: rootNormHull IS route paper Θ (Lead route reading)

This SUPERSEDES the previous "rootNormHull = paper Θ unconfirmed" note.

- Route §2.1/§3.2 fixes the paper coefficient as **`c_P/(2l)` with `c_P = v_P(q_P)/e_P^abs`
  (spectral) = cNorm`**.  Hence the route paper Θ object is
  **`rootNormHull := rootThetaHull (qVFamTensorPlaces T b) qVFamTensorTuple rootHalfCoefficient`**
  with `rootHalfCoefficient := rootNormCoefficient/(2l)` and
  `rootNormCoefficient := qVFamNormalizedCoefficientFamily` (= spectral cNorm = c_P).
- The raw-order object `paperFaithfulThetaHull` (via
  `qVFamPaperRootCoefficient := (qVFamily).order/(2l)` = `e·c_P/(2l)`) is an **e-scaled
  DIFFERENT object**, not the route paper Θ.
- Therefore **no `qVFamNormRatio = 1` is needed** for route R1: the equality
  `rootNormHull = route paper Θ` holds by the route's coefficient convention, and the
  earlier claim that it was unconfirmed/required the norm-ratio bridge is RETRACTED.
- Consequence for the prior chain: `perBQPilotLog_le_perBThetaHullLog` uses exactly
  `rootHalfCoefficient` (c_P/(2l)) on the F-side actual objects ⇒ it is the route R1
  per-b statement; `globalQPilotLog_le_globalThetaHullLog` is its weighted global form
  (weights = nativeBadLocalWeight; if route weights are lambda/d_mod, the weight-change is
  the separate normalization item, not a coefficient/normRatio issue).

### 2026-11-18 21:5x verdicts: PaperBlockTarget DONE 21:01:06 (lambdaORegion_zero_mem_candidate/leastLambdaOHull_subset_lambdaORegion_zero/lambdaORegion_zero_measure_lt_top/paperHull_measure_lt_top/qPilotPaperRegionLog_le_paperHullLog_unconditional; axioms probe NO-EVENT). BoxR2RouteCheck DONE 21:06:33: def PaperThetaReadout_le_perBThetaHullLog := paperReadT <= perBThetaHull (target as named Prop); header states prior chain NOT paper R2 upper bound, missing bridge. hW files only row tables. localCompletionDegree duplicated name: absolute (P7ThetaDeg:30) vs relative (ProcessionNormalizationWeights:49).

## VERDICTS 2026-11-18 21:5x-22:0x: PaperBlockTarget hull / S716 / R2RouteCheck

### `Mzk1PaperBlockTargetActual` 21:01:06: S800 least hull, NOT paper Θ
- `qPilotPaperRegionLog_le_paperHullLog_unconditional : qPilotPaperRegionLog T b mu ≤
  paperHullLog T b mu`, where `paperHull`/`paperHullLog` is the **S800 least lambda-O hull**
  (`leastLambdaOHull` = intersection of `lambdaORegion c` candidates containing
  `paperPossibleImages`).
- File header GAP (quoted): "S800 paperHullLog is the least lambda-O hull at
  rootHalfCoefficient with SignedLabel (includes j=0), not the P4 paperFaithful NonzeroHull;
  no identification."
- Additionally `Mzk1PaperHullZeroLabelActual` **DONE 2026-11-12 22:01:09** proves
  `rootThetaRegion_zeroLabel_eq_RmulO`, `RmulO_subset_leastLambdaOHull`,
  **`leastLambdaOHull_eq_RmulO`**, `leastLambdaOHull_eq_holomorphic`, and `paperHullLog = 0`
  (file rows: "q-order independent; old S800 hull").
=> The block-target inequality is against a DIFFERENT (collapsed) hull whose normalized log is
   0; it cannot contribute to R1 paper Θ (= rootNormHull) without an identification that is
   not in the tree - it is at most a degenerate statement.

### `S716PaperThetaHullLogSourceAuditActual.paperPerBThetaHullLog_eq_ambientHullLog`
- Source (mtime 11-14 23:58): `paperPerBThetaHullLog := perBThetaHullLog`;
  `paperPerBThetaHullLog_eq_rootNormHullLog := rfl`;
  **`paperPerBThetaHullLog_eq_ambientHullLog := rfl`** (paper read = normalized log volume of
  `rootNormHull`); `paperGlobalThetaHullLog_eq := rfl`.
- VERDICT: file **NO-EVENT** and its **olean is STALE** (olean 10-30 01:00 < source 11-14
  23:58) -> the declarations are NOT verified/available; no axiom verdict.

### `Mzk1BoxR2RouteCheckActual` current source vs old DONE
- Current source (mtime 06:01:21) contains the inhabitant
  `paperThetaReadout_le_perBThetaHullLog_instance` (paperReadT := normalized log volume of
  `rootNormHull`; perBThetaHull := `perBThetaHullLog`), proved via
  `paperPerBThetaHullLog_eq_ambientHullLog`.
- BUT source is NEWER than olean (05:06:32), so the DONE 21:06:33 refers to the OLD
  content; the current source is UNCOMPILED; its log errors are
  `Mzk1BoxR2RouteCheckActual.lean:32:9: error: Function expected at Bad` and
  `:37:14: error: Unknown constant `perBQPilotLog_le_perBThetaHullLog_reuse`` (intermediate
  attempt), i.e. no valid verdict for the current inhabitant.


## VERDICTS 2026-11-18 22:06-22:10 (compile request state + new fails)

- `S716PaperThetaHullLogSourceAuditActual`: **NO-EVENT** (target present in
  `dag/watchdog/extra-targets.txt`, requeued; watchdog still busy with a 77-pending queue,
  no START/log yet). No DONE/error available; not using the stale 10-30 olean.
- `Mzk1BoxR2RouteCheckActual` current source: **not yet recompiled** (status still old DONE
  21:06:33; source newer than olean 05:06:32). Pending in the same queue.
- `Mzk1URPaperThetaR1FinalActual` **FAIL 22:10:31 = CODE** (log
  `dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1URPaperThetaR1FinalActual.lean.log`):
  - `:31:19: error(lean.unknownIdentifier): Unknown identifier `Mzk1ULR1CPrimeFiberActual.cPFullFiber``
  - `:33:16: error(lean.unknownIdentifier): Unknown identifier `Mzk1ULR1CPrimeFiberActual.Qb``
  - `:34:6: error(lean.unknownIdentifier): Unknown identifier `cPFullFiber``
  - `:30:29` / `:32:30` / `:36:16: error: Invalid argument name `l` for function`
  - `:44:50: error(lean.unknownIdentifier): Unknown identifier `thetaLamWeight_pos``
  - current `#print axioms neg_Mpaper_le_paperThetaSum` shows **`sorryAx`**.
- `Mzk1G1F2ThetaPaperCoefficientBridgeActual`: **START 22:10:32** (no verdict).
- `Mzk1PaperBlockTargetActual`: **discarded** for R1 purposes (S800 least hull;
  `leastLambdaOHull = RmulO = holomorphicLattice`, `paperHullLog = 0` in
  `Mzk1PaperHullZeroLabelActual`; degenerate, not paper Θ).


## VERDICT 2026-11-18 22:22: RouteCheck recompile attempt (stale)

- `S716PaperThetaHullLogSourceAuditActual` **DONE 22:15:21** (fresh); its declarations print
  `paperPerBThetaHullLog` and **`paperPerBThetaHullLog_eq_ambientHullLog :
  paperPerBThetaHullLog T b = arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
  qVFamTensorTuple Measure.addHaar (rootNormHull T b)`**, plus `PaperHullVsS663ThetaAverageGap`.
- `Mzk1BoxR2RouteCheckActual` last verdict **FAIL 22:22:09**; log errors:
  `:32:9 error: Function expected at Bad` (Bad unknown),
  `:37:14 error(lean.unknownIdentifier): Unknown constant `perBQPilotLog_le_perBThetaHullLog_reuse``,
  `:49:8 error: (deterministic) timeout at `isDefEq` (200000)`,
  `:54:14 error(lean.unknownIdentifier): Unknown constant `paperThetaReadout_le_perBThetaHullLog_instance``,
  `:54:8 isDefEq timeout`, `:59:14 Unknown constant paperThetaReadout...`.
  The line numbers/content (`_reuse`, `Bad`) do NOT match the current 58-line source
  (which now imports QVFamTensorCoefficientActual/RootNormalizedContainment/
  FinitePlaceNormalizedUnitScalingLogVolume/SourcePlacePartitionReduction/
  SourceDefinition31NativeContractBridgeReduction and has the inhabitant at lines 41-52),
  and the source mtime (22:23:19) is LATER than the FAIL -> verdict is STALE; no valid
  DONE/axiom verdict for the readout bridge yet.


## VERDICTS 2026-11-18 22:27-22:35 (exact, fresh)

- `Mzk1URPaperThetaR1FinalActual` **re-DONE 22:27:20**: `neg_Mpaper_le_paperThetaSum` ->
  `[propext, Classical.choice, Quot.sound]`; probe `_ProbeR1FinalAxiomsActual` **DONE 22:30:17**
  confirms the same trio.
- `Mzk1ULR0QMEndpointActual` **DONE 22:27:56** (adjacent batch).
- `Mzk1G1F2R2RowVAssemblyActual` **DONE 22:34:48**: `rowV_le_collectionChoiceBound` ->
  `[propext, Classical.choice, Quot.sound]` (later print; an earlier sorryAx line is stale).
  Statement: `arithmeticTupleNormalizedLogVolume places tuple D.mu (packetHull D) ≤
  collectionChoiceBound l (Real.log p) iotaL j d oq et idag`, from
  `packetHull_normalizedLogVolume_le_box` + `packetHull_le_collectionChoiceBound`
  with hypotheses `hslot`, `hd`, `hexc` (no equalities).
- `Mzk1BoxR2RouteCheckActual` **DONE 22:35:22**: the inhabitant
  `paperThetaReadout_le_perBThetaHullLog_instance` prints
  `[propext, Classical.choice, Quot.sound]` (final blocks; the `set_option` syntax error and
  `sorryAx` lines in the log are from earlier pre-fix attempts).  The `set_option` placement
  was fixed (file-level `set_option maxHeartbeats 4000000`), and the inhabitant uses
  `S716.paperPerBThetaHullLog_eq_ambientHullLog` (paper read = rootNormHull ambient log).


## VERDICTS 2026-11-18 22:38-22:41 (R1/R2 audit)

- `Mzk1G1F2JbRootMassRouteActual` **DONE 22:38:33**: `noncomputable def rootLatticeJ`,
  **`rootLatticeJ_subset_rootNormHull` -> `[propext, Classical.choice, Quot.sound]`**;
  probe `_ProbeJbRouteActual` **DONE 22:41:23** confirms same trio.
  (Sibling variants `JbRootMassRoute{Done,Fresh,Fresh2,Fresh3}Actual` are FAILs of earlier
  attempts - superseded by the green base file.)
- `Mzk1ULR1RootHullAssemblyActual` **NO-EVENT** (no verdict); source: single theorem
  `rootHull_assembly`.
- `Mzk1BoxR2RowPacketWiringActual` **FAIL 22:41:45 = CODE**:
  `Mzk1BoxR2RowPacketWiringActual.lean:66:2: error(lean.unknownIdentifier): Unknown identifier `refine``
  (tactic `refine` used in a term/command position).
- `Mzk1BoxR2RouteCheckActual` **DONE 22:35:22** (inhabitant `paperThetaReadout_le_perBThetaHullLog_instance`
  tri) - re-confirmed in this audit.


## VERDICTS 2026-11-18 22:43-22:47 (Jb / Assembly / R2ActualInstantiation)

- `Mzk1G1F2JbRootMassRouteActual` **re-DONE 22:43:17**: `noncomputable def rootLatticeJ`,
  **`rootLatticeJ_subset_rootNormHull` -> `[propext, Classical.choice, Quot.sound]`** (print).
- `Mzk1ULR1RootHullAssemblyActual`: **NO valid verdict** - running with INFRA/dependency
  read failures (log `dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1ULR1RootHullAssemblyActual.lean.log`):
  `:2:0: failed to read file '...\LeanFormal\IUT\IUTII\Frobenioid\Example36SourceModelDivisor.olean'`,
  `'...Mathlib\Combinatorics\SimpleGraph\Clique.olean.private'`,
  `'...Mathlib\Data\List\DropRight.olean'`; source has single theorem `rootHull_assembly`.
- `Mzk1G1F2R2ActualInstantiationActual` **FAIL 22:46:51 = CODE**:
  `Mzk1G1F2R2ActualInstantiationActual.lean:67:17: error(lean.unknownIdentifier):
  Unknown identifier `collectionChoiceBound`` (missing import/open of
  `StepVProcessionAverage`); its `sorryAx` axiom prints are from pre-fix attempts (source says
  no sorry at line 14 docstring).


## VERDICTS 2026-11-18 22:49-22:51 (Jb / Assembly / ActualInstantiation / LeH)

- `Mzk1G1F2JbRootMassRouteActual` **DONE 22:43:17** (source has 2 declarations):
  `noncomputable def rootLatticeJ` (line 44),
  **`rootLatticeJ_subset_rootNormHull` (line 50) -> `[propext, Classical.choice, Quot.sound]`**.
  (Note: 2 declarations in the green file; the '''trio''' is the axiom trio of the theorem.)
- `Mzk1ULR1RootHullAssemblyActual` **DONE 22:50:53**: **`rootHull_assembly` ->
  `[propext, Classical.choice, Quot.sound]`** (previous attempt was infra: missing
  `Example36SourceModelDivisor.olean` + mathlib `.olean.private` Clique/DropRight).
- `Mzk1G1F2R2ActualInstantiationActual` **FAIL 22:50:50 = CODE**:
  `Mzk1G1F2R2ActualInstantiationActual.lean:83:4: error: Application type mismatch:
  The argument d has type ι → ℝ of sort Type v but is expected to have type ℝ of sort Type
  in the application paperBound_le_collectionChoiceBound l (Real.log ↑p) iotaL (↑j) d`
  -- argument order/type mismatch at the bridge call (d/oq vs lam/dsum/exc positions).
- `Mzk1BoxR2PaperThetaLeHActual` **FAIL 22:51:04 = CODE**:
  `:35:53: error: (deterministic) timeout at `isDefEq` (max heartbeats 200000)`
  and `:45:14: error(lean.unknownIdentifier): Unknown constant `paperThetaWeighted_le``.


## VERDICTS 2026-11-18 22:54-22:55 (R1.1 probe / R2 LeH / Instantiation / RowPacket)

- `_ProbeRootHullAssemblyActual` **DONE 22:54:28**: prints
  `Mzk1ULR1RootHullAssemblyActual.rootHull_assembly` -> `[propext, Classical.choice, Quot.sound]`
  (R1.1 assembly trio confirmed).
- `Mzk1BoxR2PaperThetaLeHActual` **DONE 22:55:34**: `noncomputable def paperThetaReadoutB (b)`,
  **`paperThetaWeighted_le (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ)` ->
  `[propext, Classical.choice, Quot.sound]`**.
- `Mzk1G1F2R2ActualInstantiationActual` **FAIL 22:55:12 = CODE**:
  `:27:5: error: unknown namespace `LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage``;
  `:68:17: error(lean.unknownIdentifier): Unknown identifier `collectionChoiceBound``;
  `:83:4: error: Application type mismatch` (the earlier d : ι→ℝ vs ℝ mismatch).
  Root cause: the module `LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage` is not
  imported (or imported under a wrong path), so `collectionChoiceBound` is unknown.
- `Mzk1BoxR2RowPacketWiringActual` **FAIL 22:45:34 (no log file)** - stale/no-log verdict;
  the last content-bearing error seen was `:66:2: Unknown identifier `refine``.


## AUDIT 2026-11-18 23:0x: row-V / paperΘ identification and R2 verdicts

### DONE with exact names + axioms (verified)
- `Mzk1ULR1RootHullAssemblyActual` **DONE 22:50:53**: `rootHull_assembly` ->
  `[propext, Classical.choice, Quot.sound]` (probe `_ProbeRootHullAssemblyActual`
  **DONE 22:54:28** prints the same trio).
- `Mzk1URPaperThetaR1FinalActual` **DONE 22:27:20**: `neg_Mpaper_le_paperThetaSum` -> trio
  (probe `_ProbeR1FinalAxiomsActual` DONE 22:30:17).
- `Mzk1G1F2JbRootMassRouteActual` **DONE 22:43:17**: `rootLatticeJ` (def),
  `rootLatticeJ_subset_rootNormHull` -> trio.
- `Mzk1G1F2R2ActualInstantiationActual` **DONE 22:58:40**: `packetHull_le_collectionChoiceBound`
  -> trio (`#print axioms` clean; only unused-`logp` warning).
- `Mzk1BoxR2PaperThetaLeHActual` **DONE 23:01:51**: `paperThetaReadoutB` (def),
  `paperThetaWeighted_le` -> trio (print from the 22:55 green run).
- `Mzk1G1F2R2RowVAssemblyActual` **DONE 22:34:48**: `rowV_le_collectionChoiceBound` -> trio.
- `Mzk1BoxR2RouteCheckActual` **DONE 22:35:22**: inhabitant
  `paperThetaReadout_le_perBThetaHullLog_instance` -> trio.
  This is the row-V <-> paperTheta readout identification: `paperReadT :=` the ambient
  `rootNormHull` normalized log volume; identified with `perBThetaHullLog` via
  `S716.paperPerBThetaHullLog_eq_ambientHullLog` (defeq), so the comparison is `≤` refl.
  `Mzk1BoxR2IntegrationActual` **DONE 20:52:49** and `Mzk1BoxR2StepVBridgeActual`
  **DONE 22:09:23** (obsolete equality `hparam`; ignored per ruling).

### Current FAIL
- `Mzk1BoxR2RowPacketWiringActual` **FAIL 23:03:27 with NO LOG FILE** (verdict records
  "(no log file)"); no file:line error is available for this run.  Last content-bearing
  error from the earlier 22:41 attempt was
  `Mzk1BoxR2RowPacketWiringActual.lean:66:2: error(lean.unknownIdentifier): Unknown identifier
  `refine``.


## VERDICTS 2026-11-18 23:06 (R2 current)

- `Mzk1BoxR2PaperThetaLeHAssemblyActual` **NO-EVENT** (not compiled); source single theorem
  `paperThetaWeighted_le_H (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ)`.
- `Mzk1BoxR2RowPacketWiringActual` **FAIL 23:06:07 = CODE**: unsolved goal
  `arithmeticTupleNormalizedLogVolume places tuple (D t).mu (packetHull (D t)) ≤
  collectionChoiceBound l (Real.log ↑p) iotaL j d oq t slot`; its
  `actual_weightedAverage_le_collectionBound_rowPackets` print shows **`sorryAx`**.
  (needs the per-packet application of `packetHull_le_collectionChoiceBound` at `D t`).
- `Mzk1BoxR2PaperThetaLeHActual` **FAIL 23:06:05 = INFRA (OOM)**: log ends
  `libc++abi: terminating due to uncaught exception of type std::bad_alloc: std::bad_alloc`;
  the previous green run **DONE 23:01:51** (`paperThetaReadoutB`, `paperThetaWeighted_le` trio)
  remains the valid verdict.
- `Mzk1G1F2R2ActualInstantiationActual` **DONE 22:58:40** (unchanged):
  `packetHull_le_collectionChoiceBound` -> trio.
- `_ProbeR2AxiomsActual` **NO-EVENT** (not yet scheduled/started).


## AUDIT 2026-11-18 23:12: R2 row-V vs paperΘ readout identification

### Exact carriers/readouts
- `Mzk1BoxR2RowPacketWiringActual.rowPackets_weightedAverage_le_H` (namespace
  `Mzk1BoxR2PaperThetaLeHFinalActual`): V is
  `fun t => arithmeticTupleNormalizedLogVolume places tuple (D t).mu (packetHull (D t))`,
  on the GENERIC carrier `ArithmeticTensorTupleBlock places tuple` (variables
  `K p places tuple J E`).
- `Mzk1BoxR2PaperThetaLeHActual.paperThetaReadoutB (b) :=
  `arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
  Measure.addHaar (rootNormHull (l := l) T b)`, on `qVFamTensorBlock T b`.

### Identification verdict: NOT defeq, NOT covered; missing identification is explicit
- Carriers differ (generic `places/tuple` vs `qVFamTensorPlaces T b/qVFamTensorTuple`);
  readout objects differ (`packetHull (D t)` vs `rootNormHull T b`).
- No defeq/type equality and no transfer lemma: `rowPackets_weightedAverage_le_H` is stated
  directly for the actual packet hulls and its header says a `rootNormHull ⊆ packetHull`
  transfer is not needed FOR THE ROW BOUND; it does not identify with `paperThetaReadoutB`.
- `Mzk1BoxR2PaperThetaLeHAssemblyActual` header names the gap:
  "The remaining identification (weighted row-V average vs sum_b thetaLamWeight *
  paperThetaReadoutB) is the named RouteCheck gap and is NOT assumed as equality here."
- Exact missing object: an identification/inequality relating
  `Σ_t W(t)·vol(packetHull (D t))` with `Σ_b θλ_b·paperThetaReadoutB b`, which requires
  (i) `places := qVFamTensorPlaces T b`, `tuple := qVFamTensorTuple`, `mu := Measure.addHaar`,
  and (ii) a `packetHull (D b) = rootNormHull T b`-type comparison (or its inequality);
  also an index matching between row tuples `Fin (j+1) → ι` and bad indices `Bad ...`.

### Current verdicts (source-vs-verdict)
- `Mzk1BoxR2RowPacketWiringActual`: source mtime 23:10:25 > last FAIL 23:06:07; verdict
  **FAIL 23:06:07 with NO LOG FILE** (no file:line error available); earlier content error was
  `:66:2: Unknown identifier `refine``; current source has single theorem
  `rowPackets_weightedAverage_le_H`.
- `Mzk1BoxR2PaperThetaLeHAssemblyActual`: source mtime 23:10:19; **NO-EVENT**; single theorem
  `paperThetaWeighted_le_H (H : ℝ) (w : Bad ... → ℝ)`.
- `Mzk1BoxR2PaperThetaLeHActual`: source mtime 23:02:32 > DONE 23:01:51; latest verdict
  **FAIL 23:06:05 = INFRA OOM** (`libc++abi: terminating ... std::bad_alloc`); the 23:01:51
  green run (`paperThetaReadoutB`, `paperThetaWeighted_le` trio) is for older content.
- `_ProbeR2AxiomsActual`: **NO-EVENT**.


## EXACT R2 FINAL VERDICTS 2026-11-18 23:19-23:25

DONE (fresh, mtime < DONE):
- `Mzk1G1F2R2ActualInstantiationActual` **DONE 22:58:40** (mtime 22:56:10):
  `packetHull_le_collectionChoiceBound` -> `[propext, Classical.choice, Quot.sound]`.
- `Mzk1BoxR2PaperThetaLeHActual` **DONE 23:19:16** (mtime 23:13:23):
  `paperThetaReadoutB` -> `[propext, Classical.choice, Quot.sound]`;
  `paperThetaWeighted_le` -> `[propext, Classical.choice, Quot.sound]`.

FAIL / pending:
- `Mzk1BoxR2RowPacketWiringActual` **FAIL 23:18:08 = CODE** (source mtime 23:25:51 is NEWER,
  so this verdict is stale):
  - `Mzk1BoxR2RowPacketWiringActual.lean:72:21: error: Application type mismatch: The argument
    Real.log_pos hp2 has type 0 < Real.log ↑p but is expected to have type
    -LocalFieldLogarithm.localNormOrder p (D t).varpi < -(↑j ^ 2 / (2*l) * oq (t slot))
    in the application le_of_lt (Real.log_pos hp2)`
  - `:73:28: error: Application type mismatch: The argument hd t has type Σ localNormOrder …)
    ≤ Σ d (t i) but is expected to have type Σ over exceptional … ≤ 4*(j+1)*iotaL
    in the application packetHull_le_collectionChoiceBound (D t) l (Real.log ↑p) iotaL j t slot
    d oq ?m.478 ?m.479 (hd t)`
  - `:73:8: error: linarith failed to find a contradiction`
- `Mzk1BoxR2PaperThetaLeHAssemblyActual` **NO-EVENT** (single theorem
  `paperThetaWeighted_le_H`).
- `_ProbeR2AxiomsActual` **NO-EVENT**.


## EXACT R2 FINAL AUDIT 2026-11-18 23:28-23:30

DONE:
- `Mzk1BoxR2RowPacketWiringActual` **DONE 23:28:07**: `rowPackets_weightedAverage_le_H` ->
  `[propext, Classical.choice, Quot.sound]`.
- `Mzk1G1F2R2ActualInstantiationActual` **DONE 22:58:40**: `packetHull_le_collectionChoiceBound` -> trio.
- `Mzk1BoxR2PaperThetaLeHActual` **DONE 23:19:16**: `paperThetaReadoutB` -> trio;
  `paperThetaWeighted_le` -> trio.

`hread` statement (file `Mzk1BoxR2PaperThetaLeHFinalActual.lean`, NO-EVENT):
- line 40: `theorem paperTheta_le_H_of_perB (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ) ...`
- **line 48-54: `theorem paperTheta_le_H_of_rowAverage
  (H : ℝ) (w : Bad (nativePlaceSelection T) → ℝ) (hw : ∀ b, 0 ≤ w b)
  (hH : (∑ b, w b * perBThetaHullLog T b) ≤ H)
  (rowAvg : ℝ)
  (hread : (∑ b, w b * paperThetaReadoutB (l := l) T b) ≤ rowAvg)
  (hrow : rowAvg ≤ H) :
  (∑ b, w b * paperThetaReadoutB (l := l) T b) ≤ H := le_trans hread hrow`**
- `hread` is an explicit INEQUALITY (paper readout sum ≤ row-V weighted average), not an
  equality; the theorem composes it with `hrow : rowAvg ≤ H`.

NO-EVENT (not compiled):
- `Mzk1BoxR2PaperThetaLeHAssemblyActual` (single theorem `paperThetaWeighted_le_H`)
- `Mzk1BoxR2PaperThetaLeHFinalActual` (`paperTheta_le_H_of_perB`, `paperTheta_le_H_of_rowAverage`)
- `_ProbeR2AxiomsActual`


## EXACT FIRST ERRORS 2026-11-18 23:35 (hread / LeHAssembly / LocalStepV)

- `Mzk1BoxR2PaperThetaLeHFinalActual` (hread file; START 23:35:29) -
  `Mzk1BoxR2PaperThetaLeHFinalActual.lean:42:53: error: Function expected at
  perBThetaHullLog but this term has type ?m.14` (applied to `T`; missing import/open of the
  module defining `perBThetaHullLog`); second error `:50:53` same.
- `Mzk1BoxR2PaperThetaLeHAssemblyActual` (START 23:35:29) -
  `:48:53: error: Function expected at perBThetaHullLog but this term has type ?m.14`
  (same missing import/open as above).
- `Mzk1G1F2R2LocalStepVActual` (START 23:35:29) -
  `:27:39: error: Function expected at rootNormedExtension but this term has type ?m.4`
  (applied to `T`; missing import/open); also `:28:45 Function expected at …` and
  `:28:3: error(lean.unknownIdentifier): Unknown identifier `Integers``.


## DONE 2026-11-18 23:5x: `R2PerRowBoxActual` (per-row B_j and exceptional/different bounds)

- File `tmp/sheaf/xif/paper/R2PerRowBoxActual.lean`, direct-compiled (watchdog OFF):
  **exit=0**, three theorems, all `[propext, Classical.choice, Quot.sound]`:
  - `noncomputable def perRowBox (lam dsum exc logp : ℝ) : ℝ := (-lam + dsum + 1) * logp + exc`
    (paper per-row box `B_j(t,s)`, IV L1691-1696);
  - **`perRowBox_le_collectionChoiceBound (hslot : (j²/(2l))·oq(et idag) ≤ lam)
    (hd : dsum ≤ Σ_i d(t i)) (hexc : exc ≤ 4(j+1)·iota) (hlogp : 0 ≤ logp) :
    perRowBox lam dsum exc logp ≤ collectionChoiceBound l logp iotaL j d oq et idag` -> trio**;
  - **`exceptional_bound_of_r4 (hsub : Istar ⊆ I) (hcard : I.card = j+1)
    (hR4 : ∀ i ∈ Istar, p ≤ el ∧ log(e i) ≤ -3 + 4 log el) :
    Σ_{i∈Istar} (3 + log(e i)) ≤ 4(j+1)·(if p ≤ el then log el else 0)` -> trio**
    (from the StepV donor `exceptionalSum_le_r4`);
  - **`perRowBox_le_collectionChoiceBound_of_r4 ... :
    perRowBox lam dsum (Σ_{i∈Istar} (3+log(e i))) logp ≤ collectionChoiceBound l logp
    (if p ≤ el then log el else 0) j d oq et idag` -> trio**.
- Donors used: `LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean`
  (`collectionChoiceBound` line 125, `exceptionalSum_le_r4`); inequalities only (hslot/hd/hexc/
  hlogp), no equalities as source data.


## AUDIT 2026-11-18 23:5x-00:0x: procession donors vs real gaps (route §4.2)

### `Mzk1URThetaProcessionActual` - direct compile exit=1
Reusable (DONE within file):
- `noncomputable def urProcessionV (n) (D Q S T') (j) := collectionBound (2n+1) D Q S T' j` (:39);
- `noncomputable def urProcessionAvg := ULPacketHullValue` (:44);
- `noncomputable def urProcessionBound := ULPacketHullBound` (:48);
- `theorem urProcessionAvg_le_bound (hn : 2 ≤ n) (hD hS hT) : avg ≤ bound` (:52) -
  print `[propext, Classical.choice, Quot.sound]`.
Error / gap:
- `Mzk1URThetaProcessionActual.lean:73:9: error: (deterministic) timeout at `isDefEq`,
  maximum number of heartbeats (2000000)` inside `nu_ksThetaHull_le_nu_ceilRegion` (:65) -
  performance/elaboration timeout, not a missing statement.
- **Real gap**: `def stepV_hullVolume_le_processionAvg (b) (n D Q S T') : Prop` (:85) -
  documented R2 OPEN (geometric StepV source map hull -> procession average; route 4.2
  mechanism 2/3).

### `ProcessionThetaPacketAverageActual` - direct compile exit=0 (no sorry in source)
Reusable:
- `abbrev c3ThetaCard : Nat := Fintype.card (SignedLabel l.value)` (:63); `c3ThetaCard_pos` (:65);
- `noncomputable def c3ThetaProcession (C3) : WeightedValues (SignedLabel l.value)` (:71)
  (value j = log (C3.thetaPacket.scale j), uniform weight 1/card);
- `c3ThetaProcession_average : average = thetaPacket.logVolume / card` (:86);
- `c3ThetaProcession_weights_nonnegative` (:94);
- `c3ThetaProcession_average_nonpos (hQ : ThetaPacketQIdentification)` (:103);
- `actualThetaPacketAverage_eq_c3Procession_average` (:116);
- `processionEqThetaPacketAverage_of_procession_eq` (:124);
- `paperThetaMagnitudeComparison_of_procession_eq` (:135).
Gap:
- `def PaperProcessionEqC3ThetaProcession` (:147) - `Prop` identifying the paper procession
  with the canonical C3 packet procession; consumed by
  `processionEqThetaPacketAverage_of_paperProcessionEq` (:155).  No inhabitant/instance in
  this file - named real gap.

### `Mzk1URPacketActualInstanceActual` - direct compile exit=1 (INFRA)
- `Mzk1URPacketActualInstanceActual.lean:14:0: error: failed to read file
  '...Mathlib/MeasureTheory/Measure/MeasureSpaceDef.olean.private'` - infra read failure
  (no code verdict this run).
Reusable (source):
- `urActualB` (:57) - FIXED via `Classical.choose (V_mod_bad_nonempty)`;
- `urPacketP := qVFamTensorP T (urActualB T)` (:62); `urPacketSlot : qVFamTensorV := ()` (:65);
- `urPacketTuple : qVFamTensorV → Unit := fun _ => ()` (:68); `urPacketQ` (:71);
- `qReading_formula_actual` (:76); `qRootLattice_actual` (:84); `thetaSourceSpan_actual` (:92);
- `referenceLattice_actual` (:96); `urPhi_actual := ksThetaPhi (urActualB T)` (:102);
- `urPhi_actual_id_mem` (:108); `isClosed_productHull` (:118); `isClosed_packetHull_actual` (:138);
- `update_single_eq_localGenerator` (:168); `thetaImageSet_subset_possibleImages_actual` (:178);
- `ksThetaHull_subset_packetHull_actual` (:208); `urCeilLocalGenerator_ne_zero` (:228);
- `ksThetaHullLog_le_urPacketV_K` (:236).
**Real gaps (route §4.1)**: index is degenerate - `urActualB` is a single chosen bad place,
`urPacketP` uses that fixed b, `urPacketSlot := ()`, `urPacketTuple := fun _ => ()`; there is
no real (b,j,slot) procession index, no row regions H_bj / V_bj, and the source map
`urPhi_actual` is defined only at `urActualB` (not a per-row transport to a procession product).


## FULL-REPO SEARCH 2026-11-19 00:2x: F-side hperB / containment / different correction

### F-side containment `actualLocalHullRegion ⊆ arithmeticTupleHolomorphicHull(StepVPossibleImages)`
Already present (candidates, no new file needed):
- `FsideHperBActual.lean:50` `actualLocalHullLog_le_packetV_of_containment (e) (istar) (varpi) (Phi)
  (hcont : actualLocalHullRegion T b ⊆ arithmeticTupleHolomorphicHull (qVFamTensorPlaces T b)
  qVFamTensorTuple e (arithmeticTupleStepVPossibleImages … istar varpi Phi)) (hpos) (hfin) :
  actualLocalHullLog T b ≤ packetV e istar varpi Phi` - hcont is EXACTLY the containment;
  proof via `arithmeticTupleNormalizedLogVolume_mono`.
- `FsideHperBActual.lean:111` `actualLocalHullRegion_subset_hull_of_rows (hrows : ∀ j,
  actualRootThetaRegion T b j ⊆ arithmeticTupleHolomorphicHull e (StepVPossibleImages …)) :
  actualLocalHullRegion T b ⊆ …` - reduces containment to per-row containment (closure of
  union inside closed hull); `:90 isClosed_arithmeticTupleHolomorphicHull'`.
- `FsideHperBActual.lean:72` `fside_thetaHull_le_ucHpkt (V) (hperB : ∀ b, actualLocalHullLog b ≤ V b) :
  actualThetaHullLogRoot ≤ ucWeightedHpkt (nativeBadLocalWeight) V` - assembly.
- `Mzk1URThetaHullNonzeroActual` `urActualLocalHullRegion_eq_holomorphic :
  actualLocalHullRegion T b = (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
  qVFamTensorTuple : Set _)` - hull = holomorphic lattice identity (equality; useful with
  monotonicity but does not by itself give the StepV possible-image containment).
- Core donors: `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean:668
  def arithmeticTupleStepVPossibleImages`; `:678 measure_arithmeticTupleStepVPossibleImages_pos`;
  `:720 arithmeticTupleStepVPossibleImages_subset_endpoint`;
  `FinitePlaceStepVJInvariant.lean:71`; `Cor312CarrierRealizationSpec.lean:281-282
  possibleThetaPilotImage_subset_sourceHolomorphicHull` (K-side StepXI hull, not F-side).

### F-side alignment / different-index correction
- `Mzk1URThetaTransportActual.lean:83` `RootTensorVolumeAlignmentAt (b) : Prop :=
  `actualLocalHullLog b = Real.log ‖(urRootAlpha T b : urRootCarrier T b)‖`;
  `:90` `RootTensorVolumeAlignmentWithCorrection (b) (Delta) : Prop := actualLocalHullLog b + Delta
  = Real.log ‖urRootAlpha T b‖`; `:142 rootHullScalingFormulaAt_of_alignment`;
  `:151 ur_htheta_of_alignment`.
- `FsideVolumeAlignmentActual.lean:29` `rootLogNorm_eq_localRootLogVolume`; `:37
  fsideHullLog_eq_localRootLogVolume_sub_correction (Delta) (h : actualLocalHullLog + Delta =
  log‖sourceRootQUnit‖) : actualLocalHullLog = localRootLogVolume - Delta`; `:47
  fsideHullLog_eq_localRootLogVolume_of_alignment (halign : RootTensorVolumeAlignmentAt)`.
- `FsideGeneratorTransportActual.lean:33 fsideRootGenerator`, `:36 ne_zero`, `:40 pow`,
  `:47 actualRootCoeff_eq_half_order`, `:57 fsideVolumeFormula`.
- `Mzk1URThetaHperBReductionActual.lean:47` `hperB_of_coeffScale_le (b) (hlogp : 0 < log p)
  (hlam0 : 0 ≤ thetaLamWeight) (hcoef : thetaLamWeight·urCeilC ≤ cPFullFiber/(2l)) : …`;
  `:68 urCeilC_ge_actualRootCoeff`; `:80 hcoef_prime`.
- `Mzk1LpDifferentBoundActual.lean:31` `localDifferentPaperOrder_le_degree_padicVal'`;
  `:46 localDifferentPaperOrder_le_boundedDegree`; `:68 localDifferentOrder_eq_paperOrder_mul_ramification`.
- `LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualTensorInclusion.lean:701`
  `noncomputable def localDifferentPaperOrder : ℝ`;
  `LocalDifferentUpperBound.lean:138 localDifferentPaperOrder_le_degree_padicVal`
  (Prop 1.3(ii): ≤ localDifferentPaperOrder K + padicValNat p (finrank K L) + 1/logShellRamificationExponent);
  `LocalDifferentNormOrder.lean:25/55/74` norm-order lemmas.
- `BadPlaceRootHullScalingFormulaActual.lean:89` and `BadPlaceHalfRootSupplyActual.lean:104/118`
  take `(hull_eq : actualLocalHullRegion = …)` as an explicit hypothesis (completion-root form).

### Coverage verdict
- Containment: covered by `FsideHperBActual` (per-row -> hull reduction + log inequality);
  the missing piece is the per-row containment `actualRootThetaRegion ⊆ hull(StepVPossibleImages)`
  (source-action/Ind input), NOT a new file.
- Correction: `RootTensorVolumeAlignmentWithCorrection` and
  `fsideHullLog_eq_localRootLogVolume_sub_correction` exist but take `Delta`/`h` as INPUT;
  there is NO lemma identifying `Delta_b` with `localDifferentPaperOrder` (named gap);
  `localDifferentPaperOrder_le_degree_padicVal` is its only bound donor.
- Compile state: `FsideGeneratorTransportActual` exit=1
  (`:52:6 failed to synthesize Fintype (Bad (nativePlaceSelection T))`;
  `:62:11 Function expected at Integers`); `FsideVolumeAlignmentActual` exit=1
  (`:30:16 Function expected at sourceRootQUnit`); other F-side files pending direct compile.

