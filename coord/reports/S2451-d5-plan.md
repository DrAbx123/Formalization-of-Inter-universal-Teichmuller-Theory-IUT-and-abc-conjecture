# S2451: D5 non-compiling plan for S2446 and final integration

Date: 2026-11-03. BUILD HOLD: no lake/lean commands run for this report.

## S2446D5FinalActual.lean status

Source SHA256: 4B4F9FACEC6015988BF08BB8CD77DAC5641E87533F92B67F7F84D2F7844ECB19
olean: not produced (build hold).

### s2446FiberEquiv

The final `refine` block is:

  refine ⟨fun x => ⟨x.1.1, ?_⟩,
          fun y => ⟨⟨y.1, hroot y y.2⟩, ?_⟩, ?_, ?_⟩
  · exact congrArg Subtype.val x.2
  · apply Subtype.ext
    exact y.2
  · intro x
    apply Subtype.ext
    rfl
  · intro y
    apply Subtype.ext
    rfl

The earlier failure was in the FOURTH field: after
`apply Subtype.ext` the goal is

  ↑((fun x => ⟨↑↑x, _⟩) ((fun y => ⟨⟨↑y, _⟩, _⟩) y)) = ↑y

so the term must be `rfl` (both sides are literally the same E-element).
Putting `exact y.2` there was wrong and caused the last compile error.

Proof obligations:
1. forward property: `minpoly F x.1.1 = b.1`, from `congrArg Subtype.val x.2`;
2. inverse property: `s2425RootFactor (⟨y.1, hroot y y.2⟩) = b`, from
   `Subtype.ext; exact y.2`;
3. left_inv: `Subtype.ext; rfl`;
4. right_inv: `Subtype.ext; rfl`.

`hroot` uses `Polynomial.mem_normalizedFactors_iff` on `b.2` to get
`hb_monic`, `hb_irr`, `hb_dvd`; then `minpoly.aeval`, `b.1 ∣ fbar`, and
`Polynomial.mem_rootSet'` with the monic image nonzero.

### s2446Fiber_card

  rw [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (s2446FiberEquiv K L f p P hmonic hsep b)]
  change (s2408FiberSet b.1).ncard = b.1.natDegree
  exact s2408FiberSet_ncard K L f p P hmonic hsep hsplit b.2

Potential compile risks after build resume:
- `change` must see `{y // minpoly F y = b.1}` as the subtype underlying
  `s2408FiberSet b.1`; if not, use `show` plus `Nat.card_coe_set_eq`;
- `Nat.card_congr` orientation must rewrite `Nat.card fibre` to the target;
  if reversed, use `(Nat.card_congr e).symm`.

## Integration plan after S2446 compiles

Let β := {g : F[X] // g ∈ normalizedFactors (fbar f p)}.

1. root factor map:
   p := s2425RootFactor f p P hmonic hsep :
        (fbar f p).rootSet E -> β.
   Need Fintype β: use `Fintype.ofFinite β` if `Finite β` is synthesized
   from the finite multiset, or β := subtype of `normalizedFactors.toFinset`
   with `Fintype` from the finset subtype.  DecidableEq β by classical.

2. fibre card:
   hcard b := s2446Fiber_card f p P hmonic hsep hsplit b.

3. fibre invariance:
   hinv x := s2425RootFactor_permBar f p P hmonic hsep x.

4. fibre transitivity:
   for b, x, y with p x = b, p y = b:
   - b.2 gives g=b.1 monic irreducible and g ∣ fbar;
   - p x=b gives minpoly F x.1=g, so aeval x.1 g=0 (minpoly.aeval);
   - same for y;
   - S2339FrobTransitive f p P hb_monic hb_irr hb_dvd gives
       exists n, (frobBar p P)^[n] x.1 = y.1;
   - convert to `(permBar (f:=f) p P).SameCycle x y`.
   The conversion frobBar-iterate -> permBar-power is the next formal
   sub-lemma; use `frobBar` definition / `Equiv.Perm` power lemmas.

5. apply S2217:
   cycleType_eq_fiber_sizes (permBar p P) p (fun b => b.1.natDegree)
     hinv hcard htrans.
   Result:
     (permBar p P).cycleType
       = (Finset.univ.filter (fun b => 2 ≤ b.1.natDegree)).val.map
           (fun b => b.1.natDegree).
   Need to identify the RHS with
     ((normalizedFactors (fbar f p)).map natDegree).filter (fun n => 2 ≤ n).
   This is a finset/multiset normalization using
   `normalizedFactors_nodup`; the exact missing API is the equality
   between `Finset.univ` of the factor subtype and the normalizedFactors
   multiset with natDegree, after filtering size ≥ 2.

6. S2428 filter:
   s2428_filter_fiberSizes_eq_factorDegrees_filter gives
     ((normalizedFactors ...).map (fun g => (s2408FiberSet g).ncard)).filter (2≤·)
       = (factorDegrees ...).filter (·≠1).
   Combined with hcard (fibre card = natDegree), this yields
     (permBar p P).cycleType = (factorDegrees ...).filter (·≠1).

7. S2440 cycle transfer:
   for sigma with IsArithFrobAt O_K sigma P,
   s2440_permBar_cycleType_eq_rootCycleType gives
     rootCycleType K L f hsplit sigma
       = (factorDegrees (fbar f p)).filter (·≠1).

8. final corrected theorem:
   choose sigma := arithFrobAt (O_K) (Gal L/K) P (S2167FrobeniusExists);
   conclude DedekindFrobeniusCycleTypeStatementCorrected and
   DedekindFrobeniusOrbitSizeStatement (add fixed points/1s via
   orbitSizeMultiset and cycleType).

## Exact current first missing

1. S2446 not compiled: after build resume, rerun S2446 gate; expected
   right_inv=rfl fix to close s2446FiberEquiv, then check s2446Fiber_card
   direction/change.
2. Fintype instance for the normalized-factor subtype.
3. frobBar-iterate -> permBar-power/SameCycle conversion.
4. Finset.univ filter/map normalization to the normalizedFactors multiset.

D5 corrected theorem NOT accepted; no fake.

## Upstream clean

- S2440RootPermCycleCleanActual: EXIT=0, olean before build hold.
- S2428FilterBridgeActual: EXIT=0, olean before build hold.
- S2425PermBarInvarianceActual, S2420DedekindApplyActual: clean.
- S2427RootPermCycleActual: contains sorryAx; forbidden.
