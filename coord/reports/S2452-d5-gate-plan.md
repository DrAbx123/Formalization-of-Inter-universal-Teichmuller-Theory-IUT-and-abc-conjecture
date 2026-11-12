# S2452: D5 PairTransitive / cycle-type proof plan (build hold)

Date: 2026-11-03. NO compilation was run for this report. It records proof
status, exact missing lemmas/APIs, and the serial rebuild order after the
Mathlib-artifact incident is resolved.

## 1. Current gate status (pre-incident oleans; do not rebuild in parallel)

Clean and source/olean-consistent:
- S2440RangePairTransitiveSubagentActual: src 18883
  f28e328d7574ac8d7f4c858fa60fb32ed04fc248d2a96253050f6219e35442b1,
  olean 271464 f29846e9ef9fb0bde5683c30559783c45b28dfc69e4dd03c70e9c6076bdfbcd6.
- S2442QE5DegreeOrderSubagentActual: src 17683
  4f8cc5931797582759a8f460994519451b08586e6b82a79c60574646c7f02bb4,
  olean 402368 d64997a5785a99267ca0bb776deef686ee2ec75c655a9c92cfb22cc6712b067c.
- S2445D5LargeImageChainActual: src 6034
  e34bad303d2ed93f11c3fe8cf569331c6395097dcf2ae79d6cdb6c06f0ca4387,
  olean 44368 25020ad028104d2a1f84b95eb8f2efb322c78e1105e4d55005efab733311b9a7.
- S2449D5FinalStatusActual: src 2313
  d18371ddcc6c4266fdb055d732b286aada1b599973da903637f549503cdfa587,
  olean 18024 d5511703ebf0198e16ebef0470bbf226af320c8ce2ae8d932629e6366c0005fd.

Unverified / do not consume:
- S2461CycleTypeFinalActual: current src 25963
  c5da57b1e9bd63508caf0eec7eeeab5af4573bfce84cfc6cbd0c3312c8da4297,
  but olean 88680 6fbaf697b7a3cc0c71018ad538f01ddcebc5e6f509368d200ec65737844b842b
  was built from an earlier 7666-byte source. STALE.
- S2460PairTransitiveFinalActual: current src 21384
  172c5991a405c9d5fa33b057fc0ba8e3e335442b890030208fedcca15132a762,
  no olean. UNVERIFIED.
- S2462FullQE5FieldActual: invalid/incomplete placeholder; do not consume.
- S2465D5FinalIntegrationActual: EDITED after its last clean compile (B2 link
  added); current source is unverified. Recompile last in the serial order.

## 2. Actual PairTransitive target

Target (all definitionally equal):
  S2203RangePairTransitiveRequired S1982Basis
  = PairTransitive (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))
  = S2375ExactFirstMissing = S2378ExactFirstMissing.

Kernel-checked reductions (S2440 and S2460 source):
- S2440SL2PairTransitive: SL2(F5) is pair-transitive on the twelve pairs.
- S2440RangePairTransitive_of_imageTail:
  S1725ImageTail S1987Five S1982Basis -> target.
- S2440RangePairTransitive_of_largeImage:
  S1987D5LargeImageFive -> target.
- S2440RangePairTransitive_of_twelveCycle:
  a 12-cycle in the actual range -> target.
- S2440RangePairTransitive_iff_imageTail_of_cycleType102:
  HasCycleType102 -> (target <-> S1725ImageTail).
- S2440RangePairTransitive_iff_forall_basis: basis independence.
- S2460 source additionally identifies matrix pair cycle type with the root
  permutation cycle type and defines S2460RootTwelveCycleRequired; the file is
  unverified and must be recompiled.

What is missing (exact first missing):
  S2460RootTwelveCycleRequired
  := exists sigma : Gal(closure F' / F'), the induced permutation of the twelve
     roots of prePsi_5 is a 12-cycle.
Equivalent sufficient form: S2440TwelveCycleInputRequired (a 12-cycle on the
twelve S2009 pairs in the actual range).

Required lemmas/APIs to close it:
1. Mod-13 finite-field certificate:
   S2460Mod13Certificate
   := Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 13))).
   The actual integer model S2132Psi5Z exists; the irreducibility proof is
   missing. Do not confuse with the mod-29 degree-ten S2126 result.
2. Dedekind-Frobenius orbit/cycle comparison:
   S2217Missing (DedekindFrobeniusOrbitSizeTheorem): factorization degrees of
   the reduction equal the Frobenius cycle type on roots. Mathlib v4.32.2 has
   arithmetic Frobenius arithFrobAt but no orbit-size comparison.
3. Q-level to F'-level transport / linear disjointness:
   F' cap Q(E[5]) = Q (S2253IntersectionIsBot / S2270DegreeProduct) and the
   resulting restriction surjectivity; without this a Q-Frobenius 12-cycle does
   not automatically lift to Gal(closure F'/F').
4. Root <-> affine-pair equivariance on the actual curve:
   S2056RootPairEquiv plus the S2460 bridge
   S2460pairPerm_cycleType_eq_rootPerm (source, unverified).

## 3. Actual HasCycleType102 target

Target:
  S2203RangeCycleTypeRequired S1982Basis
  = HasCycleType102 (range rho_{5,S1982Basis})
  = exists h in range, (pairPermHom h).cycleType = {10,2}.

Kernel-checked reductions in S2461 source (stale olean; recompile first):
- S2461Target_iff_range, S2461Target_iff_range1982.
- S2461cycleType_pairPermHom_conj / S2461HasCycleType102_map_conj.
- S2461RangeCycleType_congr, S2461Target_iff_basis,
  S2461Target_iff_forall_basis, S2461Target_iff_exists_basis.
- S2461Target_iff_exists_sigma.
- S2461PairPerm_cycleType_eq_rootPerm and
  S2461Target_iff_exists_rootCycle.
- S2461FirstMissing := exists sigma, root permutation cycle type {10,2};
  S2461FirstMissing_iff_target proves it is exactly the target.
No inhabitant of S2461FirstMissing is produced.

Required lemmas/APIs to close it:
1. A repaired mod-29 factorization object. The S2057Mod29FactorizationData is
   empty/false (S2132); the true product carries the scalar 4
   (S2132CorrectedProduct), and the recorded product without 4 is false
   (S2132RecordedProduct_false). The degree-ten factor irreducibility is
   S2126/S2094 (f irreducible) after scaling by the unit 4; the quadratic
   factor and the product still need the corrected statement.
2. Dedekind-Frobenius cycle comparison at a prime above 29, including the
   arithmetic Frobenius element and the residual factorization-to-cycle-type
   theorem (S2217Missing).
3. Local/global transport: the relative Frobenius at 29 over F' is affected by
   the residue degree/inertia (S2167 records 29 inert in Q(sqrt(-3))); need
   the linear-disjointness/restriction surjectivity input from S2253/S2328.
4. The actual matrix element in rho_5(range) and the pair/root cycle-type
   equality (S2461 source).

## 4. Full Q(E[5]) degree 480 question

S2442 proves that s2289QE5 = SplittingField(prePsi_5), the x-coordinate field,
has degree 240 under the explicit bridge S2442Psi5ProjectiveBridge:
  S2304Gal ~= GL2(F5)/{+-I}.
It refutes S2445DegreeEqImageOrder and the original S2445ExactFirstMissing.
Do NOT present s2289QE5 as the full 5-division field.

If the paper needs degree 480, a separate object is required:
- full 5-division field K = Q(x(P), y(P) : P in E[5], P != 0);
- construction of y(P) from the Weierstrass equation and the quadratic fibre;
- proof that K has degree |image| = 480 under the large-image hypothesis;
- proof K is Galois and its Galois group is the full matrix image.
None of these objects/APIs exists in the tree. Exact missing: a full
5-division field construction and its degree theorem, not a proof about
s2289QE5.

## 5. Integration status and exact D5 missing

S2449D5FinalStatusActual (clean) defines:
  S2449D5ExactFirstMissing = S2445GroupRouteExact
  = PairTransitive(range at S1982Basis) AND HasCycleType102(range at S1982Basis).
S2449D5LargeImageFive_of_exact is conditional only. No actual
S1987D5LargeImageFive is constructed.

Exact D5 first missing:
  (A) PairTransitive(range at S1982Basis), with sufficient inputs
      S1725ImageTail or a 12-cycle in the range;
  (B) HasCycleType102(range at S1982Basis), equivalently S2461FirstMissing
      (root cycle type (10,2)).
Degree 480 is not part of the D5 target; it is a separate refuted/corrected
degree question.

## 6. Serial compile order after build coordinator clearance

1. Confirm Mathlib/toolchain artifacts are restored; run only one lean process.
2. S2440RangePairTransitiveSubagentActual.lean (fresh olean).
3. S2445D5LargeImageChainActual.lean (imports S2440).
4. S2442QE5DegreeOrderSubagentActual.lean (imports S2445).
5. S2449D5FinalStatusActual.lean (imports S2442/S2445/S2440).
6. S2461CycleTypeFinalActual.lean (discard stale olean; recompile current src).
7. S2460PairTransitiveFinalActual.lean (no olean; compile current src).
8. S2462FullQE5FieldActual.lean only if completed.
9. S2465D5FinalIntegrationActual.lean (imports S2449/S2440/S2442/S2461).
Each step: EXIT=0, source SHA, olean SHA, #print axioms trio; only then
advance. Do not compile files in parallel.

## 7. Verification caveat

The Mathlib incident shows concurrent lake builds can remove/alter .olean/.ir
files. Until coordination, no command should be run. The status above is
based on the last consistent compiles; S2461/S2460/S2462 are explicitly
unverified and must not be cited as actual.
