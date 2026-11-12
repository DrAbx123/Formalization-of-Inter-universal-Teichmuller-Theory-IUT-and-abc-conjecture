# D5 large-image gate status (build incident pause)

Date: 2026-11-03. No new compilation performed after the Mathlib artifact
incident. This report records proof status only.

## Clean gate files (compiled EXIT=0 before the incident; source/olean hashes match)

- S2440RangePairTransitiveSubagentActual.lean
  source 18883 B, SHA256 f28e328d7574ac8d7f4c858fa60fb32ed04fc248d2a96253050f6219e35442b1
  olean 271464 B, SHA256 f29846e9ef9fb0bde5683c30559783c45b28dfc69e4dd03c70e9c6076bdfbcd6
- S2442QE5DegreeOrderSubagentActual.lean
  source 17683 B, SHA256 4f8cc5931797582759a8f460994519451b08586e6b82a79c60574646c7f02bb4
  olean 402368 B, SHA256 d64997a5785a99267ca0bb776deef686ee2ec75c655a9c92cfb22cc6712b067c
- S2445D5LargeImageChainActual.lean
  source 6034 B, SHA256 e34bad303d2ed93f11c3fe8cf569331c6395097dcf2ae79d6cdb6c06f0ca4387
  olean 44368 B, SHA256 25020ad028104d2a1f84b95eb8f2efb322c78e1105e4d55005efab733311b9a7
- S2449D5FinalStatusActual.lean
  source 2313 B, SHA256 d18371ddcc6c4266fdb055d732b286aada1b599973da903637f549503cdfa587
  olean 18024 B, SHA256 d5511703ebf0198e16ebef0470bbf226af320c8ce2ae8d932629e6366c0005fd

Axioms for the checked theorems in these four: propext, Classical.choice,
Quot.sound only.

## Pair transitivity

S2440 provides actual reductions:
- SL2(F5) is pair-transitive;
- S1725ImageTail -> PairTransitive(range), hence S1987D5LargeImageFive ->
  PairTransitive(range);
- a 12-cycle in the actual range -> PairTransitive(range);
- under HasCycleType102, PairTransitive(range) <-> S1725ImageTail.

The target itself is NOT proved:
  S2203RangePairTransitiveRequired S1982Basis.

## Cycle type

S2461CycleTypeFinalActual.lean is UNVERIFIED/STALE: source is 25963 B with SHA
c5da57b1e9bd63508caf0eec7eeeab5af4573bfce84cfc6cbd0c3312c8da4297, but the
olean (88680 B, SHA 6fbaf697b7a3cc0c71018ad538f01ddcebc5e6f509368d200ec65737844b842b)
was built from an earlier smaller source. Do not consume until recompiled by the
build coordinator.

S2460PairTransitiveFinalActual.lean is UNVERIFIED: source 21384 B, SHA
172c5991a405c9d5fa33b057fc0ba8e3e335442b890030208fedcca15132a762, no olean.
Do not consume.

S2462FullQE5FieldActual.lean is INCOMPLETE/INVALID (source 67 B, stale olean);
do not consume.

The exact cycle-type target remains:
  S2203RangeCycleTypeRequired S1982Basis.

## Degree = image order

S2442 proves under the explicit projective bridge
  S2442Psi5ProjectiveBridge : S2304Gal ~= GL2 / {+-I}
that
  Module.finrank Q s2289QE5 = 240,
not 480, and refutes S2445DegreeEqImageOrder and the original
S2445ExactFirstMissing. s2289QE5 is the splitting field of psi5 (x-coordinates),
not the full 5-division field Q(E[5]). A genuine 480 theorem needs a different
full 5-division field object; it is not a missing proof of s2289QE5 degree.

## D5 final status

The D5 target is NOT actual. Exact missing:

  S2449D5ExactFirstMissing
    = S2445GroupRouteExact
    = PairTransitive(range) at S1982Basis
      AND HasCycleType102(range) at S1982Basis.

Conditional theorem only:
  S2449D5LargeImageFive_of_exact :
    S2449D5ExactFirstMissing -> S1987D5LargeImageFive.

No conditional identity is announced as actual. No fake, no sorry, no axiom.

## Build incident

Mathlib build artifacts are missing (LibraryRewrite.olean, Bochner/Set.olean,
UniformField.olean, and transient .olean.private/.ir failures). All lake/lean
commands stopped; awaiting build coordinator.
