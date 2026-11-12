# S1866: apex coherence for the coherent covers — reduction, no-go, and the exact first missing

Status: proof file compiled, EXIT=0, no warnings, no `sorryAx`; axiom footprint is the
allowed trio only.  `S1854PullbackApexCoherent` / `S1854CoproductApexCoherent` are
**not** proved.  The exact first missing is named at the presentation level and proved
equivalent to S1854's conditions.

## Target

    S1854PullbackApexCoherent h  :
      for every cospan of underlying covers of coherent covers, the chosen
      Limits.pullback f g is the underlying cover of some coherent cover;
    S1854CoproductApexCoherent h0 h2 :
      the chosen initial object and binary coproducts of coherent covers are
      underlying covers of coherent covers.

These are the inputs S1854/S1856 need for `HasPullbacks` / `HasFiniteCoproducts`
on `CoherentCover` (S1856's transports themselves are already theorems).

## Verdict

Not proved.  The obstruction is the recorded weak presentation datum of the chosen
apex, not the categorical transport:

* a cover carries a recorded `EtaleStackFiniteEtaleMorphism`; coherence is a property
  of that presentation, not of the underlying stack map;
* the S1728 apex is an opaque choice inside the Prop-valued `HasPullbacks` /
  `HasInitial` / `HasBinaryCoproducts`; limits determine it only up to isomorphism;
* coherence is not invariant under isomorphism of recorded covers, proved concretely:
  `S1762TerminalCover` is coherent, `S1850DoubledCover` is not, they have the same
  source and structure map, and they are isomorphic in `S1728Cover`
  (`S1866TerminalDoubled_iso`).

A stronger no-go is also proved: the *same* identity cospan of the terminal cover
admits two `S1832TwoPullback` data, with apex `S1762TerminalCover`
(`S1866TerminalApexTwoPullback`) and apex `S1850DoubledCover`
(`S1866DoubledApexTwoPullback`).  Hence the S1832 universal property alone does not
determine the coherence of the apex, and "every two-pullback apex is coherent" is
false (`S1866TwoPullbackApexAllStrong_false`).

## What is proved

1. `S1866StrongCoverOf Y` (the recorded weak structure of `Y` admits a strong
   refinement with the *same* base-change presentations);
   `S1866StrongCoverOf_iff_baseChange` identifies it with `∀ T q,
   S1852ConeEssSurj (Y.finiteEtale.baseChange T q)`, and `..._iff_coherent` with
   `∃ C : CoherentCover, C.cover = Y`.

2. Exact first missing, pullbacks:

       S1866PullbackApexFirstMissing h  :=  ∀ cospan of coherent covers, ∀ T q,
         S1852ConeEssSurj ((Limits.pullback f g).finiteEtale.baseChange T q)

   with `S1866PullbackApexFirstMissing_iff : ... ↔ S1854PullbackApexCoherent h`.
   The predicate depends only on the Prop-valued `HasPullbacks` structure
   (`..._irrelevant`).

3. Exact first missing, finite coproducts:

       S1866CoproductApexFirstMissing h0 h2
         := strong recorded presentations of ⊥_ S1728Cover and of every
            A.cover ⨿ B.cover,

   with `S1866CoproductApexFirstMissing_iff : ... ↔ S1854CoproductApexCoherent h0 h2`,
   and the S1833 affine-equivalence form `S1866CoproductApexFirstMissingAffine e`
   (using S1833's `S1833InitialObj e` and `S1833CoproductObj e A B`), with
   `..._iff : ... ↔ S1854CoproductApexCoherent (S1833HasInitial_of_affineEquiv e)
   (S1833HasBinaryCoproducts_of_affineEquiv e)`.

4. Consumers, at both hom universes:
   * `S1866HasPullbacks`, `S1866HasFiniteCoproducts` at
     `S1854CoherentCategory11` (via S1856);
   * `S1866HasPullbacks01`, `S1866HasInitial01`, `S1866HasBinaryCoproducts01`,
     `S1866HasFiniteCoproducts01` at the target universe
     `S1854CoherentCategory01` (via S1857);
   * the S1833 affine specializations `S1866HasPullbacks_of_affineEquiv`,
     `S1866HasFiniteCoproducts_of_affineEquiv`.
   The S1856 first-missing statements are restated in the presentation-level form
   (`S1866PullbackFirstMissing_iff`, `S1866CoproductFirstMissing_iff`).

5. Non-vacuity: `S1866StrongCoverOf_terminal` (the terminal cover is strong) and
   `S1866StrongCoverOf_doubled_not` (the doubled cover is not).

## Honest boundary

* No inhabitant of `S1854PullbackApexCoherent`, `S1854CoproductApexCoherent`, or of
  the first-missing predicates is produced.  No fake coherent cover, strong
  presentation, limit or axiom is used.
* The no-go does not say the geometric fibre product of two coherent covers is
  non-coherent.  It says the recorded presentation of the chosen apex is the
  load-bearing datum, so a genuine construction of the fibre product with its strong
  presentations is required.
* The natural next step is to construct the base-change presentations of the
  bicategorical fibre product of coherent covers (iso-comma stack + the strong
  squares of the two projections) and prove `S1866PullbackApexFirstMissing` for the
  chosen S1832 structure; the coproduct side likewise needs the disjoint-union /
  affine transport construction.

## Evidence

* File: `tmp/sheaf/xif/paper/S1866ApexCoherenceActual.lean`, 29796 bytes, 617 lines,
  SHA256 `A5D060F31D6FE79C2809C88F3C113FA9D6FBD9813C19A265F6D981F3C9C7A367`.
* Compile: `lake env lean -j1 -R D:\lean -o
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1866ApexCoherenceActual.olean
  tmp/sheaf/xif/paper/S1866ApexCoherenceActual.lean`, EXIT=0, zero errors/warnings;
  log `tmp/sheaf/xif/paper/S1866_compile.log`.
* Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1866ApexCoherenceActual.olean`,
  173728 bytes, SHA256
  `38E13DD7F41D691FCD20EAB522DF961ECD97D636C759D3653E83DE1E123EE164`.
* Verification: `_S1866Verify.lean` imports the olean and checks the main statements
  (both hom universes), EXIT=0; log `tmp/sheaf/xif/paper/S1866_verify.log`.
* `#print axioms` on all checked declarations: `propext`, `Classical.choice`,
  `Quot.sound` only.

Honest labels: `statement_compiles`=yes; `proof_body_checked`=yes for the proved
reductions/no-go statements; `kernel_closed`=yes (trio axioms); `target_accepted`=no
(the apex coherence statements are named, not proved).
