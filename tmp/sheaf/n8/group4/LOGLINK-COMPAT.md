# N8 group4 stage 1: log-link / Kummer-log-volume compatibility

- package: N8 group4
- node: LOGLINK-COMPAT (stage 1)
- owner file: tmp/sheaf/n8/group4/LOGLINK-COMPAT.md
- production changes: none. No change to MultiradialKernel.Profile or any source file.

## Source anchors (read-only)

1. IUT III, pp. 20-21, around text line 1150 (paper pages 20-21):
   after the (Ind3) upper-semi description, the paper states:
   "Finally, as one varies m, these Kummer isomorphisms of tensor packets of
   log-shells are [precisely!] compatible, relative to the log-links of the
   n-th column ..., with the respective log-volumes [cf. Proposition 3.9,
   (iv)]."
   The text immediately before this distinguishes:
   - (Ind3) upper-semi-compatibility: natural inclusions at nonarchimedean
     places and natural surjections at archimedean places;
   - precise compatibility with the respective log-volumes.
   These are two different clauses.

2. IUT III, Proposition 3.9, (iv) (text line 6838 onward), especially (a), (b):
   log-volumes on the various IQ((−)) attached to the local/global
   LGP-/lgp-monoids/Frobenioids in the F-prime-strips, indexed by (n,m), and
   compatibility of the volumes indexed by (n,m) with those indexed by
   (n,m-1), relative to the log-link.

3. IUT III, pp. 227-229 (paper pages 186-188 in the text extraction):
   the final upper-bound discussion for C_Theta / Corollary 3.12. The
   discussion explains that the inequality is obtained from dismantling and
   reassembling value-group/unit-group portions via log-volumes; it does not
   assert a separate precise Kummer/log-volume equality for an arbitrary
   Kummer arrow.

## Current Lean objects and exact quantifiers

### A. Abstract multiradial profile

File: LeanFormal/IUT/IUTIII/Theorem311/MultiradialProfileKernel.lean

- structure MultiradialKernel.Core (Label Choice) [AddGroup Label]:
  base, level, ind1, ind2, ind3 and their laws.
- structure MultiradialKernel.Profile (core : Core Label Choice):
  logVolume : Choice -> Real
  possibleImage : Choice -> Set Real
  ind1_invariant, ind2_invariant
  ind3_upper : forall n c, logVolume c <= logVolume (core.ind3 n c)
  possibleImage_nonempty
  possibleImage_ind1, possibleImage_ind2
  possibleImage_ind3 :
    forall n c z, z in possibleImage c ->
      exists w, w in possibleImage (core.ind3 n c) and z <= w.

These fields are data supplied when a concrete Profile instance is built.
They are not derived from a Kummer isomorphism. The field ind3_upper is a
one-sided upper-semi inequality; possibleImage_ind3 is its image-level form.

Derived consumers:
- Profile.logVolume_applyRoute_le:
  forall route c, logVolume c <= logVolume (applyRoute core route c).
- MultiradialKernel.Output.source_logVolume_le_target:
  logVolume source <= logVolume target.
- MultiradialKernel.Output.target_image_upper:
  forall z in possibleImage source, exists w in possibleImage target with z <= w.

This is the "final upper bound" shape. It contains no Kummer isomorphism and
no equality of log-volumes across a Kummer arrow.

### B. Kummer interface

Files:
- LeanFormal/IUT/IUTIII/Theorem311/SourceKummerEvaluationArrows.lean
- LeanFormal/IUT/IUTII/Kummer/TimesMuIsm.lean

- Theorem311Source.SourceTimesMuKummerLayer G upper lower:
  sourceAction : forall v, G ->* MulAut ((upper.Mon v)ˣ)
  targetAction : forall v, G ->* MulAut ((lower.Mon v)ˣ)
  kummer : forall v, TimesMuKummer.Isomorphism (sourceAction v) (targetAction v).
- Theorem311Source.SourceKummerArrow G upper lower:
  stripIso : FPrimeStripEquiv upper lower
  layer : SourceTimesMuKummerLayer G upper lower.
- TimesMuKummer.Isomorphism source target:
  equiv : TimesMuQuotient U ≃* TimesMuQuotient W
  equivariant : forall g x, equiv (action source g x) = action target g (equiv x)
  invariantImage : the invariant-image law for every open subgroup.

There is no log-volume field, no source/target volume function, and no map
from the Kummer carriers to the abstract Choice/logVolume carriers. Therefore
the paper's precise Kummer/log-volume compatibility is not even stated at the
current interfaces.

## Gap decomposition

### Child obligation A: final upper bound (already represented, conditional)

Target: the one-sided inequality used by the final estimate.

Exact existing declaration:
  MultiradialKernel.Profile.ind3_upper :
    forall (n : Nat) (c : Choice),
      profile.logVolume c <= profile.logVolume (core.ind3 n c)

and its route/output consumers:
  MultiradialKernel.Profile.logVolume_applyRoute_le
  MultiradialKernel.Output.source_logVolume_le_target
  MultiradialKernel.Output.target_image_upper

Consumer: the Corollary 3.12 / final upper-bound side of the multiradial
assembly.

Status: this is a Profile field, not a theorem derived from Kummer theory.
A concrete Profile instance may supply it (e.g. the concrete finite model), but
the abstract kernel alone does not construct a Profile or prove its fields.
No Kummer arrow is consumed. This child does not imply the precise equality
clause below.

### Child obligation B: Kummer isomorphisms precisely compatible with log-volumes

Target: for a Kummer arrow/layer, the actual source and target log-volumes on
the tensor packet of log-shells agree exactly under the Kummer isomorphism,
not merely up to the one-sided (Ind3) inequality.

Missing pieces:
1. Actual source/target log-volume functions on the carriers of the Kummer
   layer (or on the corresponding log-shell tensor packets), constructed from
   Proposition 3.9, (i)-(ii)/(iv).
2. Exact compatibility square:
   sourceVolume_v x = targetVolume_v ((L.kummer v).equiv x)
   for every place v and every source carrier element x.
3. A bridge from these actual volumes to the abstract
   MultiradialKernel.Profile.logVolume values (choiceOf : FPrimeStrip V ->
   Choice or an equivalent log-shell packet identification). Without this
   bridge one cannot state a comparison with the final upper bound.

Current status: all three pieces are absent. In particular:
- SourceTimesMuKummerLayer has no volume function;
- SourceKummerArrow has no volume compatibility field;
- MultiradialKernel.Profile has no Kummer parameter or Kummer compatibility
  field.
The precise clause is therefore an OPEN child obligation, not a consequence of
ind3_upper.

## Minimal stage 2 type (reduced carrier form)

The smallest faithful statement at the existing Kummer carriers is the exact
equality of two supplied real-valued volume functions along the Kummer
equivalence. It does not introduce a Profile, a root, or a quotient action; it
only states the precise compatibility shape.

~~~lean
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

namespace LeanFormal.IUT.Theorem311Source

universe uG uv

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uv} {upper lower : FPrimeStrip V}

/-- Precise Kummer/log-volume compatibility on the reduced unit-quotient
carriers: the source volume of every carrier element equals the target volume
of its image under the Kummer equivalence.  The volume functions are explicit
children to be constructed from Proposition 3.9; they are not chosen here. -/
def KummerLogVolumeCompatibility
    (L : SourceTimesMuKummerLayer G upper lower)
    (sourceVolume : ∀ v : V,
      TimesMuQuotient ((upper.Mon v)ˣ) → Real)
    (targetVolume : ∀ v : V,
      TimesMuQuotient ((lower.Mon v)ˣ) → Real) : Prop :=
  ∀ (v : V) (x : TimesMuQuotient ((upper.Mon v)ˣ)),
    sourceVolume v x = targetVolume v ((L.kummer v).equiv x)

end LeanFormal.IUT.Theorem311Source
~~~

This is a statement type / specification, not a proof. It deliberately does
not assert that sourceVolume/targetVolume exist or are the paper's log-volumes.
The next child after it is the actual construction of those functions from
Proposition 3.9 and the comparison to Profile.logVolume.

## Consumer and dependency summary

- Direct consumer of Child A: MultiradialKernel.Output and the final
  Corollary 3.12 upper-bound side.
- Direct consumer of Child B: a not-yet-existing log-Kummer/Theta-x-mu
  consumer that combines SourceKummerArrow with Profile.logVolume; currently no
  declaration imports both interfaces into one theorem.
- Dependencies for Child B: Proposition 3.9 local/global/procession
  log-volumes, the source/target strip data, and the Kummer layer's
  TimesMuKummer.Isomorphism. None of these are currently connected in Lean.
- Upstream source: IUT III pp.20-21 line 1150; Proposition 3.9(iv);
  pp.227-229 upper-bound discussion.

## Stage status

- stage 1: this document.
- stage 2: KummerLogVolumeCompatibility type above, pending a file owner and
  the actual volume-function construction.
- stage 3: not started.
- no production file modified; Profile untouched.

## Stage 2 type statement check

- Probe file: tmp/sheaf/n8/group4/LogVolumeCompatTypeProbe.lean
- lake env lean -j1 probe -> EXIT 0.
- statement_compiles=true for KummerLogVolumeCompatibility.
- proof_body_checked=false: no inhabitant of the compatibility predicate is
  constructed; this is a specification, not a theorem about actual
  log-volumes.
