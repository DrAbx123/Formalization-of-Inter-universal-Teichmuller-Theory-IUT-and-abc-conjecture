# Simplification audit for the xi-f target

Date: 2026-10-29.  Status: audit only; no new xi-f claim.

The user's rule: a 99% simplified object is not acceptable; it will fail at
the last step, and the failure probability may be even higher than 99%.  This
file lists every known simplification currently on or near the xi-f path and
states the actual paper object that must replace it.

Strict admissibility criterion: an object counts only if it is the paper
construction definition-by-definition.  A model object, a divisor-sum stand-in
for a categorical product, a value realization, a Classical.choice q family, an
ENNReal truncation, a hand-normalized scalar, or a '99% correct' carrier is not
admissible as the final object.  Such objects may be used only as exact
gap-locators, never as evidence for xi-f.

## 1. Source / Frobenioid architecture

Paper (IUT III, Definition 3.8(i)):
- q-pilot is an object of C^⊩_Δ determined by the q_v collection;
- Theta-pilot is an object of C^⊩_LGP / C^⊩_lgp determined by LGP-monoid
  theta values;
- they are the domain/codomain of the Theta-link, not one carrier.

Current simplifications:
1. GlobalRealifiedFrobenioidActual is only a q-side C^⊩_mod carrier.  The full
   presentation and the actual q_v divisor insertion are missing.
2. GlobalFrobenioidPresentationActual models C^⊩_mod, not C^⊩_LGP/C^⊩_lgp.
3. No actual LGP-monoid presentation/splitting data is constructed.
4. No actual 2l-th root q_v with its mu_{2l} ambiguity is constructed; current
   thetaValueFamily uses qVFamily directly, so it is the q parameter, not the
   paper's 2l-th root theta input.
5. The Theta-pilot product over j is realized only as a divisor-monoid finite
   sum + model object class; no categorical product object in a product
   Frobenioid category exists in the tree.

These are object-level gaps, not notation.  They must be constructed, not
replaced by a value-layer/function-space surrogate.

## 2. q-pilot scalar

Current:
- NativeGlobalQPilotNormalizedLogVolumeActual uses
  baseQ := badPlaceQCandidate, a Classical.choice of a FinitePlaceQCandidate
  carrying only v(q)<1.  It is not asserted to equal the clause-B q_v family.
- qVFamily is the actual clause-B comparison parameter (QPilotZeroLocusDivisorActual),
  but the native q-pilot scalar does not use it.
- SourceVolumeIndex / procession cardinality factors are not yet uniformly
  propagated between q-pilot and Theta-pilot scalars.

Required:
- one actual q_v family (clause-B qVFamily or its actual 2l-th root as the paper
  requires);
- the same family on both sides;
- the same place weights/procession normalization on both sides.

## 3. Theta-pilot possible images

Current invalid surrogates:
- PaperThetaPilotCarrierActual.paperThetaPilotPointAt q j is
  fun _ => log(thetaValue q j), a constant/diagonal tuple;
- paperPossibleImageSet is the range of these constant tuples;
- PaperLabelHullHaarComputed and PaperLabelHullCopiesSame are invalid and must
  not be used;
- sourceThetaPilotPoint / SignedHullSupActual are value-layer realizations.

Paper:
- possible images are tensor-packet regions n,circ U_{j,vQ} inside
  I_Q(S^±_{j+1}; D^⊣_{vQ}), not constant functions on F_l^×;
- the hull is their actual holomorphic hull, subject to Kummer/Ind1-3.

Current actual partial:
- ThetaPilotGlobalObjectActual constructs an actual SourceModelFrobenioid.Object
  factor family with divisor j^2 * qVEffectiveMultiplicity;
- ThetaPilotGlobalProductActual sums these divisors and packages the model object.

But these are still a model-object/divisor simplification of the paper's
tensor-packet region and hull.  The tensor packet, log-shell, Kummer action and
Ind1-3 hull are not yet constructed.

## 4. Theta hull log-volume

Current invalid/insufficient:
- sourcePointVolume = ENNReal.ofReal(sourceLocalLogDegree) truncates negative
  theta logs to zero (SourceHullVolumeSignCorrectedActual proves this);
- positiveHullLogVolume = sup of -sourceLocalLogDegree is a positive magnitude
  candidate, not the paper's unit-normalized hull log-volume;
- paperLabelHullLogVolume uses generic holomorphicHull of a single value point;
- PaperThetaHullEqQPilotActual is marked INVALID SURROGATE;
- global Theta log-volume candidates average value-layer logs or sum component
  logs, not the actual tensor-packet hull log-volume.

Required:
- actual tensor-packet region/hull;
- actual paper mu_log normalization (unit/integral region zero);
- actual hull log-volume, then procession average;
- no ENNReal.ofReal of a signed negative log as a substitute.

## 5. Theta-link / Kummer / Indeterminacies

Current:
- Kummer label action only unit-level and some algebraic identities;
- full Kummer-to-label compatibility and multiradial action are exact
  obstructions;
- Ind1/Ind2/Ind3 are only partial carrier/action models;
- Theta-link identification remains a field/Prop, not a constructed theorem.

Required:
- actual Kummer isomorphisms/multiradial action;
- Ind1/Ind2/Ind3 actual actions;
- actual Theta-link identification;
- actual comparison of the two global objects.

## 6. What is not simplified (safe actual material)

- clause-B qVFamily and its q/valuation/order data;
- actual model Frobenioid presentation of C^⊩_mod (globalFrobenioidPresentationActual);
- actual divisor monoid finite sums and model object classes;
- actual finite places/completions/local rings used by the C3/one-column construction;
- surface F_l^× = (ZMod l.value)^× and SignedLabel equivalences;
- sign-correct scalar reductions:
  PaperXiFGlobalDirectActual, GlobalPositiveHullPaperXiFActual,
  PositiveHullVsQPilotCorrectedActual, GlobalHullPaperXiFActual
  are algebraically correct but conditional on an unproved actual scalar
  comparison; they are not the paper objects by themselves.

## 7. Rule going forward

Do not put a simplified carrier, constant-tuple image, ENNReal zero truncation,
weighted value-layer average, or divisor-sum model object into the final xi-f
path.  Each must be replaced by the actual paper object or recorded as an exact
object-level gap.  No final theorem is claimed from the current conditional
scaffolding.

No sorry, axiom, True, PUnit, or toy object is introduced by this audit.
