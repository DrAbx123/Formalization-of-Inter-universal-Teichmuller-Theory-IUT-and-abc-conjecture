# Paper q-pilot q versus the concrete Gaussian q = 1/5

Date: 2026-10-28.  Status: source-check only; no Lake/Lean run.

## 1. What the paper calls the q-pilot object

IUT III, Definition 3.8, (i) (source-extract/iut3.txt lines 6731-6768; printed
pp. 112-113) defines a q-pilot object as the object of the global realified
Frobenioid `C^⊩_Δ` determined by any collection, indexed by
`v ∈ V_bad`, of generators up to torsion of the split Frobenioid `F^⊣_{Δ,v}`
— concretely, by the `q_v`, for `v ∈ V_bad`.

So the paper q-pilot input is a **collection `(q_v)_{v ∈ V_bad}`**, not a single
local q and not a normalized scalar.  The associated `-|log(q)|` is not
defined as `-log(q_v)` for one v; IUT III, Corollary 3.12 (iut3.txt lines
10499-10535; printed pp. 173-174) defines

> `-|log(q)|` as the procession-normalized mono-analytic log-volume of the
> image of a q-pilot object, relative to the relevant Kummer isomorphisms, in
> the multiradial representation of Theorem 3.11, (i), without the
> indeterminacies (Ind1), (Ind2), (Ind3).

Thus `paperQPilotLogMagnitude` must be the magnitude of the global q-pilot
log-volume (a procession average/sum over the q-pilot object), not the local
log of one q_v and not `-log(1/5)`.

## 2. What the concrete Gaussian q = 1/5 is

IUT II (iut2.txt line 99) fixes notation: `q_v` denotes the q-parameter at
`v ∈ V_bad` of the elliptic curve.  The project's source theater carries a
single local Gaussian finite theta packet

`FiniteThetaPacket.ofQ gaussianFiveThetaQ gaussianFiveThetaQ_pos`

with `gaussianFiveThetaQ = 1/5` (Example36SourceTheaterCarrier lines 163-186).
This is the **local q-parameter at the concrete place** used to build the
Gaussian theta packet.  It is not the collection `(q_v)` of Definition 3.8,
and the paper does not identify the global q-pilot log-volume with
`log 5`.

## 3. Actual computation of gaussExponentSum/card

For signed labels `j ∈ F_l^⋆`, `gaussExponent j = j^2`
(Foundations/Theta/GaussianKernel.lean lines 23-27).  The signed labels are
`-l⋆, ..., l⋆`, hence

`gaussExponentSum = 2 * sum_{j=1}^{l⋆} j^2
                 = l⋆(l⋆+1)(2l⋆+1)/3`,
`card(SignedLabel l.value) = 2l⋆ + 1`.

Therefore

`gaussExponentSum / card = l⋆(l⋆+1)/3`.

For `l = 5`, `l⋆ = 2`, so the quotient is `2*3/3 = 2 > 1`.
For every prime `l ≥ 5`, `l⋆ ≥ 2`, hence `l⋆(l⋆+1)/3 ≥ 2 > 1`.

Consequently, **if** the q-pilot magnitude were the local `log 5 = -log(1/5)`,
the actual source-theater signed average

`average = log 5 * (gaussExponentSum/card) = log 5 * l⋆(l⋆+1)/3`

would be strictly greater than `log 5`.  The proposed
`ConcreteQMagnitudeBound` would then be false, not merely unproved.

## 4. Conclusion for the concrete comparison

`ConcreteQMagnitudeBound` compares the local signed average of the source
theater with `paperQPilotLogMagnitude` of the same local C3.  The source
paper does not make this comparison:

* the q-pilot object is the global collection `(q_v)_{v ∈ V_bad}`;
* its `-|log(q)|` is a procession-normalized multiradial log-volume;
* `q = 1/5` is one local Gaussian q-parameter, not the global q-pilot scalar.

Thus the concrete bound is **not paper-faithful**.  If one nevertheless
identifies the q-pilot magnitude with the local `log 5`, the bound is false
already at `l = 5` because the coefficient `l⋆(l⋆+1)/3 = 2 > 1`.

The exact missing object for a paper-faithful comparison is the global
q-pilot log-volume object: the collection of q-parameters over `V_bad`, its
multiradial/procession-normalized log-volume, and its identification with the
global `-|log(q)|`.  No such global object is constructed by the local
Gaussian q = 1/5 data.

## 5. References

- IUT III, Definition 3.8, (i): iut3.txt lines 6731-6768 (pp. 112-113).
- IUT III, Corollary 3.12: iut3.txt lines 10499-10535 (pp. 173-174).
- IUT II q-parameter notation: iut2.txt line 99.
- Project Gaussian exponent: `Foundations/Theta/GaussianKernel.lean` lines 23-27.
- Project source Gaussian q = 1/5: `Example36SourceTheaterCarrier.lean` lines
  163-186.

No inequality is asserted as a theorem in this note; the quotient computation
is arithmetic and the bound falsity statement is conditional on the local
`log 5` identification, which is not paper-faithful.