# S2039: the actual constant monoid Psi_cns and the exact first missing chain

Date: 2026-11-02.  File: `tmp/sheaf/xif/paper/S2039ActualPsiCns.lean`.
Consumer: `tmp/sheaf/xif/paper/_S2039Consumer.lean`.
Upstream: S2000/S2006 (actual cohomological limit and Kummer map), S2011
(Cor 1.10(b) interface, G_v-action), S2017 (Verlagerung, muQZ/muHatZ),
S2024/S2027 (local reciprocity, local Artin map).
Source: [AbsTopIII] Corollary 1.10, (a), (b), (d), Remark 1.11.5, (i);
IUT II, Proposition 4.1, (ii).

## Outcome

**EXIT = 0.**  The **target half of (M3) is now constructed** (Z-hat was
repeatedly recorded as absent from the tree and is not), the **source-faithful
Kummer map of the local field's integral monoid** is constructed and proved
injective, the **actual Psi_cns** is defined as a genuine submonoid of S2000's
actual cohomological limit, and the identification Psi_cns = O^tri_{F_v} is
**reduced exactly** to the two source assertions (the valuation property and
the exhaustion of Remark 1.11.5, (i) / Cor 1.10, (d)), with both converse
directions proved.  No sorry, axiom, admit, True/PUnit slot, empty structure,
arbitrary inhabitant, or assumption-only Nonempty gate is used; all checked
declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Constructed / proved

1. **Z-hat.** `Zhat` is the inverse limit of the reductions
   `ZMod n -> ZMod m` (`m | n`) over the positive integers, as a
   `Subring` of the product; `zhatMod`, `zhat_compat`, the ring homomorphism
   `zhatIntHom : Int →+* Zhat` (`zhatInt`, `zhatNat`) and its injectivity
   `zhatIntHom_injective`; the nonnegative part `zhatNatSubmonoid` /
   `zhatNonneg` with its monoid laws.  This is the codomain of the (M4)
   normalization and the target of the (M3) isomorphism.

2. **O^tri_{F_v} and its Kummer map.** `FvBase` is the valuation ring of the
   local field F_v = Q_p, `OtriFv = (FvBase)⁰` its nonzero integral monoid;
   `otriFvToOtri` embeds it in S2000's O^tri_{Qbar_p} (`otriFvToOtri_mul`,
   `otriFvToOtri_injective`), and `PsiCnsBaseKummer` is the resulting Kummer
   map into the actual limit, proved injective (`PsiCnsBaseKummer_injective`,
   using S2006) with `PsiCnsBaseImage p ≃* OtriFv p`
   (`PsiCnsBaseImage_equiv`).

3. **The actual Psi_cns.**  `PsiCnsNormalization` is the (M4) datum
   (a surjection `PsiCnsCohomology p →* Multiplicative Zhat`); `PsiCns N` is
   the inverse image of `zhatNonneg`, exactly as in IUT II, Proposition 4.1,
   (ii).  It is a submonoid (`one_mem_PsiCns`, `mul_mem_PsiCns`), stable
   under S2011's actual `germAction` whenever the normalization is
   G_v-invariant (`PsiCns_stable_of_invariant`), and contains the unit Kummer
   classes whenever the normalization is trivial on them
   (`PsiCnsUnitKummer_mem`).

4. **The reduction.**  `NormalizationIsValuation N` and
   `PsiCnsExhaustion N` are the two source assertions; `kummerEquals_iff`
   proves

     KummerEqualsPsiCns N  <->  NormalizationIsValuation N and PsiCnsExhaustion N,

   `baseImageToPsiCns_bijective_iff_exhaustion` proves that the canonical
   inclusion is an isomorphism exactly under the exhaustion, and
   `PsiCns_equiv_otriFv` concludes `Nonempty (PsiCns N ≃* OtriFv p)`.

5. **The cyclotomic comparison.**  `cyclotomeComparison_iff` characterizes
   S2017's `muHatComparison p` exactly as
   `Nonempty (muHatZ p ≃* PsiCnsCyclotome p)`, i.e. as the identification of
   the group-theoretic cyclotome with the coefficient module actually used by
   the Kummer map.

## Model correction: O^tri_{F_v} is not O^tri_{Qbar_p}

S2000's `PsiCnsKummer` is the Kummer map of `Otri p = O^tri_{Qbar_p}`, and
S2006 correctly identifies its image with `Otri p`.  The source's (d), and
the identification Psi_cns = O^tri, are about the **local field** F_v.  The two
monoids differ: the integral closure contains a square root of p (integral),
which is not in Q_p.  Hence identifying Psi_cns with `Otri p` would be wrong,
and this file uses the source-faithful `OtriFv`.  The S2000 item (M6) is thus
sharpened from a caveat to a correction of the target object.

## Exact first missing chain, in dependency order

(M1) transfer/colimit: **done** (S2017).
(M2) local reciprocity on torsion / local Artin map: **missing**; S2024/S2027
     isolate it.  In this file it is consumed only through
     `CyclotomeComparison = muHatComparison p` (cyclotomic rigidity).  A
     comparison of the two cohomological limits (group-theoretic vs actual
     coefficients) additionally needs the G_v-action on the group-theoretic
     cyclotome, which does not exist (S2017 (M5)).
(M3) H^2(G_v, mu_hat^Z) = Z-hat: **Z-hat constructed here**; Mathlib v4.32.2
     has `continuousCohomology` (`TopRep`), so the group is constructible;
     the computation via `Br(k_v) = Q/Z` is missing.  No declaration is
     fabricated.
(M4) normalized surjection H^1 →> Z-hat: **missing**; taken here as the
     hypothesis structure `PsiCnsNormalization`, with exactly its used
     properties isolated.
(d)  Kummer image = inverse image of Z: isolated as
     `NormalizationIsValuation` + `PsiCnsExhaustion`, proven equivalent to
     the identification.

## Evidence

* source: `tmp/sheaf/xif/paper/S2039ActualPsiCns.lean`, 710 lines,
  31,482 bytes, SHA256
  `34A38CD7F40EF6B71591F0F6A988F4E6E19B89C163248CEBAB409D19CEEBDCF2`.
* compile: EXIT = 0, 0 errors, 0 warnings:
  `lake env lean -R D:\lean -s 65536 -M 8192 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2039ActualPsiCns.olean tmp/sheaf/xif/paper/S2039ActualPsiCns.lean`
* olean: 591,176 bytes, SHA256
  `C01AABF95E21D42FD26D4FC761834524D82C3801CAE088398C082E7CD03A820F`.
* axiom probes (`#print axioms` in the file, 18 declarations): only
  `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, no custom
  axiom.
* consumer: `tmp/sheaf/xif/paper/_S2039Consumer.lean`, EXIT = 0, olean
  4,024 bytes, SHA256
  `99876D03C14EF135A103651D9169F145C1D3432B7BC831CAF10010F01F35973D`;
  source SHA256
  `54FA3C94A17A3FC59C924F24785D738A76592C64EBDD71EF65E1F6FC460DCCF5`.
* logs: `tmp/sheaf/xif/paper/S2039Compile.log`,
  `tmp/sheaf/xif/paper/_S2039Consumer.log`.

## Not run

Full Project build, target comparator, independent review, and the actual
construction of the normalization map.

## Next executable step

Construct (M4) in the two-step form (M3) then cup product: package
`PsiCnsCoefficientAction` as a `TopRep ℤ (LocalAbsoluteGalois p)` (all the
required instances on `Additive (PsiCnsCyclotome p)` were checked to
elaborate: AddCommGroup, the induced topology, IsTopologicalAddGroup,
Module ℤ, ContinuousSMul ℤ; only the coercion packaging of the continuous
linear automorphisms remains) and use Mathlib's `continuousCohomology 2` to
state `H2Normalization`; the normalization map is then the cup product with
the fundamental class followed by the valuation.  The genuinely missing
mathematical input is local CFT (`Br(k_v) = Q/Z` and
`H^1(G_v, mu_n) = k^×/k^×^n`); note the S2048 ledger entry reporting an
external `LocalClassFieldTheory` repo with `PadicField.artin` and
`PadicField.artin_transfer`, relevant to (M2a)/(M2b) but not a current
dependency.

## Parallel artifact

`tmp/sheaf/xif/paper/S2039ActualPsiCnsInterface.lean` (written by another
session at 00:28, before this package) records M2a as the exact first missing
datum and is not touched here; it does not conflict with this file.