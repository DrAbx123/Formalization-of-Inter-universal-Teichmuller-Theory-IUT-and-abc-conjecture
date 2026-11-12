# S1301: audit of new products — actual original vs simplified surrogate

Scope: audit only; no Lean files changed.  Paper object takes priority: simplified
models may be used as internal donors/probes but NOT as final paper objects or
final judgements.

Status key: ORIGINAL = actual paper-side object; ACTUAL-COMPONENT = actual
mathematical component reusable in a paper construction; SIMPLIFIED = surrogate
not the paper object; MISSING = the original object is absent.

| File / object | Status | Can be used for final judgement? | Missing original object |
|---|---|---|---|
| S1195 upperEnv (graph common group from fLinkAt + S1188 non-refl layer) | SIMPLIFIED | No | actual paper evaluation/Kummer operation on the source prime-strips; fLinkAt is a generic source link, not the evaluation isomorphism |
| S1234 finiteKernelRun | SIMPLIFIED | No | actual paper SourceRun on SourceDefinition31Data/D5-D11 operations; ProcessionChoice finite model is not the paper source run |
| S1262 HDD local lattice (rank 1, span of unit section) | SIMPLIFIED | No | actual HDD hull+det module with genuine local lattices/ranks from the source output |
| S1286 localizeSection (constant unit section) | SIMPLIFIED | No | actual localizeSection representing the HDD lattice element, not a constant unit section |
| S1295 localizeSection span / LatticeSectionRepresentation | SIMPLIFIED/EXACT | No | localRing-module structure on bundle.total and an actual section representation |
| S1287 ActualHDDReadoutFields assembly | SIMPLIFIED assembly | No | same HDD lattice/localizeSection paper objects; it only packs the rank-one surrogate |
| S1270 nontrivial capsule contract (IQSpan shell) | ACTUAL-COMPONENT/SIMPLIFIED | No | actual integral/Z_p log-shell module; IQSpan/Q-vector loses the integral structure required by the paper |
| S1280 Definition 3.1 prefix (D3/D4) | ACTUAL-COMPONENT/PARTIAL | No | D5-D11: torsion clause, q-parameter identification, remaining Definition 3.1 cards |
| S1282 sourceLevel = toNat | SIMPLIFIED/IMPOSSIBLE-FOR-CARRIER | No | paper Core level with level(ind3 n c)=level c+n; S1282 proves no total level with actual ind3 can satisfy Carrier.ind3_level_eq |
| S1283 algebraic-closure roots as completion roots | MISSING (no S1283 file) | No | actual C3 completion roots/action; algebraic-closure roots are not completion roots |
| S1219 concrete tensor landing (one-place finite tensor) | SIMPLIFIED | No | actual paper tensor packet/log-shell integral structure; ConcreteBlock is a concrete finite model |
| S1221 stripOfChoice on I.family.index | ACTUAL-COMPONENT | Not alone | evaluation operation/upperEnv provenance; stripOfChoice is actual source index→FPrimeStrip |
| S1225/S1226/S1227/S1231 Core on family index (level:=0) | SIMPLIFIED | No | paper Core/level/procession; level 0 and translation powers are a surrogate |
| S1232 sourceLogVolume shift laws | ACTUAL-COMPONENT | Not alone | tied to simplified Core; the log-volume equality itself is actual for the family |
| S1233 thetaPossibleImage | ACTUAL-COMPONENT | Not alone | paper multiradial allowed image family/HDD hull; theta scale image is only a component |
| S1258 SourceProfile attempt | NOT COMPILED/BROKEN | No | actual Profile on paper Core; file does not compile in current tree |
| S1190 eval fixed-subgroup lemma | ACTUAL-COMPONENT | No (support only) | paper group/action object; lemma is graph-group fixed-subgroup algebra, useful as support |
| S1188 non-refl Kummer layer from fLinkAt | ACTUAL-COMPONENT/SIMPLIFIED | No | paper Kummer/evaluation layer with actual integral/Z_p and source operation; current layer uses generic fLinkAt |
| S1168/S1164 candidate square | SIMPLIFIED | No | actual evaluation square; candidate fLinkAt square is not the paper operation square |
| S1170 routeTrace | ACTUAL-COMPONENT | No (support only) | paper source run operation trace; endpoint theorem is actual for any Carrier |

## Paper objects explicitly absent

- SourceDefinition31Data D5-D11 (torsion, q-parameter, remaining source cards).
- SourceProcessionCapsuleContract with actual integral log-shell/polyIso (S1270
  uses IQSpan/Q-vector and does not retain the integral/Z_p structure).
- KappaOrbitUnitsActionPairDatum with nontrivial source kappa.
- C3 completion roots/action (no S1283; algebraic-closure roots are not completion roots).
- Genuine HDD hull+det module; S1262/S1286/S1287/S1295 are rank-one/unit-section surrogates.
- Theta line bundle/function/divisor actual source object.

## Consequence for the main line

The following may NOT be used to compute a final Q<=H, lambda<=S, or Cor312
judgement:

finiteKernelRun, Choice=index×Nat/translation Core with level 0, rank-one HDD
lattice, constant-unit localizeSection, IQSpan/Q-vector tensor capsule,
algebraic-closure C3 roots, self/generic-link non-refl Kummer layer, concrete
one-place tensor landing.

Actual mathematical donors that remain reusable:
- S1221 stripOfChoice/linkOfChoice (source index to actual F-prime-strip).
- S1232 sourceLogVolume shift laws.
- S1233 thetaPossibleImage and its family-invariance.
- S1190 graph-group fixed-subgroup lemma (support algebra).
- S1170 routeTrace endpoint theorem.

## Next original-object work (in priority order)

1. SourceDefinition31Data D5-D11 and the actual SourceProcessionCapsuleContract
   integral log-shell/polyIso.
2. KappaOrbitUnitsActionPairDatum with nontrivial source kappa; C3 completion
   roots/action.
3. Actual HDD hull+det module, theta line bundle/function/divisor.
4. Only then rebuild SourceRun/evaluation/upperEnv on those objects, not on the
   finite/surrogate carriers above.

Report only; no Lean code changed.