# S2454: raw permBar cycle type actual; normalization missing

Date: 2026-11-03. Serial -j1 compiles only.

## Actual

1. tmp/sheaf/xif/paper/S2453BetaTransitiveActual.lean
   SHA256 6ECAAC3DCD2CFB628B51438004D4F4ECBD3E4EC1CFC0C121635C6BA4097A4878
   olean SHA256 5DD030F8F05517A17E3B1DE916260AD464B68EB3A0BF809FAD99360FF442C312
   size 212424
   axioms trio; no sorryAx.
   - s2453Beta_fintype;
   - s2453PermBar_pow_apply;
   - s2453Fibre_transitive.

2. tmp/sheaf/xif/paper/S2454D5FinalIntegrationActual.lean
   SHA256 49977C31BEDE4C6CB1EE4F9BFE3E02884BA265424D176BD7C5C94CE41B9BE74D
   olean SHA256 955E7282AEEF1E59AEA94648041170EA31CFBC4F20882744F3CBDA9CD47C5C5F
   size 72088
   axioms trio; no sorryAx.
   - s2454PermBar_cycleType_raw:
       (permBar f p P).cycleType
       = (Finset.univ.filter (fun b : beta => 2 <= b.1.natDegree)).val.map
           (fun b => b.1.natDegree).
     via cycleType_eq_fiber_sizes with p=s2425RootFactor,
     d=b.1.natDegree, hinv=s2425RootFactor_permBar,
     hcard=s2446Fiber_card, htrans=s2453Fibre_transitive.

## Exact first missing

Normalization:

  (Finset.univ.filter (fun b : beta => 2 <= b.1.natDegree)).val.map
    (fun b => b.1.natDegree)
  = ((normalizedFactors (fbar f p)).map natDegree).filter (2 <= .)

beta is {g | g in normalizedFactors} with Fintype from Set.Finite.fintype,
not definitionally the attach of normalizedFactors.toFinset.  Need the
multiset/Finset attach normalization using normalizedFactors_nodup.

After that: S2428 identifies with factorDegrees.filter (· != 1); S2440
transfers to rootCycleType; sigma=arithFrobAt gives corrected theorem.

## Status

- D5 corrected theorem NOT accepted.
- No fake; S2427 sorryAx unused.
- Remaining: single normalization, then S2428/S2440 final application.
