# S2455: D5 normalization plan (no new compile)

Date: 2026-11-03.

## Established clean

- S2453BetaTransitiveActual: beta Fintype, permBar power, fibre transitivity.
  src 6ECAAC3DCD2CFB628B51438004D4F4ECBD3E4EC1CFC0C121635C6BA4097A4878
  olean 5DD030F8F05517A17E3B1DE916260AD464B68EB3A0BF809FAD99360FF442C312.
- S2454D5FinalIntegrationActual: s2454PermBar_cycleType_raw.
  src 49977C31BEDE4C6CB1EE4F9BFE3E02884BA265424D176BD7C5C94CE41B9BE74D
  olean 955E7282AEEF1E59AEA94648041170EA31CFBC4F20882744F3CBDA9CD47C5C5F.

## Exact minimal normalization goal

  (Finset.univ.filter (fun b : beta => 2 <= b.1.natDegree)).val.map
    (fun b => b.1.natDegree)
  = ((normalizedFactors (fbar f p)).map natDegree).filter (2 <= .)

## Proposed fix: change beta's Fintype, not the goal

Use s := (normalizedFactors (fbar f p)).toFinset and

  beta := {g : ((O_K)⧸p)[X] // g ∈ s}
  Fintype beta := Fintype.ofFinset s.attach (by intro x; simp [s])

Then Finset.univ = s.attach (definitional for Fintype.ofFinset), and

  (Finset.univ.filter p).val.map Subtype.val
    = (s.filter p).val                     -- List.attach_map_subtype_val
    = ((normalizedFactors (fbar f p)).filter p).val -- if s.val = M

The last equality uses

  Multiset.toFinset_val : s.val = M.dedup
  Multiset.dedup_eq_self.mpr hnodup : M.dedup = M

and hnodup is available from separability:

  have hnodup : (normalizedFactors (fbar f p)).Nodup :=
    (squarefree_iff_nodup_normalizedFactors (s2397Fbar_ne_zero f p P hmonic)).mp
      hsep.squarefree

(`Polynomial.Separable.squarefree` is in Mathlib.)

After this, the map root -> beta must be defined using the membership
translation `Multiset.mem_toFinset`; hcard/htrans are transferred from
s2446Fiber_card / s2453Fibre_transitive.

## Then final two steps

1. S2428:
   (permBar p P).cycleType
     = (factorDegrees (fbar f p)).filter (· != 1).
2. S2440:
   rootCycleType K L f hsplit sigma
     = (factorDegrees (fbar f p)).filter (· != 1).
3. sigma := arithFrobAt; corrected theorem / orbitSizeMultiset.

## Status

- D5 corrected theorem NOT accepted.
- The single remaining blocker is the Fintype.ofFinset/attach normalization
  above; no new compile was run for this report.
- S2427 sorryAx unused; no fake.
