# PadicAbsoluteGaloisTopologicallyFinitelyGenerated: audit and minimal API

## Target
S2117:
  PadicAbsoluteGaloisTopologicallyFinitelyGenerated : Prop :=
    exists s : Finset (LocalAbsoluteGalois p),
      (Subgroup.closure (s : Set (LocalAbsoluteGalois p))).topologicalClosure = top.

## What is actual/available
- Mathlib: finite residue field of a p-adic field and Krasner's lemma (`IsKrasner`).
- S2117 actual:
  - `krasner_available`;
  - `topologicallyFinitelyGenerated_openSubgroup`;
  - `topologicallyFinitelyGenerated_of_continuous_surjective`;
  - `topologicallyFinitelyGenerated_of_padicAbsoluteGalois` (finite generation of G_Qp implies all open subgroups);
  - `padicAbsoluteGaloisTopologicallyFinitelyGenerated_of_atMost` (bounded generator form implies target);
  - `FinitelyManyExtensionsOfDegree`, `FinitelyManyExtensionsOfLocalFieldOfDegree`, `FinitelyManyOpenSubgroupsOfIndex` as necessary-but-not-sufficient Props.
- S2116 actual: the route to M2c from finite generation + Nikolov-Segal width.

## Exact first missing
There is no Demushkin/Shafarevich presentation of the absolute Galois group of a p-adic field in Mathlib or the tree. In particular there is no theorem producing a finite topological generating set for `LocalAbsoluteGalois p`. The tree explicitly records (S2117 lines 282-293, S2116 lines 91-94) that the Demushkin structure and the maximal pro-p quotient are absent.
Minimal API that would suffice:
1. `PadicAbsoluteGaloisInertiaProcyclic : Prop` — the residue extension quotient is procyclic (finite residue field / Frobenius);
2. `PadicWildInertiaProP : Prop` — wild inertia is pro-p;
3. `PadicAbsoluteGaloisDemushkinPresentation : Prop` — existence of finitely many generators `sigma, tau_1, tau_2` with the Demushkin relation, including the statement that their generated closed subgroup is top;
4. an actual theorem `padicTopFG_of_demushkin : PadicAbsoluteGaloisDemushkinPresentation -> PadicAbsoluteGaloisTopologicallyFinitelyGenerated`.
None of these is currently inhabited. A bare Prop/interface with no proof is not a construction and must not be treated as actual.

## Attempted assembly
The intended assembly is:
  finite residue field -> procyclic inertia quotient
  + wild inertia pro-p
  + Demushkin presentation -> finite closed generating set
  -> PadicAbsoluteGaloisTopologicallyFinitelyGenerated.
The first two steps are not formalized; the third (Demushkin) is the genuine missing arithmetic input. Without it, no finite generating set can be produced. The necessary finiteness-of-extensions statements alone do not imply finite generation (S2117 records the counterexample: a profinite product of C_{p_n} over distinct primes can have finitely many open subgroups of each index and still not be finitely generated).

## Status
No actual inhabitant and no refutation. No fake/interface-only data was added. Exact missing remains `PadicAbsoluteGaloisTopologicallyFinitelyGenerated` plus the Demushkin API above.
Baseline actual S2442MuQZFinalActual remains unchanged: source SHA256 D290C70F48BBA29CE068982CC345BF2A4FEC572A2F564B2AB847A489A93BDA6E; olean SHA256 6FC270E7C19947E6943EEAFDB72CF8528E41A3386CAC116DB6F205089A20CB95; axioms propext/Classical.choice/Quot.sound.