# ROOT-SYSTEM-INVENTORY — NatRootSystem / CyclotomicTower / SourcePilotRegionCore

Status: READ-ONLY inventory, 2026-11-12. No files outside this doc/coord were modified.
The question is constructibility of the C3 donor root/Kummer fields, not a Lean error.

## 1. NatRootSystem

Definition: LeanFormal/IUT/IUTII/Kummer/NatRootSystem.lean:17
  structure NatRootSystem {M} [CommMonoid M] (value : Mˣ) where
    root : Nat → Mˣ
    root_one : root 1 = value
    compat : forall n k, k != 0 → root (n*k)^k = root n

Constructors / instances:
- NatRootSystem.pow (NatRootSystem.lean:31): from r : NatRootSystem value gives
  NatRootSystem (value^e). Green (olean 211056 B).
- AlgebraicClosureRootSystem.rootSystemOfAlgClosed (NatRootSystem.lean:76):
  for K field, IsAlgClosed K, value : Kˣ, constructs NatRootSystem value using
  factorial chain roots. Green.
- C3Roots.algClosedRootSystem (tmp/sheaf/n8/closure/C3Roots.lean:33):
  for u : Kˣ, NatRootSystem (unitToAlgClosed u); green (olean 53392 B).
- C3Roots.qCandidateRootSystem (:46): for a finite-place q candidate,
  NatRootSystem (unitToAlgClosed q). Green.
- No constructor for a generic unit in an arbitrary completion was found.
  Completion-root existence is exactly the first-field obstruction in S1391:
  completionFirstFieldObstruction (I) place :=
    Nonempty (NatRootSystem (concreteQUnit I place));
  theorem completionFirstFieldObstruction_iff (:473) is Iff.rfl.
- BaseCompletionRootsActual/Adapted (and the BaseRootKummer* family) are attempts/
  interfaces; BaseCompletionRootsActual has no olean. S342QVFamilyRootImpossibleActual
  records a specific no-NatRootSystem-in-completion obstruction for qVUnit.

Constructibility:
- algebraically closed value: **YES** (rootSystemOfAlgClosed/algClosedRootSystem).
- completion value: **NO unconditional constructor**; exactly completion first-field
  data (Nonempty NatRootSystem concreteQUnit). This is the open carrier.

## 2. CyclotomicTower

Definition: LeanFormal/IUT/IUTII/Kummer/KummerClass.lean:18
  structure CyclotomicTower (M) [CommMonoid M] where
    component : Nat → Mˣ
    torsion : forall n, component n ^ n = 1
    transition : forall n k, k != 0 → component (n*k)^k = component n

Constructors:
- CyclotomicTower.one (KummerClass.lean:28): trivial tower, unconditional.
- CyclotomicTower.mul (:35): product of towers.
- KummerClass.kummerClass (:60): from a root system and a Galois action, a tower of
  root ratios; requires a NatRootSystem r and fixed action.
- KummerClass.rootSystemDiff (:106): from two NatRootSystems of the same value,
  component n = second.root n / first.root n.
All green (KummerClass olean 328232 B).

Constructibility:
- trivial/product/difference towers: **YES** given the corresponding root systems.
- nontrivial completion tower without roots: **NO**; rootSystemDiff still needs the two
  completion root systems.

## 3. KummerClass.rootSystemDiff

Definition: KummerClass.lean:106-113:
  def rootSystemDiff (first second : NatRootSystem value) : CyclotomicTower M where
    component n := second.root n / first.root n
    torsion n := ...
    transition n k hk := ...
The rootChange_eq field of SourcePilotRegionDonors is literally
  rootChange = KummerClass.rootSystemDiff roots roots' (S1408; C3Actual:59).
Constructibility: **YES given first,second : NatRootSystem value**. No independent
existence; it inherits the root-system obstruction.

## 4. SourcePilotRegionCore and the L/old records

SourcePilotRegionCore (tmp/sheaf/xif/paper/S1391C3LSourcePilotActual.lean:98) fields:
p, place, q, thetaPacket, qUnit : (completion)ˣ, qUnit_eq, tensorIndex/tensorFintype/
tensorPlaceIndex/tensorPlaces/tensorTuple/tensorUnit/tensorLanding/tensorLanding_q.
The root/Kummer block is deliberately outside the core.

Constructors:
- actualSourcePilotRegionCore (:308): actual, built from concreteQCandidate,
  concreteThetaPacket, concreteQUnit, concrete tensor data; no root system. Green.
- oldSourcePilotToCore (:124): from an old SourcePilotRegionData; projects the core.
- sourcePilotRegionLToCore: L record to core.

Old completion block:
- structure CompletionRootBlock (S1391:146):
    roots : NatRootSystem C.qUnit
    roots' : NatRootSystem C.qUnit
    kummerClass : CyclotomicTower (completion)
    rootChange : CyclotomicTower (completion)
    rootChange_eq : rootChange = rootSystemDiff roots roots'
- oldSourcePilotToCompletionRootBlock (:157): from an old SourcePilotRegionData;
  conditional because it reads old roots.
- completionRootBlock_nonempty_iff (:221):
    Nonempty (CompletionRootBlock C) iff Nonempty (NatRootSystem C.qUnit).
  The second root can be equal to the first, kummerClass = one, rootChange =
  rootSystemDiff r r; so the whole block reduces to the first root field.
- actualCompletionRootBlock_nonempty_iff (:480) and
  oldSourcePilotWithActualCore_nonempty_iff (:511) reduce to
  completionFirstFieldObstruction; oldSourcePilotRegionData_nonempty_of_completionRootBlock
  (:490) is conditional on the block.

Actual L record:
- actualSourcePilotRegionDataL (S1391:329): actual, inputs I and place; roots are
  concreteRootsAlgebraicClosure (an algebraic-closure NatRootSystem), not completion
  roots; qUnitAlgClosure_eq records the map from the completion q unit.
- actualSourcePilotRegionDataL_roots(:)/roots'(:) point to the actual algebraic-closure
  root systems.
Important: SourcePilotRegionDataL.roots has type
  NatRootSystem (concreteQUnitAlgebraicClosure ...), whereas CompletionRootBlock.roots
  has type NatRootSystem C.qUnit (completion). The L roots are not literally completion
  roots; the missing transport/first completion root is exactly the obstruction.

## 5. S1408 sourcePilotRegionDonorsOfLBlock — full parameters

File: tmp/sheaf/xif/paper/S1408C3LSourcePilotConsumerActual.lean:116
  noncomputable def sourcePilotRegionDonorsOfLBlock
    (D : SourcePilotRegionDataL (I := I))
    (B : SourcePilotOldCompletionBlock (I := I) D) :
    SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I

- D supplies: p, place, q, thetaPacket, qUnit, roots (algebraic closure), roots',
  kummerClass/rootChange (Galois-indexed L data), tensor block. D is actual:
  actualSourcePilotRegionDataL (I) place.
- B is defined at S1408:72 as CompletionRootBlock (sourcePilotRegionLToCore D); it
  supplies the old completion roots/roots'/kummerClass/rootChange and their
  rootChange_eq, with roots in the completion unit (not the L algebraic-closure roots).
- B is not inhabited; S1408:76 sourcePilotOldCompletionBlock_nonempty_iff shows
  Nonempty B iff Nonempty (NatRootSystem D.qUnit), and actual... iff
  completionFirstFieldObstruction.
- Downstream: c3DonorConsumerOfLBlock (:132), oldSourcePilotOfLBlock (:150),
  oldSourcePilotOfLBlock_core_actual (:160).

## 6. Constructibility verdicts

| object | verdict | required data / reason |
|---|---|---|
| NatRootSystem in alg closed field | YES | rootSystemOfAlgClosed (green) |
| NatRootSystem in completion | NO unconditional | equivalent to completionFirstFieldObstruction; no constructor |
| CyclotomicTower.one | YES | unconditional |
| CyclotomicTower from roots | YES conditional | kummerClass/rootSystemDiff need NatRootSystem |
| rootSystemDiff | YES conditional | two NatRootSystems of same value |
| SourcePilotRegionCore | YES | actualSourcePilotRegionCore (concrete I, place) |
| CompletionRootBlock | NO | equivalent to Nonempty NatRootSystem C.qUnit |
| actualSourcePilotRegionDataL | YES | I + place; roots in alg closure |
| S1408 SourcePilotRegionDonors | NO | D (YES) + B CompletionRootBlock (NO) |
| SourcePilotRegionData (old) | NO unconditional | oldSourcePilotOfCoreAndBlock needs CompletionRootBlock |

Summary: the L side is actual; the old completion root block is the exact missing
carrier. The whole C3 donor reduces to the first completion root field
(NatRootSystem (concreteQUnit ...)); once that exists, the second root, trivial tower,
root change, block, donors, and old data all follow by S1391/S1408.
