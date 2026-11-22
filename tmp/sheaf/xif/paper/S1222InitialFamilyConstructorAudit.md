# S1222: can S1218 initial/family be filled by existing constructors?

Date: 2026-10-30. Report only; no new wrapper.

## Question

S1218 found the first OriginalInput fields missing:
  initial : SourceDefinition31Data l
  family  : SourceHodgeTheaterFamily l (FinitePrimePlace 2 7)
Check whether existing SourceDefinition31Data.toSource / HodgeTheaterFamily
constructors supply them.

## initial

SourceDefinition31Data.toSource exists only as StageConstructionTrace.toSource
(SourceDefinition31RootLemmas.lean:3807):
  T : StageConstructionTrace l  |->  T.toSource : SourceDefinition31Data l.
There is no concrete StageConstructionTrace l in the tree.  The available
relation is only
  sourceStageConstructionTraceEquiv : SourceDefinition31Data l ≃ StageConstructionTrace l
(and Nonempty-level statements), not an inhabitant.  So initial is not
supplied.

## family

There is an actual constructor at FinitePrimePlace 2 7:
  finiteIntegralTwoTheaterFamily l :
    SourceHodgeTheaterFamily l (FinitePrimePlace 2 7)
(SourceHodgeTheaterFamilyLawsReduction.lean:431), built from
twoTheaterWitnessFamily with index := Bool.

But OriginalInput requires index_equiv : family.index ≃ Int × Int
(SourceOriginalInput.lean:44).  Bool is not equivalent to Int × Int, so this
actual family cannot be the OriginalInput family.

The general constructor
  sourceInitialThetaSpineFamily (S : SourceInitialThetaData l) theta P hP E
(SourceHodgeTheaterFamilySourceReduction.lean:310) can build a family over any
index I, but requires:
* S : SourceInitialThetaData l;
* theta : FiniteThetaPacket l;
* P : I -> FPrimeStrip (FinitePrimePlace 2 7) with Function.Injective P;
* E : FPrimeStripLinkSystem P.
For I = SourceTheorem311Index = Int × Int, no actual injective P and link
system E are present.  The Bool-valued finiteIntegralTwoTheaterFamily is not
usable because of index_equiv.

## Minimal actual path (conditional, no construction available)

1. Provide T : StageConstructionTrace l, set initial := T.toSource.
2. Choose I := SourceTheorem311Index (Int × Int), set index_equiv := Equiv.refl.
3. Provide S : SourceInitialThetaData l, theta, an injective
   P : I -> FPrimeStrip (FinitePrimePlace 2 7), and E : FPrimeStripLinkSystem P;
   set family := sourceInitialThetaSpineFamily S theta P hP E.
4. Prove arithmetic_alignment:
   (family.theater i).arithmetic = initial.arithmetic.
   family gives S.candidate.arithmetic; initial gives T.arithmetic; this needs
   a shared arithmetic root (a Definition31DualContractAlignment-style
   equality T.arithmetic = S.candidate.arithmetic).

No T, S, P or E with the needed Int × Int index is actual in the tree.

## Exact conclusion

initial: exact gap is StageConstructionTrace l / concrete SourceDefinition31Data.
family: actual constructor exists only with index Bool at FinitePrimePlace 2 7,
which cannot satisfy OriginalInput.index_equiv : family.index ≃ Int × Int;
Int × Int-indexed injective strip family + link system is missing.

No new wrapper, no weak Prop/Nonempty gate.
