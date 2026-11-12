# S2549 functor assembly: ACTUAL

## BUILT (EXIT=0)
S2549FunctorAssemblyActual.lean:
- S2549S2540Functor_full_faithful : S2540Functor.Full ∧ S2540Functor.Faithful.
- S2549S2540Functor_fullyFaithful : S2540Functor.FullyFaithful.
- S2549S2519Functor_full_faithful : S2519InvFunctor.Full ∧ S2519InvFunctor.Faithful.
- S2549S2519Functor_fullyFaithful : S2519InvFunctor.FullyFaithful.
- S2549S2519Functor_isEquivalence (h : S2519InvFunctor.EssSurj) : S2519InvFunctor.IsEquivalence.
- S2549S2519Equivalence (h) : FiniteEtaleCover S2482AffineScheme ≌ OrbicurveFiniteEtaleCover.
Axioms trio; no sorryAx.

Dependencies actual: S2547CorrectedFunctorFullActual, S2548S2519FullyFaithfulActual, S2542FunctorFaithfulActual.

## Remaining
EssSurj of S2519InvFunctor (qside) is the only missing IsEquivalence input.
No fake.