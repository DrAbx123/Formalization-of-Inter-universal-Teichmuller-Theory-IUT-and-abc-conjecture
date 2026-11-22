/-
# S2557: scope assessment for adding lift uniqueness

Core definition: Iut/Foundations/Orbicurve.lean, structure
EtalePseudofunctorSquare.TwoPullbackWitness.
Search over permanent files (excluding `_` probes) finds 59 structure-literal
sites `TwoPullbackWitness where|:=`, in 33 files.  Any new mandatory field
breaks every literal and every alias that constructs a witness; each site then
needs a genuine uniqueness proof, not a mechanical one.

This file provides the non-breaking mixin alternative.
-/
import tmp.sheaf.xif.paper.S2556LiftUniquenessInterfaceActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2556LiftUniquenessInterfaceActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2557LiftUniquenessScopeActual

universe u
variable {F : Type u} [Field F]

/-- Non-breaking mixin: a two-pullback witness together with the missing
lift-uniqueness coherence.  Existing `TwoPullbackWitness` constructors are
unaffected; only consumers that need uniqueness require this mixin. -/
structure S2557WitnessWithLiftUniqueness
    {P X Y Z : Iut.EtaleStackPseudofunctor F}
    (sq : Iut.EtalePseudofunctorSquare P X Y Z) where
  witness : sq.TwoPullbackWitness
  liftUniq : S2556LiftUniqueness sq witness

theorem S2557LiftUniqueness_of_data
    {P X Y Z : Iut.EtaleStackPseudofunctor F}
    {sq : Iut.EtalePseudofunctorSquare P X Y Z}
    (w : S2557WitnessWithLiftUniqueness sq) :
    S2556LiftUniqueness sq w.witness :=
  w.liftUniq

/-! ## Scope of forcing a core field

Core file: `Iut/Foundations/Orbicurve.lean` (definition).

Permanent constructor sites (59, from search over files not named `_*`):

- S1762CoverLimitsActual (1)
- S1800IdentityAtlasSmallnessActual (1)
- S1801LiftEssSurjActual (1)
- S1844PointSeparatedActual (1)
- S1845Dev (2)
- S1850RefuteS1756Actual (1)
- S1896BoundaryCuspActual (1)
- S1897CoherentEssSurjActual (1)
- S1900StrongSliceRealizationActual (2)
- S1911RepresentableTwoPullbackActual (1)
- S1926RepresentableOpenImmersionActual (1)
- S1943AssembleEssSurjActual (2)
- S2010BaseChangeFullActual (1)
- S2023SourceSchemeActual (1)
- S2058D6FiniteEtaleActual (1)
- S2062TwoPullbackPasteActual (1)
- S2071PastingWitnessActual (1)
- S2076IsoCommaTwoPullbackActual (1)
- S2097BaseChangeButterflyActual (3)
- S2107RightCancelActual (2)
- S2108PastedTransportActual (3)
- S2114CanonicalLiftTwoCellActual (4)
- S2115UpperTwoCellFullActual (1)
- S2121ChoiceFreeLowerWitnessActual (4)
- S2124ToYEquationActual (4)
- S2127ToYLegsActual (2)
- S2185ConcreteTwoPullbackActual (2)
- S2240StrictConeIsoActual (6)
- S2512StackOpenImmersionUB (2)
- S2514IdentityFiniteEtaleActual (1)
- S2515TwoPullbackUBActual (1)
- S2517CoverEquivMapActual (1)
- S2547TransportIsoActual (1)

Additionally the `abbrev`/alias sites (S2114WP, S2121WP/W2, S2115UpperWitness,
S2547Witness-backed presentations, etc.) inherit the field without a new proof,
but every direct structure literal needs a uniqueness proof.
-/

#check S2557WitnessWithLiftUniqueness
#check S2557LiftUniqueness_of_data
end LeanFormal.IUT.XiFPaper.S2557LiftUniquenessScopeActual
end