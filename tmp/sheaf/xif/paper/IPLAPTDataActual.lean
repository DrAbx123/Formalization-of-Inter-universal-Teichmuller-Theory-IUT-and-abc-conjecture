import tmp.sheaf.xif.paper.IPLAPTActual
import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitFactorizationProvider
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceKummerEvaluationSquareExtension

/-!
# Actual self-strip IPL and Kummer-evaluation data

The production factorization provider supplies, for every F-prime-strip envStrip,
the unconditional kappa-orbit units-action datum on the canonical product group
  G := (v : V) -> envStrip.toDPrimeStrip.Pi v.
Using its actual supplied units action (not a trivial action) and the identity
strip representative, this file constructs:

* SourceTimesMuKummerLayer G envStrip envStrip;
* SourceEvaluationUnitPortion G envStrip envStrip;
* SourceKummerArrow G envStrip envStrip via sourceKummerArrowOfLayer;
* SourceEvaluationArrow G envStrip envStrip via
  sourceEvaluationArrowOfUnitPortion;
* SourceKummerEvaluationSquare G envStrip envStrip envStrip envStrip via
  SourceKummerEvaluationSquare.ofThreeLegs;
* KummerEvaluationActual G envStrip envStrip envStrip envStrip;
* IPLActual G envStrip envStrip envStrip envStrip envStrip.

This is the identity/trivial-source-strip specialization explicitly permitted by
the task. It is actual self-data of the canonical envStrip: the group actions
are the strip units actions composed with the canonical evaluation
factorization, the layer isomorphism is the actual identity isomorphism, and
the square is the three-legs extension of the actual self evaluation/Kummer
arrows. It is NOT the paper's non-trivial Kummer/evaluation arrow between
distinct env/gau/coric/q-pilot strips. The exact missing source arrows for the
non-trivial IPL are:

1. a SourceTimesMuKummerLayer G upper lower for genuinely different upper/lower
   strips with its non-identity TimesMuKummer.Isomorphism;
2. a SourceEvaluationUnitPortion G upper lower with its non-identity unit layer;
3. the lower-horizontal evaluation strip representative between the distinct
   environment/gau strips.

No toy data, True, PUnit, axiom, or sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace Theorem311Source
namespace IPLAPTDataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.FPrimeStrip
open LeanFormal.IUT.KappaOrbitUnitsActionDatum

universe uV

variable {V : Type uV}

/-- The canonical product group of a strip, as supplied by the factorization
provider. -/
abbrev SelfGroup (envStrip : FPrimeStrip V) : Type _ :=
  (v : V) -> envStrip.toDPrimeStrip.Pi v

/-- The actual self Kummer layer: both actions are the supplied units action of
the canonical kappa-orbit datum, and the layer isomorphism is the identity
TimesMuKummer isomorphism at that action. -/
noncomputable def selfKummerLayer (envStrip : FPrimeStrip V) :
    SourceTimesMuKummerLayer (SelfGroup envStrip) envStrip envStrip where
  sourceAction := fun v =>
    (envStrip.universalKappaOrbitUnitsActionDatum).suppliedUnitsAction v
  targetAction := fun v =>
    (envStrip.universalKappaOrbitUnitsActionDatum).suppliedUnitsAction v
  kummer := fun v =>
    TimesMuKummer.Isomorphism.refl
      ((envStrip.universalKappaOrbitUnitsActionDatum).suppliedUnitsAction v)

/-- The actual self evaluation unit portion: the same supplied action on both
sides and the identity unit-layer isomorphism. -/
noncomputable def selfEvaluationUnitPortion (envStrip : FPrimeStrip V) :
    SourceEvaluationUnitPortion (SelfGroup envStrip) envStrip envStrip where
  sourceAction := fun v =>
    (envStrip.universalKappaOrbitUnitsActionDatum).suppliedUnitsAction v
  targetAction := fun v =>
    (envStrip.universalKappaOrbitUnitsActionDatum).suppliedUnitsAction v
  unitLayer := fun v =>
    MulEquiv.refl (TimesMuQuotient ((envStrip.Mon v)ˣ))
  unitLayer_equivariant := fun v g x => rfl

/-- The actual self Kummer arrow from sourceKummerArrowOfLayer. -/
noncomputable def selfKummerArrow (envStrip : FPrimeStrip V) :
    SourceKummerArrow (SelfGroup envStrip) envStrip envStrip :=
  sourceKummerArrowOfLayer (FPrimeStripEquiv.refl envStrip)
    (selfKummerLayer envStrip)

/-- The actual self evaluation arrow from sourceEvaluationArrowOfUnitPortion. -/
noncomputable def selfEvaluationArrow (envStrip : FPrimeStrip V) :
    SourceEvaluationArrow (SelfGroup envStrip) envStrip envStrip :=
  sourceEvaluationArrowOfUnitPortion (FPrimeStripEquiv.refl envStrip)
    (selfEvaluationUnitPortion envStrip)

/-- The actual Kummer-evaluation square on the canonical envStrip, constructed
by the production three-legs extension from the self evaluation arrow, the two
self Kummer arrows, and the self unit portion. -/
noncomputable def selfKummerEvaluationSquare (envStrip : FPrimeStrip V) :
    SourceKummerEvaluationSquare (SelfGroup envStrip) envStrip envStrip
      envStrip envStrip :=
  SourceKummerEvaluationSquare.ofThreeLegs
    (selfEvaluationArrow envStrip)
    (selfKummerArrow envStrip)
    (selfKummerArrow envStrip)
    (selfEvaluationUnitPortion envStrip)

/-- The actual KummerEvaluationActual on the canonical envStrip. -/
noncomputable def selfKummerEvaluationActual (envStrip : FPrimeStrip V) :
    KummerEvaluationActual (G := SelfGroup envStrip) envStrip envStrip
      envStrip envStrip where
  square := selfKummerEvaluationSquare envStrip

/-- The actual IPLActual on the canonical envStrip. The input link is recorded
as the frozen composite expression itself, so the factorization field is
definitional. -/
noncomputable def selfIplActual (envStrip : FPrimeStrip V) :
    IPLActual (G := SelfGroup envStrip) envStrip envStrip envStrip envStrip
      envStrip where
  lowerHorizontal1 := FPrimeStripEquiv.refl envStrip
  lowerHorizontal2 := FPrimeStripEquiv.refl envStrip
  kummer := selfKummerArrow envStrip
  evaluation := selfEvaluationArrow envStrip
  inputLink :=
    (FPrimeStripEquiv.refl envStrip).symm.trans
      ((FPrimeStripEquiv.refl envStrip).symm.trans
        ((selfKummerArrow envStrip).stripIso.trans
          (selfEvaluationArrow envStrip).stripIso))
  factorization := rfl

/-- The frozen IPL factorization is rfl for the constructed self data. -/
theorem selfIplActual_factorization (envStrip : FPrimeStrip V) :
    (selfIplActual envStrip).inputLink =
      (selfIplActual envStrip).composite :=
  (selfIplActual envStrip).factorization

/-- The Kummer-evaluation two-path equality is the actual square equality. -/
theorem selfKummerEvaluationActual_twoPath (envStrip : FPrimeStrip V) :
    (selfKummerEvaluationActual envStrip).square.domainExpression =
      (selfKummerEvaluationActual envStrip).square.codomainExpression :=
  (selfKummerEvaluationActual envStrip).square.domainExpression_eq_codomainExpression

end IPLAPTDataActual
end Theorem311Source
end LeanFormal.IUT
end
