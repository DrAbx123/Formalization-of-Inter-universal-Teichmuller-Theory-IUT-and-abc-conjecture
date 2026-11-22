/-!
# Frd02: Frobenioid tree-asset reuse audit (data only)

Tree assets to REUSE for [FrdI]/[FrdII] (no re-proof):
* production model Frobenioid boundary:
  LeanFormal/IUT/IUTII/Frobenioid/ConcreteSourceFrobenioidBridge.lean
  ConcreteSourceFrobenioidBoundary (fields: cStage, place, model :
  Iut.FrobenioidPresentation, model_input : Iut.SourceModelFrobenioid.Input ...);
  concreteSourceFrobenioidBoundary(l) (noncomputable def); boundary_cStage /
  boundary_place / boundary_model / boundary_model_input / boundary_kernel;
  concrete_place_comap/stable/multiplicative/selected_input/input_arithmetic;
  source_stage_base_connected; concreteStage* abbrevs (place/stage/base/divisor/
  modelInput/Model/IntegralFunctor/IntegralColimit/ZeroFunctor/ZeroColimit/
  IndIntegralMonoid/SourceMLF).
* Iut foundations (importable): Iut.Foundations.SourceModelFrobenioidPresentation
  (frobenioidPresentation [IsConnected D]); SourceModelFrobenioidRationalNaturality;
  SourceModelFrobenioidZeroEvaluation.
* production Frobenioid examples/actions (LeanFormal/IUT/IUTII/Frobenioid/):
  DivisorialMonoidMinimalReplacement, Example36FrobeniusValueAction,
  Example36PrimeStripDivisorFrobenius, Example36LogShellFrobeniusAction,
  Example36FrobenioidTransport, Example36* (many local/global place assets),
  ConcreteLocalKummerExample, ConcreteTateCurveExample.
* production source MLF / reconstruction: Iut.SourceFinitePlaceReconstruction
  (Base/IndIntegralMonoid), Iut.SourceMLFIntegralMonoid.
* audit obligations: LeanFormal/IUT/Audit/Diagnostics/LegacyContracts (anabelian/
  Frobenioid construction notes); dispute ledger notes Frobenioids treated honestly.
* corpus texts: The Geometry of Frobenioids I/II (+ comments), Responses to
  questions on Frobenioids (papers/motizuki_corpus/text).
Classification: construction/boundary layer = A (exists, concrete); paper
category-theoreticity/functoriality theorems = B (named, not claimed).
**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.Frd02ReuseAuditActual

/-- Reuse rows: (paper component, tree asset, class). -/
def frdReuseAudit : List (String × String × String) :=
  [ ("concrete source Frobenioid boundary", "ConcreteSourceFrobenioidBridge: ConcreteSourceFrobenioidBoundary + concreteSourceFrobenioidBoundary(l) + boundary_* theorems + concreteStageModel : Iut.FrobenioidPresentation", "A (reuse)"),
    ("model Frobenioid presentation", "Iut.Foundations.SourceModelFrobenioidPresentation.frobenioidPresentation [IsConnected D]", "A (reuse)"),
    ("divisor monoid minimal replacement", "IUTII/Frobenioid/DivisorialMonoidMinimalReplacement.lean", "A/B (reuse)"),
    ("Frobenius action on values/log-shell", "IUTII/Frobenioid/Example36FrobeniusValueAction.lean; Example36LogShellFrobeniusAction.lean; Example36PrimeStripDivisorFrobenius.lean", "A (reuse) / B semantics"),
    ("local Kummer / Tate curve examples", "IUTII/Frobenioid/ConcreteLocalKummerExample.lean; ConcreteTateCurveExample.lean", "A (reuse)"),
    ("Frobenioid transport", "IUTII/Frobenioid/Example36FrobenioidTransport.lean", "A (reuse)"),
    ("source MLF / finite place reconstruction", "Iut.SourceFinitePlaceReconstruction (Base/IndIntegralMonoid); Iut.SourceMLFIntegralMonoid", "A (reuse)"),
    ("category-theoreticity/functoriality paper theorems", "FrdI §§1-6; FrdII Thm 1.2/Thm 2.4/Prop 3.4", "B (named; not claimed)") ]

end LeanFormal.IUT.XiFPaper.Frd02ReuseAuditActual
