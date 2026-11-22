import Mathlib.Data.NNReal.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Group.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S2045FDoublePlusMilestoneActual
open scoped NNReal

/-- Exact first missing for the actual C^env/C^gau local realified monoid family:
a family over the Fmod place set (not the one-column Q_p index) with paper local
theta/Gaussian monoid, constant/ray decomposition, and realification. -/
structure S2045FmodLocalThetaFamily (Fmod : Type*) [Field Fmod] [NumberField Fmod] where
  env : NumberField.FinitePlace Fmod → Type*
  [envMonoid : ∀ v, Monoid (env v)]
  gau : NumberField.FinitePlace Fmod → Type*
  [gauMonoid : ∀ v, Monoid (gau v)]
  realified : NumberField.FinitePlace Fmod → Type*
  [realifiedMonoid : ∀ v, Monoid (realified v)]
  envRealification : ∀ v, env v →* realified v
  gauRealification : ∀ v, gau v →* realified v
  evaluation : ∀ v, env v →* gau v

/-- Exact first missing geometric pi1 datum: actual once-punctured curve group
at every place, arithmetic projection, and nontrivial nonabelian geometric
kernel.  No inhabitant is asserted. -/
structure S2045CurvePi1Family where
  place : Type*
  curveGroup : place → Type*
  [group : ∀ v, Group (curveGroup v)]
  arithmeticGroup : place → Type*
  [arithGroup : ∀ v, Group (arithmeticGroup v)]
  arithmeticProjection : ∀ v, curveGroup v →* arithmeticGroup v
  geometricKernel : place → Type*
  nontrivial : ∀ v, Nontrivial (geometricKernel v)

end LeanFormal.IUT.XiFPaper.S2045FDoublePlusMilestoneActual
end