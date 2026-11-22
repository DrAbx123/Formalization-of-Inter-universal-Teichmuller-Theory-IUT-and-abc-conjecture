import tmp.sheaf.xif.paper.S1965FDoublePlusStripActual
import tmp.sheaf.xif.paper.S1973PsiCnsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S2044FDoublePlusActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.S1965FDoublePlusStripActual
open LeanFormal.IUT.XiFPaper.S1966LocalThetaMonoidActual

/-- Actual local env/gau monoid family over the source finite prime places,
using the S1973 actual Psi_env/Psi_gau models and their evaluation. -/
structure S2044LocalMonoidFamily (l : PrimeGeFive) where
  env : (v : FinitePrimePlace 2 7) -> Type
  [envMonoid : ∀ v, Monoid (env v)]
  gau : (v : FinitePrimePlace 2 7) -> Type
  [gauMonoid : ∀ v, Monoid (gau v)]
  evaluation : (v : FinitePrimePlace 2 7) -> env v →* gau v
  evaluation_bijective : ∀ v, Function.Bijective (evaluation v)
  env_eq_model : ∀ v, env v = PsiEnvModel v
  gau_eq_model : ∀ v, gau v = PsiGauModel v l

/-- The actual family of S1973 models. -/
noncomputable def s2044Family (l : PrimeGeFive) : S2044LocalMonoidFamily l where
  env := fun v => PsiEnvModel v
  envMonoid := fun v => inferInstance
  gau := fun v => PsiGauModel v l
  gauMonoid := fun v => inferInstance
  evaluation := fun v => psiEvaluation v l
  evaluation_bijective := fun v => psiEvaluation_bijective v l
  env_eq_model := fun _ => rfl
  gau_eq_model := fun _ => rfl

/-- Paper-faithful C^⊩env/C^⊩gau local realified monoid family.  This is
NOT the S1973 model family: it requires the actual paper local monoids together
with their identification to the S1973 models.  No inhabitant is asserted. -/
structure S2044PaperLocalMonoidFamily (l : PrimeGeFive) where
  env : (v : FinitePrimePlace 2 7) -> Type
  [envMonoid : ∀ v, Monoid (env v)]
  gau : (v : FinitePrimePlace 2 7) -> Type
  [gauMonoid : ∀ v, Monoid (gau v)]
  env_identification : ∀ v, env v ≃* PsiEnvModel v
  gau_identification : ∀ v, gau v ≃* PsiGauModel v l

/-- Exact first missing: the paper's cohomological Psi_cns(Pi_v) construction
and its identification with the actual local field model (S1973 first missing). -/
structure S2044PsiCnsConstruction (l : PrimeGeFive) where
  psiCns : (v : FinitePrimePlace 2 7) -> Type
  identification : ∀ v, psiCns v = PsiCnsModel v

/-- Exact first missing geometric pi1: the tempered/etale fundamental group of
the once-punctured elliptic curve with nontrivial geometric kernel, attached to
FDoublePlusPrimeStrip.  The numberFieldPrimeStrip has trivial kernels. -/
structure S2044GeometricPi1 where
  fundamentalGroup : Type
  geometricKernel : Type
  nontrivial : Nontrivial geometricKernel

end LeanFormal.IUT.XiFPaper.S2044FDoublePlusActual
end