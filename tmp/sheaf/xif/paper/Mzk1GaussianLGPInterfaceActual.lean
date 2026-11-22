import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Theta.GaussianSquareSum
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteHodgeTheaterExample

/-!
# Mzk1GaussianLGPInterfaceActual — Gaussian/LGP interface over the tree Gaussian assets

STEP 0 prior-art (reused, no new mathematics):
* Foundations/Theta/GaussianKernel (gaussExponent, realThetaValue, Gaussian theta values);
* Foundations/Theta/GaussianSquareSum (gaussianSquareSum, normalizedGaussianDegree and its
  factor formula);
* Foundations/Theta/SignedLabelEquiv (signed labels, translation, sum invariance, cardinality);
* IUTI/HodgeTheater/ConcreteHodgeTheaterExample (gaussianHodgeTheater, gaussianThreeTheaterSystem).

WHAT THIS FILE DOES:
* defines the typed Gaussian/LGP interface model at a prime l: the Gaussian Hodge theater,
  the Gaussian q-parameter (0<q<1 with q = 1/2 for the concrete model) and its theta packet;
* proves the concrete model's theta-packet q, signed-label cardinality, the Gaussian
  normalization factor and the basic Gaussian value positivity;
* records rows, keeping the paper-level Gaussian/LGP compatibility statement NAMED.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GaussianLGPInterfaceActual

open LeanFormal.IUT
open scoped BigOperators

/-- The Gaussian/LGP interface model at a prime l >= 5: a Gaussian Hodge theater and a
Gaussian q-parameter in the convergence range (concrete: q = 1/2). -/
structure GaussianLGPModel (l : PrimeGeFive) where
  /-- the Gaussian Hodge theater (tree concrete example). -/
  hodgeTheater : HodgeTheater l RationalPrimePlace
  /-- the Gaussian q-parameter. -/
  q : ℝ
  /-- convergence range: q > 0. -/
  q_pos : 0 < q
  /-- convergence range: q < 1. -/
  q_lt_one : q < 1
  /-- concrete value q = 1/2. -/
  q_eq : q = 1 / 2

/-- The concrete Gaussian/LGP model from the tree assets. -/
noncomputable def gaussianLGPModel (l : PrimeGeFive) : GaussianLGPModel l where
  hodgeTheater := gaussianHodgeTheater l
  q := 1 / 2
  q_pos := by norm_num
  q_lt_one := by norm_num
  q_eq := rfl

/-- The Gaussian/LGP model is nonempty for every l >= 5. -/
theorem gaussianLGPModel_nonempty (l : PrimeGeFive) : Nonempty (GaussianLGPModel l) :=
  ⟨gaussianLGPModel l⟩

/-- The concrete Gaussian Hodge theater's theta-packet q-parameter is 1/2. -/
theorem gaussianLGPModel_theater_q (l : PrimeGeFive) :
    (gaussianLGPModel l).hodgeTheater.thetaPacket.q = 1 / 2 :=
  gaussianHodgeTheater_q l

/-- The concrete model's q-parameter is in (0,1). -/
theorem gaussianLGPModel_q_mem (l : PrimeGeFive) :
    0 < (gaussianLGPModel l).q ∧ (gaussianLGPModel l).q < 1 :=
  ⟨(gaussianLGPModel l).q_pos, (gaussianLGPModel l).q_lt_one⟩

/-- Gaussian theta values are positive for q > 0. -/
theorem gaussianLGPModel_thetaValue_pos {q : ℝ} (hq : 0 < q) (j : ℤ) :
    0 < realThetaValue q j :=
  realThetaValue_pos hq j

/-- The signed-label cardinality is l. -/
theorem gaussianLGPModel_card_signedLabel (l : PrimeGeFive) :
    Fintype.card (SignedLabel l.value) = l.value :=
  card_signedLabel l

/-- The Gaussian square-sum normalization factor is l(l+1)/12 for odd l >= 5. -/
theorem gaussianLGPModel_normalization (l : PrimeGeFive) :
    normalizedGaussianDegree l.value = (l.value : ℝ) * ((l.value : ℝ) + 1) / 12 :=
  normalizedGaussianDegree_eq_factor l.value l.odd l.ge_five

/-- Gaussian/LGP rows: (paper object, formal asset, status). -/
def gaussianLGPRows : List (String × String × String) :=
  [ ("Gaussian Hodge theater", "gaussianHodgeTheater; gaussianLGPModel.hodgeTheater", "TREE ASSET + carrier"),
    ("Gaussian q-parameter (0<q<1, concrete 1/2)", "gaussianLGPModel.q/q_pos/q_lt_one/q_eq", "PROVED (concrete model)"),
    ("theta-packet q at 1/2", "gaussianLGPModel_theater_q", "PROVED (rfl via tree)"),
    ("Gaussian theta values positive", "realThetaValue_pos; gaussianLGPModel_thetaValue_pos", "TREE PROOF (re-exported)"),
    ("signed-label cardinality", "card_signedLabel; gaussianLGPModel_card_signedLabel", "TREE PROOF (re-exported)"),
    ("Gaussian normalization factor l(l+1)/12", "normalizedGaussianDegree_eq_factor; gaussianLGPModel_normalization", "TREE PROOF (re-exported)"),
    ("paper Gaussian/LGP compatibility (theta x log compatibility)", "not asserted; tree Gaussian assets + Hodge theater carrier only", "NAMED (paper input)") ]

/-- The Gaussian/LGP row record has seven rows. -/
theorem gaussianLGPRows_length : gaussianLGPRows.length = 7 := rfl

#check GaussianLGPModel
#check gaussianLGPModel
#check gaussianLGPModel_nonempty
#check gaussianLGPModel_theater_q
#check gaussianLGPModel_card_signedLabel
#check gaussianLGPModel_normalization
#check gaussianLGPRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GaussianLGPInterfaceActual
end
