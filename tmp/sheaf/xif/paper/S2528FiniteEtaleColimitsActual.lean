import tmp.sheaf.xif.paper._S1779ClosureProbe

noncomputable section
open CategoryTheory Limits

namespace LeanFormal.IUT.XiFPaper.S2528FiniteEtaleColimitsActual

universe u

/-- The opposite of finite etale R-algebras has finite coproducts. -/
noncomputable instance S2528HasFiniteCoproducts (R : Type) [CommRing R] :
    HasFiniteCoproducts ((CommAlgCat.FiniteEtale.{0} R)ᵒᵖ) :=
  S1779Closure.FiniteEtaleClosure.hasFiniteCoproducts (R := R)

/-- The opposite of finite etale R-algebras has pullbacks. -/
noncomputable instance S2528HasPullbacks (R : Type) [CommRing R] :
    HasPullbacks ((CommAlgCat.FiniteEtale.{0} R)ᵒᵖ) :=
  S1779Closure.FiniteEtaleClosure.hasPullbacks (R := R)

#check S2528HasFiniteCoproducts
#check S2528HasPullbacks
end LeanFormal.IUT.XiFPaper.S2528FiniteEtaleColimitsActual
end