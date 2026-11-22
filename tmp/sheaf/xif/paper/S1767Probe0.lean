/-
Probe for S1767: check that S1745's instances apply to (CommAlgCat.FiniteEtale K)^op.
-/
import tmp.sheaf.xif.paper.S1745FiniteEtaleLimitsActual
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Equivalence

open CategoryTheory CategoryTheory.Limits

namespace S1767Probe

abbrev FiniteEtaleAlg (K : Type) [Field K] : Type 1 := (CommAlgCat.FiniteEtale K)ᵒᵖ

variable {K : Type} [Field K]

example : HasPullbacks (FiniteEtaleAlg K) := inferInstance
example : HasFiniteCoproducts (FiniteEtaleAlg K) := inferInstance
example : HasPullbacks (FiniteEtaleAlg K) := S1745.FiniteEtaleClosure.hasPullbacks (K := K)
example : HasFiniteCoproducts (FiniteEtaleAlg K) := S1745.FiniteEtaleClosure.hasFiniteCoproducts (K := K)

end S1767Probe
