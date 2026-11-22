import tmp.sheaf.n8.closure.O3ConstructedComparison
import tmp.sheaf.n8.closure.EtaTensorZpSubmoduleLatticeActual

/-!
# C7 lattice index divisors: precise obstruction

Actual data available:

* Q = qORegionLogVolume X (qO endpoint).
* hTensor = log tensorHaar X (nnLattice X gNonIntegral 1) (tensor endpoint).
* actual Z_p lattices LuSub, LvSub(g) and edgeZp : LuSub -> LvSub(g).

The proposed construction A := lattice index of LuSub in LvSub(g),
Z := 0 does give an actual natural-number index candidate if the finite
index/relIndex is available.  It does NOT by itself prove the comparison law

  hTensor - d * Q = S - kappa.

The missing object is the actual edge comparison law/normalization identifying
the qO Q with the tensor hTensor along the lattice edge.  No arbitrary divisor
or index is fabricated.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.O3ConstructedComparison
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open ABCBridge.N8.C3TensorTargetCorrection

namespace LeanFormal.IUT.N8Closure.C7LatticeIndexDivisors

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- Actual endpoint Q (re-export). -/
noncomputable def Q : ℝ := O3Q X

/-- Actual tensor endpoint h (re-export). -/
noncomputable def hTensor : ℝ := O3HTensor X

/-- Exact missing inclusion lemma LuSub <= LvSub(g0) for g0 = fPlaceP^{-1}. -/
def MissingLuSubLeLvSub : Prop :=
  ∀ x : E X, x ∈ Lu X → x ∈ Lv X (gNonIntegral X)

/-- Exact missing edge comparison law: the qO endpoint and tensor endpoint are
related by the lattice multiplier/effective zero. -/
def MissingEdgeComparisonLaw : Prop :=
  ∃ (d : ℕ) (A Z kappa S : ℝ),
    kappa = A ∧ S = Z ∧
    hTensor X - (d : ℝ) * Q X = S - kappa ∧ 0 ≤ S

/-- Exact C7 object: actual lattice index exponent plus A,Z and law. -/
structure C7Divisors where
  d : ℕ
  A : ℝ
  Z : ℝ
  kappa : ℝ
  S : ℝ
  kappa_eq_A : kappa = A
  S_eq_Z : S = Z
  law : hTensor X - (d : ℝ) * Q X = S - kappa
  S_nonneg : 0 ≤ S

/-- Decisive obstruction: index/A/Z candidates alone do not yield C7Divisors;
the missing source object is the edge comparison law/normalization. -/
def MissingC7EdgeComparisonObject : Prop := Nonempty (C7Divisors X)

end LeanFormal.IUT.N8Closure.C7LatticeIndexDivisors
