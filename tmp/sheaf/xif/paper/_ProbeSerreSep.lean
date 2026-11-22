import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Tactic
noncomputable section
open LeanFormal
namespace ProbeSerreSep
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  [IsDedekindDomain A] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra (FractionRing A) (FractionRing B)]
  (hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B))
example : differentIdeal A B ≠ ⊥ := by
  haveI : Algebra.IsSeparable (FractionRing A) (FractionRing B) := hsep
  exact differentIdeal_ne_bot
end ProbeSerreSep
