import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Algebra.Algebra.Prod

universe u
variable {K : Type u} [Field K]
variable {B : Type u} [CommRing B] [Algebra K B]
variable (I J : Ideal B) (h : IsCompl I J)

#check (Ideal.quotientEquivAlgOfEq K (I := (⊥ : Ideal B)) (J := I ⊓ J) h.inf_eq_bot.symm)
#check (AlgEquiv.quotientBot K B).symm
#check (AlgEquiv.quotientBot K B).symm.trans ((Ideal.quotientEquivAlgOfEq K (I := (⊥ : Ideal B)) (J := I ⊓ J) h.inf_eq_bot.symm))
#check Ideal.Quotient.factor
#check Ideal.Quotient.factor_mk
#check Ideal.Quotient.factor_eq_mk
#check Ideal.Quotient.factor_apply
#check Ideal.Quotient.mk_algebraMap
