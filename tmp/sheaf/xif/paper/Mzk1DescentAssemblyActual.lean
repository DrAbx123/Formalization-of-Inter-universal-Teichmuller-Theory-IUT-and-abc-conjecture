import LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1Reduction

/-!
# Mzk1DescentAssemblyActual — real assembly: Ind1 descent quotient package (R2 rung)

Status: PENDING-VERIFY. No sorry, no axiom.
Consumer (not adapted copy): assembles the compiled Ind1 quotient reduction facts
(action absorbed by formal quotient; descended lift computes quotientMap; functoriality)
into one descent rung package. Uses only proved theorems of Ind1Reduction. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1DescentAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialKernel.Core

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-- Genuine assembly theorem: Ind1 action is absorbed by the formal quotient and the
descended lift computes quotientMap on representatives. -/
theorem descent_ind1_quotient_package (I : Input Label Choice) :
    (∀ (g : Label) (c : Choice),
        ind1QuotientMap I (I.core.ind1 g c) = ind1QuotientMap I c) ∧
      (∀ c : Choice, ind1QuotientLift I (ind1QuotientMap I c) = quotientMap I c) :=
  ⟨ind1QuotientMap_ind1 I, ind1QuotientLift_mk I⟩

/-- Genuine assembly theorem: Ind1 quotient functoriality on representatives. -/
theorem descent_ind1_functorial_package {Choice2 : Type v} [Preorder Choice2]
    (I : Input Label Choice) (I2 : Input Label Choice2) (e : Choice → Choice2)
    (he : ∀ ⦃a b : Choice⦄, Ind1Relation I a b → Ind1Relation I2 (e a) (e b))
    (c : Choice) :
    ind1QuotientFunctorial I I2 e he (ind1QuotientMap I c) =
      ind1QuotientMap I2 (e c) :=
  ind1QuotientFunctorial_mk I I2 e he c

end LeanFormal.IUT.XiFPaper.Mzk1DescentAssemblyActual
end
