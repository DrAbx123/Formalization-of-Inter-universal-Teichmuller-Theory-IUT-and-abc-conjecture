import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.Separable

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2533RootIntegralActual

variable (R K L S : Type*)
  [CommRing R] [CommRing S]
  [Field K] [Field L]
  [Algebra R K] [Algebra R S] [Algebra S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsIntegralClosure S R L] [IsFractionRing R K]
  [FiniteDimensional K L] [IsGalois K L]

theorem S2533_root_integral
    (f : R[X]) (hmonic : f.Monic)
    {x : L} (hx : Polynomial.aeval x (f.map (algebraMap R L)) = 0) :
    ∃ y : S, algebraMap S L y = x := by
  have hint : IsIntegral R x :=
    IsIntegral.of_aeval_monic (hmonic.map (algebraMap R L)) hx
  exact (IsIntegralClosure.isIntegral_iff (A := S) (R := R) (B := L)).mp hint

def S2533_card_rootSet_required
    (f : R[X]) (hmonic : f.Monic)
    (hsep : (f.map (algebraMap R L)).Separable)
    (hsplit : (f.map (algebraMap R L)).Splits) : Prop :=
  Fintype.card (f.rootSet S) = f.natDegree

#print axioms S2533_root_integral
end LeanFormal.IUT.XiFPaper.S2533RootIntegralActual
end