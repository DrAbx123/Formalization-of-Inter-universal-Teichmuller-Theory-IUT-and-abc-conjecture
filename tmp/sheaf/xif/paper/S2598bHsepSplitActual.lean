/-
S2598b: the S2543 separability and splitting hypotheses for the concrete
localized model.

S2543 `FrobeniusOrbitActual` works with the data

  f : R[X], p : Ideal R, P : Ideal S,
  hmonic : f.Monic,
  hsep : (f.map (Ideal.Quotient.mk p)).Separable,
  hsplit : (f.map (algebraMap R L)).Splits,

where `R = O_{F'}[1/10]`, `S = O_L[1/10]` and `L` is the actual 5-division
field (S2537).  The concrete model used by S2544/S2545/S2548 and S2667 is

  f = f10' (S2577),   p = p10 (S2577),   L = S2057FiveDivisionField (S2057).

This file closes the three `f`-side hypotheses for that model:

* `S2598b_hmonic : f10'.Monic` (from S2577);
* `S2598b_hsep : (f10'.map (Ideal.Quotient.mk p10)).Separable`;
* `S2598b_hsplit : (f10'.map (algebraMap R10 L10)).Splits`.

The separability is reduced to `Irreducible (f10'.map φ10)` over the
perfect field `ZMod 613`, transported back along the residue isomorphism
`e : R ⧸ p10 ≃+* ZMod 613` (both from S2577).

The splitting rewrites `f10' = C u * S2132Psi5Z.map (algebraMap ℤ R10)`
and uses `S2003Psi5Z_map_K` (S2577) together with
`Polynomial.SplittingField.splits` for `S2057Psi5F`; the scalar factor
`C u` is harmless for splitting (`Polynomial.Splits.C_mul`).

No sorry/axiom/native_decide/True is used.
-/
import tmp.sheaf.xif.paper.S2577Away10FbarActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2577Away10FbarActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual

attribute [local instance] Ideal.Quotient.field

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

abbrev R10 : Type := S2537ConcreteLocalizationActual.R

abbrev L10 : Type := S2057DedekindFrobBridgeActual.S2057FiveDivisionField

/-- The concrete `f = f10'` is monic. -/
theorem S2598b_hmonic : S2577Away10FbarActual.f10'.Monic :=
  S2577Away10FbarActual.f10'_monic

/-- The `hsep` hypothesis of S2543 for `f = f10'` and `p = p10`. -/
theorem S2598b_hsep :
    (S2577Away10FbarActual.f10'.map
      (Ideal.Quotient.mk S2577Away10FbarActual.p10)).Separable := by
  haveI hp10 : (S2577Away10FbarActual.p10).IsMaximal :=
    S2577Away10FbarActual.p10_max
  letI : Field (R10 ⧸ S2577Away10FbarActual.p10) := Ideal.Quotient.field _
  have hI : Irreducible (S2577Away10FbarActual.fbar10.map
      S2577Away10FbarActual.e.toRingHom) := by
    rw [← S2577Away10FbarActual.fbar10_map_e]
    exact S2577Away10FbarActual.f10'_map_φ_irreducible
  have hsep' : (S2577Away10FbarActual.fbar10.map
      S2577Away10FbarActual.e.toRingHom).Separable :=
    PerfectField.separable_of_irreducible hI
  exact (Polynomial.separable_map S2577Away10FbarActual.e.toRingHom).mp hsep'

/-- The `hsplit` hypothesis of S2543 for `f = f10'` and `L = L10`. -/
theorem S2598b_hsplit :
    (S2577Away10FbarActual.f10'.map (algebraMap R10 L10)).Splits := by
  have hcompK : (algebraMap S1720Field L10).comp
      (Int.castRingHom S1720Field) = Int.castRingHom L10 := by
    ext z
    simp
  have h2 : (algebraMap S1720Field L10) (2 : S1720Field) = (2 : L10) := by
    simpa using map_natCast (algebraMap S1720Field L10) 2
  have hPsi : S2132Psi5Z.map (Int.castRingHom L10) =
      Polynomial.C ((2 : L10) ^ 36) *
        S2057Psi5F.map (algebraMap S1720Field L10) := by
    have h := congrArg (Polynomial.map (algebraMap S1720Field L10))
      S2577Away10FbarActual.S2003Psi5Z_map_K
    simpa [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      hcompK, h2] using h
  have hcomp : (algebraMap R10 L10).comp (algebraMap ℤ R10) =
      Int.castRingHom L10 := by
    ext z
    simp
  unfold S2577Away10FbarActual.f10'
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hcomp, hPsi]
  exact Polynomial.Splits.C_mul
    (Polynomial.Splits.C_mul
      (Polynomial.SplittingField.splits (f := S2057Psi5F)) _) _

/-- `S2582`'s `fbar10_separable`, re-established here. -/
theorem fbar10_separable : S2577Away10FbarActual.fbar10.Separable :=
  S2598b_hsep

/-- `S2582`'s `f10'_map_L_splits`, re-established here. -/
theorem f10'_map_L_splits :
    (S2577Away10FbarActual.f10'.map (algebraMap R10 L10)).Splits :=
  S2598b_hsplit

/-- The three S2543 `f`-side hypotheses as a single conjunction. -/
theorem S2598b_hypotheses :
    S2577Away10FbarActual.f10'.Monic ∧
      (S2577Away10FbarActual.f10'.map
        (Ideal.Quotient.mk S2577Away10FbarActual.p10)).Separable ∧
      (S2577Away10FbarActual.f10'.map (algebraMap R10 L10)).Splits :=
  ⟨S2598b_hmonic, S2598b_hsep, S2598b_hsplit⟩

#check S2598b_hmonic
#check S2598b_hsep
#check S2598b_hsplit
#check fbar10_separable
#check f10'_map_L_splits
#check S2598b_hypotheses
#print axioms S2598b_hmonic
#print axioms S2598b_hsep
#print axioms S2598b_hsplit
#print axioms fbar10_separable
#print axioms f10'_map_L_splits
#print axioms S2598b_hypotheses

end LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual
end
