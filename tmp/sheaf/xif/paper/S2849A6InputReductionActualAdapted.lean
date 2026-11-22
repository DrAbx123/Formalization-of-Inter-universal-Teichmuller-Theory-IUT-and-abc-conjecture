import tmp.sheaf.xif.paper.S2848A6CompletionConditionalActual
import tmp.sheaf.xif.paper.S2841A6PlaceSelectionActual
import tmp.sheaf.xif.paper.S2798StableEverywhere37Actual
import tmp.sheaf.xif.paper.S2840A6ClauseAActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual
open LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual
open LeanFormal.IUT.XiFPaper.S2798StableEverywhere37Actual
open LeanFormal.IUT.XiFPaper.S2840A6ClauseAActual
open LeanFormal.IUT.XiFPaper.S2839A6F6ClauseRestatementActual
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2849A6InputReductionActualAdapted

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF
local instance : Algebra GaussianField S2847A6.F :=
  inferInstanceAs (Algebra GaussianField S2847F6)

/-- The selected A6 place, with its F-type ascription. -/
noncomputable def S2841PlaceF : NumberField.FinitePlace S2847A6.F := S2841Place

theorem S2841PlaceF_residue :
    NumberFieldFinitePlace.residueCharacteristic S2841PlaceF = 37 := by
  simpa [S2841PlaceF] using S2841_residueCharacteristic

/-- The singleton bad set for the selected place. -/
def S2841BadSet : Set (NumberField.FinitePlace S2847A6.F) := {S2841PlaceF}

/-- Bridge from S2841PlaceSelection to the singleton set. -/
theorem S2849_badSet_eq
    (S : SourceSignQuotientData S2847A6)
    (hV : S.V_mod_bad = S2841PlaceSelection.V_mod_bad) :
    S.V_mod_bad = S2841BadSet := by
  rw [hV]
  ext q
  simp only [S2841PlaceSelection, S2841BadSet, S2841PlaceF,
    Set.mem_singleton_iff]

/-- If S's bad set is the selected 37-place, residue coprimality is actual. -/
theorem S2849_residueCoprime
    (S : SourceSignQuotientData S2847A6)
    (hV : S.V_mod_bad = S2841BadSet) :
    ∀ (p : NumberField.FinitePlace S2847A6.F),
      p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (NumberFieldFinitePlace.residueCharacteristic p) := by
  intro p hp
  rw [hV] at hp
  have hpEq : p = S2841PlaceF := by
    simpa [S2841BadSet, Set.mem_singleton_iff] using hp
  subst hpEq
  have hres : NumberFieldFinitePlace.residueCharacteristic S2841PlaceF = 37 :=
    S2841_residueCharacteristic
  rw [hres]
  norm_num [S2771FiveLabel]

/-- If S's bad set is the selected 37-place, multiplicative reduction at bad
places is actual, by S2798 at the contracted Gaussian place plus base change. -/
theorem S2849_multiplicative
    (S : SourceSignQuotientData S2847A6)
    (hV : S.V_mod_bad = S2841BadSet) :
    ∀ (p : NumberField.FinitePlace S2847A6.F),
      p ∈ S.V_mod_bad →
        S2847A6.curve.HasMultiplicativeReductionAt p := by
  intro p hp
  rw [hV] at hp
  have hpEq : p = S2841PlaceF := by
    simpa [S2841BadSet, Set.mem_singleton_iff] using hp
  subst hpEq
  let Pg : NumberField.FinitePlace GaussianField :=
    NumberFieldFinitePlace.comap (k := GaussianField) S2841PlaceF
  have hgRes : NumberFieldFinitePlace.residueCharacteristic
      (NumberFieldFinitePlace.comap (k := ℚ) Pg) = 37 := by
    rw [NumberFieldFinitePlace.residueCharacteristic_comap (k := ℚ) Pg]
    change NumberFieldFinitePlace.residueCharacteristic
      (NumberFieldFinitePlace.comap (k := GaussianField) S2841PlaceF) = 37
    rw [NumberFieldFinitePlace.residueCharacteristic_comap
      (k := GaussianField) S2841PlaceF]
    exact S2841PlaceF_residue
  have hG : E37QiPunctured.HasMultiplicativeReductionAt Pg :=
    S2798_multiplicative37 Pg hgRes
  have hbase := PuncturedEllipticCurve.hasMultiplicativeReductionAt_baseChange
    (X := E37QiPunctured) (K := S2847A6.F) (place := S2841PlaceF)
    (by simpa [Pg] using hG)
  unfold PuncturedEllipticCurve.HasMultiplicativeReductionAt at hbase ⊢
  simp only [NumberFieldFinitePlace.underlyingPrime] at hbase ⊢
  have hcurve : S2847A6.curve.curve = A6Curve.curve :=
    congrArg PuncturedEllipticCurve.curve S2840A6_curve_eq_zero
  rw [hcurve, S2840A6_curve_eq]
  exact hbase

#check S2849_residueCoprime
#check S2849_multiplicative
#print axioms S2849_residueCoprime
#print axioms S2849_multiplicative

end LeanFormal.IUT.XiFPaper.S2849A6InputReductionActualAdapted
end
