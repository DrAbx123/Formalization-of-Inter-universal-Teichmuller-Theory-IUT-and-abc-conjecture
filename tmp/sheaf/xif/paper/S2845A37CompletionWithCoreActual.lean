import tmp.sheaf.xif.paper.S2844A37ClauseBDerivationsActual
import tmp.sheaf.xif.paper.S2846A37GeometricCoreConditionalActual
import tmp.sheaf.xif.paper.S2843A37SourceCompletionConditionalActual
import tmp.sheaf.xif.paper.S2798StableEverywhere37Actual
import tmp.sheaf.xif.paper.S2823ClauseDConditionalActual
import tmp.sheaf.xif.paper.S2786PlaceBlockActual
import tmp.sheaf.xif.paper.S2786E37PrimeIdealsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2844A37ClauseBDerivationsActual
open LeanFormal.IUT.XiFPaper.S2846A37GeometricCoreConditionalActual
open LeanFormal.IUT.XiFPaper.S2843A37SourceCompletionConditionalActual
open LeanFormal.IUT.XiFPaper.S2842A37ClauseAssemblyConditionalActual
open LeanFormal.IUT.XiFPaper.S2836RebuildOnKernelArithmetic
open LeanFormal.IUT.XiFPaper.S2837PlaceSelectionArithmetic37Actual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2786E37PrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2836ClauseBCRebuildActual
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2798StableEverywhere37Actual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.XiFPaper.S2823ClauseDConditionalActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 16000000

local instance s2845GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2845A37CompletionWithCoreActual

noncomputable def S2845S
    (G : SourceSignQuotientGeometricCore arithmetic37) :
    SourceSignQuotientData arithmetic37 :=
  G.toSourceSignQuotientData S2837PlaceSelection

theorem S2845_hV
    (G : SourceSignQuotientGeometricCore arithmetic37) :
    (S2845S G).V_mod_bad = S2837PlaceSelection.V_mod_bad := rfl

theorem S2845_plus_residue :
    residueCharacteristic
      (S2786PlusPlace : NumberField.FinitePlace arithmetic37.Fmod) = 37 := by
  have h : (S2786PlusPlace : NumberField.FinitePlace arithmetic37.Fmod) =
      (gaussianField37PlusPlace : NumberField.FinitePlace arithmetic37.Fmod) := rfl
  rw [h]
  exact gaussianField37PlusPlace_residueCharacteristic

theorem S2845_minus_residue :
    residueCharacteristic
      (S2786MinusPlace : NumberField.FinitePlace arithmetic37.Fmod) = 37 := by
  have h : (S2786MinusPlace : NumberField.FinitePlace arithmetic37.Fmod) =
      (gaussianField37MinusPlace : NumberField.FinitePlace arithmetic37.Fmod) := rfl
  rw [h]
  exact gaussianField37MinusPlace_residueCharacteristic

theorem S2845_multiplicative
    (G : SourceSignQuotientGeometricCore arithmetic37) :
    forall (p : NumberField.FinitePlace arithmetic37.F),
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
        (S2845S G).V_mod_bad →
      arithmetic37.curve.HasMultiplicativeReductionAt p := by
  intro p hp
  have hmem : NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
      S2837PlaceSelection.V_mod_bad := by
    rw [← S2845_hV]
    exact hp
  have hset : NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
      ({S2786PlusPlace, S2786MinusPlace} :
        Set (NumberField.FinitePlace arithmetic37.Fmod)) := by
    rw [← S2837_V_mod_bad_eq]
    exact hmem
  have hdisj : NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p =
      (S2786PlusPlace : NumberField.FinitePlace arithmetic37.Fmod) ∨
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p =
        (S2786MinusPlace : NumberField.FinitePlace arithmetic37.Fmod) := by
    have hset' : NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
        ({(S2786PlusPlace : NumberField.FinitePlace arithmetic37.Fmod),
          (S2786MinusPlace : NumberField.FinitePlace arithmetic37.Fmod)} :
            Set (NumberField.FinitePlace arithmetic37.Fmod)) := hset
    rcases Set.mem_insert_iff.mp hset' with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)
  have hres : residueCharacteristic
      (NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p) = 37 := by
    rcases hdisj with h | h
    · rw [h]; exact S2845_plus_residue
    · rw [h]; exact S2845_minus_residue
  have hrat : residueCharacteristic
      (NumberFieldFinitePlace.comap (k := ℚ) p) = 37 := by
    rw [NumberFieldFinitePlace.residueCharacteristic_comap (k := ℚ)]
    rw [← NumberFieldFinitePlace.residueCharacteristic_comap
      (k := arithmetic37.Fmod) p]
    exact hres
  have h := S2798_multiplicative37 p hrat
  unfold PuncturedEllipticCurve.HasMultiplicativeReductionAt at h ⊢
  simp only [NumberFieldFinitePlace.underlyingPrime] at h ⊢
  rw [S2836Curve_eq] at h
  exact h

theorem S2845_residue
    (G : SourceSignQuotientGeometricCore arithmetic37) :
    forall (p : NumberField.FinitePlace arithmetic37.F),
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
        (S2845S G).V_mod_bad →
      Nat.Coprime S2771FiveLabel.value
        (residueCharacteristic
          (NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p)) := by
  intro p hp
  have hmem : NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
      S2837PlaceSelection.V_mod_bad := by
    rw [← S2845_hV]
    exact hp
  have hset : NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
      ({S2786PlusPlace, S2786MinusPlace} :
        Set (NumberField.FinitePlace arithmetic37.Fmod)) := by
    rw [← S2837_V_mod_bad_eq]
    exact hmem
  have hdisj : NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p =
      (S2786PlusPlace : NumberField.FinitePlace arithmetic37.Fmod) ∨
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p =
        (S2786MinusPlace : NumberField.FinitePlace arithmetic37.Fmod) := by
    have hset' : NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
        ({(S2786PlusPlace : NumberField.FinitePlace arithmetic37.Fmod),
          (S2786MinusPlace : NumberField.FinitePlace arithmetic37.Fmod)} :
            Set (NumberField.FinitePlace arithmetic37.Fmod)) := hset
    rcases Set.mem_insert_iff.mp hset' with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)
  rcases hdisj with h | h
  · rw [h]
    change Nat.Coprime S2771FiveLabel.value
      (residueCharacteristic
        (S2786PlusPlace : NumberField.FinitePlace arithmetic37.Fmod))
    rw [S2845_plus_residue]
    norm_num [S2771FiveLabel]
  · rw [h]
    change Nat.Coprime S2771FiveLabel.value
      (residueCharacteristic
        (S2786MinusPlace : NumberField.FinitePlace arithmetic37.Fmod))
    rw [S2845_minus_residue]
    norm_num [S2771FiveLabel]

noncomputable def S2845_qWitness
    (G : SourceSignQuotientGeometricCore arithmetic37)
    (hreal : forall (p : NumberField.FinitePlace arithmetic37.F),
      CurveIndexedTateUniformization arithmetic37.curve p (S2844Candidate p)) :
    forall (p : NumberField.FinitePlace arithmetic37.F),
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
        (S2845S G).V_mod_bad →
      Nonempty (SourceTateComparisonWitness arithmetic37 p) :=
  S2844_qWitness (S2845S G) hreal

noncomputable def S2845ClauseB
    (G : SourceSignQuotientGeometricCore arithmetic37)
    (hreal : forall (p : NumberField.FinitePlace arithmetic37.F),
      CurveIndexedTateUniformization arithmetic37.curve p (S2844Candidate p)) :
    SourceClauseB arithmetic37 (S2845S G) (S2836ClauseA (S2845S G)) :=
  S2842ClauseB (S2845S G) (S2845_multiplicative G) (S2845_qWitness G hreal)
    (S2845_residue G)

#check S2845S
#check S2845_hV
#check S2845_multiplicative
#check S2845_residue
#check S2845ClauseB
#print axioms S2845_multiplicative
#print axioms S2845_residue
#print axioms S2845ClauseB

noncomputable def S2845Completion
    (G : SourceSignQuotientGeometricCore arithmetic37)
    (hreal : forall (p : NumberField.FinitePlace arithmetic37.F),
      CurveIndexedTateUniformization arithmetic37.curve p (S2844Candidate p))
    (torsion23Rational : arithmetic37.curve.Torsion23Rational)
    (hSerre : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      arithmetic37.curve S2771FiveLabel)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := arithmetic37) (S := S2845S G))
    (localFamily : SourceClauseELocalFamilyUnit arithmetic37 (S2845S G)
      (S2836ClauseA (S2845S G))
      (S2845ClauseB G hreal)
      (S2842ClauseC (S2845S G) (S2845_multiplicative G)
        (S2845_qWitness G hreal) (S2845_residue G)
        torsion23Rational hSerre)
      (S2842ClauseD (S2845S G) (S2845_multiplicative G)
        (S2845_qWitness G hreal) (S2845_residue G)
        torsion23Rational hSerre kSide))
    (boundary : SourceClauseFBoundaryUnit arithmetic37 (S2845S G)
      (S2836ClauseA (S2845S G))
      (S2845ClauseB G hreal)
      (S2842ClauseC (S2845S G) (S2845_multiplicative G)
        (S2845_qWitness G hreal) (S2845_residue G)
        torsion23Rational hSerre)
      (S2842ClauseD (S2845S G) (S2845_multiplicative G)
        (S2845_qWitness G hreal) (S2845_residue G)
        torsion23Rational hSerre kSide)
      (S2842ClauseE (S2845S G) (S2845_multiplicative G)
        (S2845_qWitness G hreal) (S2845_residue G)
        torsion23Rational hSerre kSide localFamily)) :
    SourceCompletion S2771FiveLabel :=
  S2843Completion (S := S2845S G)
    (S2845_multiplicative G) (S2845_qWitness G hreal) (S2845_residue G)
    torsion23Rational hSerre kSide localFamily boundary

#check S2845Completion
#print axioms S2845Completion

end LeanFormal.IUT.XiFPaper.S2845A37CompletionWithCoreActual
end
