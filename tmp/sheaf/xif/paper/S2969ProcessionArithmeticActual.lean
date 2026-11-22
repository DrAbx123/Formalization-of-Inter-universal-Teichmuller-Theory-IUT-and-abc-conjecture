import tmp.sheaf.xif.paper.S2933PerTripleThetaCertificateActual
import tmp.sheaf.xif.paper.S2921HeightBridgeActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary

noncomputable section
open LeanFormal.IUT
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2969ProcessionArithmeticActual

open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual

/-- `collectionBound` at the actual S2921 candidates. -/
noncomputable def S2969CollectionBound (a b c n j : Nat) : Real :=
  collectionBound (2 * (n : Real) + 1) S2921D (S2921Q a b c)
    (S2921S a b c) (S2921T a b c) j

theorem S2969_collectionBound_expand (a b c n j : Nat) :
    S2969CollectionBound a b c n j =
      ((j : Real) + 1) * S2921D -
        (j : Real) ^ 2 / (2 * (2 * (n : Real) + 1)) * S2921Q a b c +
        S2921S a b c + 4 * ((j : Real) + 1) * S2921T a b c :=
  rfl

/-- The procession average at the actual S2921 candidates. -/
noncomputable def S2969ProcessionAverage (a b c n : Nat) : Real :=
  (1 / (n : Real)) * ∑ j ∈ Icc 1 n, S2969CollectionBound a b c n j

/-- Explicit simplified procession average (using IV `processionAverage_eq`). -/
theorem S2969_processionAverage_eq (a b c n : Nat) (hn : 1 <= n) :
    S2969ProcessionAverage a b c n =
      ((2 * (n : Real) + 1) + 5) / 4 * S2921D -
        ((2 * (n : Real) + 1) + 1) / 24 * S2921Q a b c +
        S2921S a b c + ((2 * (n : Real) + 1) + 5) * S2921T a b c := by
  unfold S2969ProcessionAverage S2969CollectionBound
  exact processionAverage_eq n hn S2921D (S2921Q a b c) (S2921S a b c) (S2921T a b c)

/-- The same average with `T = l * S` substituted and S collected. -/
theorem S2969_processionAverage_T_eq (a b c n : Nat) (hn : 1 <= n) :
    S2969ProcessionAverage a b c n =
      ((2 * (n : Real) + 1) + 5) / 4 * S2921D -
        ((2 * (n : Real) + 1) + 1) / 24 * S2921Q a b c +
        (1 + ((2 * (n : Real) + 1) + 5) *
          (S2771FiveLabel.value : Real)) * S2921S a b c := by
  rw [S2969_processionAverage_eq a b c n hn]
  unfold S2921T
  ring_nf

/-- The J-height upper bound `6 log c + log 256`. -/
noncomputable def S2969LogCUpper (c : Nat) : Real :=
  6 * Real.log (c : Real) + Real.log 256

theorem S2969_Jheight_le_logCUpper (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) <= S2969LogCUpper c := by
  have h := (abcJInvariant_logHeight_bounds_abcRationalPoint habc).2
  rw [abcRationalPoint_logHeight₁ habc] at h
  simpa [S2969LogCUpper] using h

/-- Difference between the theta upper expression and `6 log c + log 256`. -/
noncomputable def S2969ThetaMinusLogC (n a b c : Nat) : Real :=
  S2933ThetaUpper n a b c - S2969LogCUpper c

theorem S2969_thetaMinusLogC_expand (n a b c : Nat) :
    S2969ThetaMinusLogC n a b c =
      ((2 * (n : Real) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : Real) + 1)) * S2921D - S2921Q a b c / 6 +
          4 / (2 * (n : Real) + 1) * S2921S a b c +
          20 / 3 * S2921T a b c) -
        (6 * Real.log (c : Real) + Real.log 256) :=
  rfl

#check S2969CollectionBound
#check S2969_collectionBound_expand
#check S2969_processionAverage_eq
#check S2969_processionAverage_T_eq
#check S2969_Jheight_le_logCUpper
#check S2969_thetaMinusLogC_expand
#print axioms S2969_processionAverage_eq
#print axioms S2969_Jheight_le_logCUpper

end LeanFormal.IUT.XiFPaper.S2969ProcessionArithmeticActual
end
