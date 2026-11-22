import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
/-! RootBaseCompletionGap: exact relation between the qVFam F-completion and the
chosen K-place completion, plus the degree-factor obstruction for the naive
degree identity `[F_w:Qp] = [K_w:Fmod_v]`.

The two completions live over **different global fields** (F vs K).  We prove
they have the same rational prime; the naive equality of Qp-degrees is reduced
to the completion tower factor `[K_w:F_w]`, and is false whenever that factor
is greater than one.  No degree identity is assumed. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1RootBaseCompletionGapActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
/-- The qVFam tensor place is exactly the F-place obtained from the native lift. -/
theorem qVFamTensorPlace_eq_nativeBadToFPlace :
    qVFamTensorPlace T b = nativeBadToFPlace T b := rfl
/-- The qVFam F-place and the chosen K-place have the same rational prime. -/
theorem completionRationalPrime_nativeBadToKPlace_eq_qVFamTensorP :
    (completionRationalPrime (nativeBadToKPlace T b)).val = qVFamTensorP T b := by
  have hK := completionRationalPrime_comap (k := T.arithmetic.Fmod)
    (K := T.arithmetic.K) (nativeBadToKPlace T b)
  rw [nativeBadToKPlace_comap T b] at hK
  have hF := completionRationalPrime_comap (k := T.arithmetic.Fmod)
    (K := T.arithmetic.F) (nativeBadToFPlace T b)
  rw [nativeBadToFPlace_comap T b] at hF
  have hprime : completionRationalPrime (nativeBadToKPlace T b) =
      completionRationalPrime (nativeBadToFPlace T b) := hK.symm.trans hF
  unfold qVFamTensorP
  rw [qVFamTensorPlace_eq_nativeBadToFPlace]
  exact congrArg (fun q : Nat.Primes => q.1) hprime
/-- Qp-degree of the actual F-completion (rootBase). -/
noncomputable def rootBaseQpDegree : Nat :=
  Module.finrank ℚ_[qVFamTensorP T b] (rootBase T b)
/-- Qp-degree of the chosen K-place completion. -/
noncomputable def kPlaceQpDegree : Nat :=
  Module.finrank ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]
    (NormalizedCompletion (nativeBadToKPlace T b))
/-- Naive target degree identity. -/
def RootBaseDegreeIdentity : Prop := rootBaseQpDegree T b = kPlaceQpDegree T b
/-- Exact degree-factor obstruction: if the K-place completion has an
F-completion subfield factor `b = [K_w:F_w] > 1` and the tower degree is
`c = b * a`, then the naive identity `a = c` is false. -/
theorem rootBaseDegreeIdentity_false_of_relativeDegree
    (A B C : Nat) (ha : 0 < A) (hb : 1 < B)
    (hbase : rootBaseQpDegree T b = A)
    (hk : kPlaceQpDegree T b = C)
    (htower : C = B * A) :
    ¬ RootBaseDegreeIdentity T b := by
  unfold RootBaseDegreeIdentity
  rw [hbase, hk, htower]
  intro hid
  have hgt : A < B * A := by
    have hB : 2 ≤ B := by omega
    have hmul : 2 * A ≤ B * A := Nat.mul_le_mul_right A hB
    have h2A : A < 2 * A := by omega
    omega
  omega
/-- Conditional form: the naive identity forces the relative factor to be
one in the tower model. -/
theorem rootBaseDegreeIdentity_forces_relativeFactor_one
    (A B C : Nat) (ha : 0 < A)
    (hbase : rootBaseQpDegree T b = A)
    (hk : kPlaceQpDegree T b = C)
    (htower : C = B * A)
    (hid : RootBaseDegreeIdentity T b) :
    B = 1 := by
  unfold RootBaseDegreeIdentity at hid
  rw [hbase, hk, htower] at hid
  have hcomm : B * A = 1 * A := by rw [one_mul]; exact hid.symm
  exact Nat.mul_right_cancel ha hcomm
end LeanFormal.IUT.XiFPaper.Mzk1RootBaseCompletionGapActual
end