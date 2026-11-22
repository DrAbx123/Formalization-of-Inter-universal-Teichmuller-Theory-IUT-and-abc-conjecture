import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import tmp.sheaf.xif.paper.GlobalFrobenioidPresentationActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend

/-!
# Actual q-pilot arithmetic line-bundle object via the global ideal family

Source: IUT III, Definition 3.8, (i), pp. 112-113: the q-pilot object is the
object of the [global realified] Frobenioid determined by the q_v, v in V_bad.
IUT III, §3, p. 16 (iut3.txt lines 880-893): the q-pilot object is determined by
the arithmetic divisor given by the zero locus of the q_v, and its log-volume is
written -|log q|.  IUT III, p. 131, (Ob1) (iut3.txt lines 8017-8042): the
q-pilot object is determined by the arithmetic line bundle that arises locally
as an ideal, i.e. as an O_k-submodule of O_k^mdl; this arithmetic line bundle is
O(-D) for the zero-locus divisor D.

This file constructs, from the actual q_v zero-locus divisor with q_v
multiplicities (QPilotGlobalLogVolumeFromQActual.qVZeroLocusQEffectiveGlobal), the
actual global ideal family of the arithmetic line bundle O(-D_q) in the actual
global model Frobenioid presentation of Example 3.6(ii)
(GlobalFrobenioidPresentationActual):

* qPilotIdealFamily: finite exponents -mult_b at the actual base bad primes and
  zero archimedean coordinates, i.e. the value coordinates of O(-D_q);
* qPilotLineBundleObject: the actual object of the model Frobenioid given by
  objectOfIdealFamily of that global ideal family;
* qPilotLineBundleObject_divisorClass: the divisor class of this line-bundle
  object is exactly the Grothendieck class of the actual q_v zero-locus divisor
  D_q on the same input;
* qPilotLineBundleObject_logVolume_link: the log-volume of that object is
  qPilotQGlobalLogVolume = - sum_b |log q_v(b)|.

No inequality is asserted.  The identification of this ideal-family object with
the paper's procession-normalized rank-one arithmetic line bundle, with the (1,0)
q-pilot F^boxplus-triangleright-x-mu-prime-strip, and with the log-Kummer
representation on 1,circ U_Q remain exact missing objects (recorded separately
in S3133QPilotPaperMissingActual).  No toy/True/PUnit/axiom/sorry.
WRITE-ONLY; no local compile; queued.
-/

noncomputable section
open scoped BigOperators
open scoped NumberField
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotIdealFamilyObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open IsDedekindDomain NumberField

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The finite-place exponent coordinate of the q-pilot arithmetic line bundle
O(-D_q): the negative of the actual q_v zero-locus multiplicities, evaluated at
the actual base bad finite primes. -/
noncomputable def qPilotIdealFamilyFinite
    [Fintype (Bad (nativePlaceSelection X.S))] :
    HeightOneSpectrum (𝓞 (BaseField X)) →₀ ℤ :=
  -((qVZeroLocusQEffectiveGlobal X).1.mapRange
      (fun n : ℕ => (n : ℤ)) (by simp))

/-- The actual global ideal family of the q-pilot arithmetic line bundle O(-D_q):
it has value coordinates -mult_b at the actual base bad finite primes and zero
archimedean coordinates. -/
noncomputable def qPilotIdealFamily
    [Fintype (Bad (nativePlaceSelection X.S))] :
    GlobalIdealFamily (BaseField X) :=
  ⟨qPilotIdealFamilyFinite X, fun _ => 0⟩

/-- The archimedean coordinate of the actual q_v zero-locus divisor vanishes. -/
theorem qVZeroLocusQEffectiveGlobal_snd
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qVZeroLocusQEffectiveGlobal X).2 = 0 := by
  classical
  unfold qVZeroLocusQEffectiveGlobal
  induction (Finset.univ : Finset (Bad (nativePlaceSelection X.S)))
      using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Prod.snd_add, ih]
      simp [qVZeroLocusQEffectiveDivisor]

/-- The explicit divisor coordinates of the q-pilot ideal family are exactly the
coordinates of the actual q_v zero-locus divisor, up to the frozen sign
convention d(J) = -delta(J) of the model backend. -/
theorem qPilotIdealFamily_neg_eq_effectiveToExplicit
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (-(qPilotIdealFamily X).finite,
      fun w => -(qPilotIdealFamily X).infinite w) =
      effectiveToExplicit (qVZeroLocusQEffectiveGlobal X) := by
  apply Prod.ext
  · simp [qPilotIdealFamily, qPilotIdealFamilyFinite, effectiveToExplicit]
  · funext w
    have hzero := qVZeroLocusQEffectiveGlobal_snd X
    rw [effectiveToExplicit_snd_apply, hzero]
    simp [qPilotIdealFamily]

/-- The divisor class of the q-pilot ideal family: the Grothendieck class of the
actual q_v zero-locus divisor. -/
noncomputable def qPilotIdealFamilyDivisorClass
    [Fintype (Bad (nativePlaceSelection X.S))] :
    Algebra.GrothendieckAddGroup (EffectiveDivisor (BaseField X)) :=
  idealFamilyDivisorClass (qPilotIdealFamily X)

/-- The q-pilot ideal family class is exactly the class of the actual zero-locus
divisor D_q. -/
theorem qPilotIdealFamilyDivisorClass_eq
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotIdealFamilyDivisorClass X =
      Algebra.GrothendieckAddGroup.of (qVZeroLocusQEffectiveGlobal X) := by
  unfold qPilotIdealFamilyDivisorClass idealFamilyDivisorClass
  rw [qPilotIdealFamily_neg_eq_effectiveToExplicit X,
    ← coneGrothendieckEquiv_of (qVZeroLocusQEffectiveGlobal X)]
  exact AddEquiv.symm_apply_apply coneGrothendieckEquiv _

/-- The actual global q-pilot arithmetic line-bundle object O(-D_q) in the
actual global model Frobenioid presentation of IUT III Example 3.6(ii). -/
noncomputable def qPilotLineBundleObject
    [Fintype (Bad (nativePlaceSelection X.S))] :
    Iut.SourceModelFrobenioid.Object (presentationDivisorMonoid X) :=
  objectOfIdealFamily (qPilotIdealFamily X)

/-- The divisor class of the q-pilot line-bundle object is exactly the class of
the actual q_v zero-locus divisor D_q. -/
theorem qPilotLineBundleObject_divisorClass
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotLineBundleObject X).divisorClass =
      Algebra.GrothendieckAddGroup.of (qVZeroLocusQEffectiveGlobal X) := by
  unfold qPilotLineBundleObject objectOfIdealFamily
  change idealFamilyDivisorClass (qPilotIdealFamily X) =
    Algebra.GrothendieckAddGroup.of (qVZeroLocusQEffectiveGlobal X)
  exact qPilotIdealFamilyDivisorClass_eq X

/-- The line-bundle object and the actual q-pilot log-volume are read off the
same q_v zero-locus divisor: its divisor class is the D_q class and its
log-volume is - sum_b |log q_v(b)|. -/
theorem qPilotLineBundleObject_logVolume_link
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotLineBundleObject X).divisorClass =
        Algebra.GrothendieckAddGroup.of (qVZeroLocusQEffectiveGlobal X) ∧
      qPilotQGlobalLogVolume X =
        -∑ b : Bad (nativePlaceSelection X.S),
          localLogMagnitude (qVFamily X.S b) :=
  ⟨qPilotLineBundleObject_divisorClass X,
    qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude X⟩

end LeanFormal.IUT.XiFPaper.S3133QPilotIdealFamilyObjectActual
