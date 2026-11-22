import tmp.sheaf.xif.paper.S3119InfinityValuationActual
import Mathlib.RingTheory.Localization.FractionRing
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119InfinityValuationActual
open LeanFormal.IUT.XiFPaper.S3128CoordinateRingTransferActual
namespace LeanFormal.IUT.XiFPaper.S3119OrdFracActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
variable {l : PrimeGeFive}

noncomputable def S3119OrdFrac (l : PrimeGeFive)
    (z : FractionRing (S1348CoordinateRing l)) : WithTop ℤ := by
  classical
  by_cases hz : z = 0
  · exact ⊤
  · let x : S1348CoordinateRing l := Classical.choose (IsFractionRing.div_surjective (S1348CoordinateRing l) z)
    let y : S1348CoordinateRing l := Classical.choose (Classical.choose_spec (IsFractionRing.div_surjective (S1348CoordinateRing l) z))
    exact match S3119InfinityOrdTop l x, S3119InfinityOrdTop l y with
      | some a, some b => some (a - b)
      | _, _ => ⊤

lemma S3119InfinityOrdTop_ne_top (l : PrimeGeFive)
    (z : S1348CoordinateRing l) (hz : z ≠ 0) :
    S3119InfinityOrdTop l z ≠ ⊤ := by
  simp [S3119InfinityOrdTop, hz]

lemma S3119OrdFrac_eq (l : PrimeGeFive)
    (z : FractionRing (S1348CoordinateRing l)) (hz : z ≠ 0) :
    S3119OrdFrac l z =
      (match S3119InfinityOrdTop l
          (Classical.choose (IsFractionRing.div_surjective (S1348CoordinateRing l) z)),
        S3119InfinityOrdTop l
          (Classical.choose (Classical.choose_spec
            (IsFractionRing.div_surjective (S1348CoordinateRing l) z))) with
      | some a, some b => some (a - b)
      | _, _ => ⊤) := by
  simp [S3119OrdFrac, hz]

def S3119OrdFracMkTarget (l : PrimeGeFive) : Prop :=
  ∀ (a b : S1348CoordinateRing l)
    (hb : b ∈ nonZeroDivisors (S1348CoordinateRing l)),
      S3119OrdFrac l
        (IsLocalization.mk' (FractionRing (S1348CoordinateRing l)) a ⟨b, hb⟩) =
        some (S3119InfinityOrd l a - S3119InfinityOrd l b)

#check S3119OrdFracMkTarget
#check S3119OrdFrac_eq
#check S3119InfinityOrdTop_ne_top
#print axioms S3119InfinityOrdTop_ne_top
#check S3119OrdFrac
end LeanFormal.IUT.XiFPaper.S3119OrdFracActual
end
