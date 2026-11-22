import tmp.sheaf.xif.paper.PaperThetaPilotCarrierActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity

-- Paper Theta-pilot component image on F_l^x
--
-- Correct possible image: the theta value is placed at the j-th component and
-- the identity value 1 at every other component. This is not the old
-- constant/diagonal paperThetaPilotPointAt. No PaperLabelHullHaarComputed is
-- used. WRITE-ONLY; no local lake/lean.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotComponentImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual

universe u

variable {l : PrimeGeFive}

-- The q-pilot coordinate label: j = 1 in F_l^x.
abbrev qPilotLabel : PaperThetaPilotCarrier (l := l) :=
  (1 : (ZMod l.value)ˣ)

theorem paperLabelInt_one :
    paperLabelInt (l := l) (qPilotLabel (l := l)) = 1 := by
  unfold paperLabelInt qPilotLabel
  have hval : ((1 : (ZMod l.value)ˣ).val.val) = 1 := by
    simp
  rw [hval]
  have hstar : 1 ≤ lStar l.value := by
    have h2 : 2 ≤ lStar l.value := PrimeGeFive.lStar_ge_two l
    omega
  rw [if_pos hstar]
  norm_num

theorem paperGaussExponent_one :
    paperGaussExponent (l := l) (qPilotLabel (l := l)) = 1 := by
  unfold paperGaussExponent
  rw [paperLabelInt_one, gaussExponent_one_toNat]

theorem paperThetaValue_one (q : Real) :
    paperThetaValue (l := l) q (qPilotLabel (l := l)) = q := by
  unfold paperThetaValue
  rw [paperGaussExponent_one, pow_one]

-- The corrected component possible image: theta value at label j, identity
-- at every other label.
noncomputable def paperThetaPilotImageAt
    (q : Real) (j : PaperThetaPilotCarrier (l := l)) :
    PaperThetaPilotCarrier (l := l) → Multiplicative Real :=
  fun i => if i = j then
    Multiplicative.ofAdd (Real.log (paperThetaValue (l := l) q j))
  else 1

@[simp] theorem paperThetaPilotImageAt_self
    (q : Real) (j : PaperThetaPilotCarrier (l := l)) :
    paperThetaPilotImageAt (l := l) q j j =
      Multiplicative.ofAdd (Real.log (paperThetaValue (l := l) q j)) := by
  unfold paperThetaPilotImageAt
  simp

@[simp] theorem paperThetaPilotImageAt_other
    (q : Real) {i j : PaperThetaPilotCarrier (l := l)} (hij : i ≠ j) :
    paperThetaPilotImageAt (l := l) q j i = 1 := by
  unfold paperThetaPilotImageAt
  simp [hij]

-- At j = 1 and at the q-pilot coordinate, the component image is exactly
-- the q-pilot value element ofAdd(log q).
theorem paperThetaPilotImageAt_qPilot_self (q : Real) :
    paperThetaPilotImageAt (l := l) q (qPilotLabel (l := l))
        (qPilotLabel (l := l)) =
      Multiplicative.ofAdd (Real.log q) := by
  rw [paperThetaPilotImageAt_self, paperThetaValue_one]

-- At every other coordinate, the j = 1 image is the identity value 1.
theorem paperThetaPilotImageAt_qPilot_other (q : Real)
    {i : PaperThetaPilotCarrier (l := l)} (hi : i ≠ qPilotLabel (l := l)) :
    paperThetaPilotImageAt (l := l) q (qPilotLabel (l := l)) i = 1 := by
  exact paperThetaPilotImageAt_other (l := l) q hi

-- The full component possible-image set over all F_l^x labels.
noncomputable def paperThetaPilotComponentImageSet (q : Real) :
    Set (PaperThetaPilotCarrier (l := l) → Multiplicative Real) :=
  Set.range (paperThetaPilotImageAt (l := l) q)

theorem paperThetaPilotImageAt_mem (q : Real)
    (j : PaperThetaPilotCarrier (l := l)) :
    paperThetaPilotImageAt (l := l) q j ∈
      paperThetaPilotComponentImageSet (l := l) q :=
  ⟨j, rfl⟩

-- The j = 1 image is the q-pilot tuple: q at the q-pilot coordinate and 1
-- elsewhere.
theorem paperThetaPilotImageAt_one_eq_qPilotTuple (q : Real) :
    paperThetaPilotImageAt (l := l) q (qPilotLabel (l := l)) =
      fun i : PaperThetaPilotCarrier (l := l) =>
        if i = qPilotLabel (l := l) then
          Multiplicative.ofAdd (Real.log q)
        else 1 := by
  funext i
  by_cases hi : i = qPilotLabel (l := l)
  · rw [hi, paperThetaPilotImageAt_qPilot_self, hi]
    simp
  · rw [paperThetaPilotImageAt_qPilot_other (l := l) q hi, if_neg hi]

#check qPilotLabel
#check paperThetaValue_one
#check paperThetaPilotImageAt
#check paperThetaPilotImageAt_qPilot_self
#check paperThetaPilotImageAt_qPilot_other
#check paperThetaPilotComponentImageSet
#check paperThetaPilotImageAt_one_eq_qPilotTuple

end LeanFormal.IUT.XiFPaper.PaperThetaPilotComponentImageActual

end