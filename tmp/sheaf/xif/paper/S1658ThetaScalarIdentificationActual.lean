import tmp.sheaf.xif.paper.S1639ThetaScalarActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1658ThetaScalarIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.S1632ThetaValueComparisonActual
open LeanFormal.IUT.XiFPaper.S1639ThetaScalarActual
open LeanFormal.IUT.Theorem311Source

universe v
variable {l : PrimeGeFive}
variable {V : Type v}
variable (I : OriginalInput l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Exact first missing source identification: the source theta q at the point
(0,0) equals the native base q product over the bad places. -/
def S1658SourceQEqProduct : Prop :=
  (I.theaterAt 0 0).thetaPacket.q = baseQProduct T

/-- The all-point source q identification (the form needed for all n,m). -/
def S1658SourceQEqProductAll : Prop :=
  ∀ n m : Int, (I.theaterAt n m).thetaPacket.q = baseQProduct T

/-- Conditional: the source q = base product gives normalization 1. -/
theorem s1658Normalization_eq_one_of_sourceQEq
    (h : S1658SourceQEqProductAll I T) (n m : Int)
    (j : SignedLabel l.value) :
    thetaNormalization I T n m j = 1 := by
  unfold thetaNormalization
  rw [h n m, div_self (baseQProduct_ne_zero T), one_pow]

/-- Conditional: the source q = base product gives the exact scalar
identification at every label. -/
theorem s1658ThetaScalarIdentification_of_sourceQEq
    (h : S1658SourceQEqProductAll I T) (n m : Int)
    (j : SignedLabel l.value) :
    ThetaScalarIdentification I T n m j := by
  unfold ThetaScalarIdentification
  rw [sourceThetaSectionValue_eq_q_pow I n m j,
    thetaScalarProduct_eq_baseQProduct_pow T j, h n m]

/-- Conditional: the exact source q = base product identification yields the
all-label scalar identification. -/
theorem s1658ThetaScalarIdentificationAll_of_sourceQEq
    (h : S1658SourceQEqProductAll I T) (n m : Int) :
    ThetaScalarIdentificationAll I T n m := by
  intro j
  unfold ThetaScalarIdentification
  rw [sourceThetaSectionValue_eq_q_pow I n m j,
    thetaScalarProduct_eq_baseQProduct_pow T j]
  exact congrArg (fun q => q ^ (gaussExponent j.1).toNat) (h n m)

/-- Exact equivalence of the desired normalized comparison at a nonzero label
with the source q/product equality. -/
theorem s1658Normalization_eq_one_iff_sourceQEq
    {n m : Int} {j : SignedLabel l.value} (hj : (gaussExponent j.1).toNat ≠ 0) :
    thetaNormalization I T n m j = 1 ↔
      (I.theaterAt n m).thetaPacket.q = baseQProduct T := by
  unfold thetaNormalization
  have hqpos : 0 < (I.theaterAt n m).thetaPacket.q := 
    (I.theaterAt n m).thetaPacket.q_pos
  have hprodpos : 0 < baseQProduct T := baseQProduct_pos T
  have hratio_pos : 0 < (I.theaterAt n m).thetaPacket.q / baseQProduct T :=
    div_pos hqpos hprodpos
  constructor
  · intro hpow
    have hlog : Real.log
        (((I.theaterAt n m).thetaPacket.q / baseQProduct T) ^
          (gaussExponent j.1).toNat) = 0 :=
      by rw [hpow, Real.log_one]
    rw [Real.log_pow] at hlog
    have hlogratio : Real.log
        ((I.theaterAt n m).thetaPacket.q / baseQProduct T) = 0 :=
      by
        rcases mul_eq_zero.mp hlog with hz | hz
        · have hn : (gaussExponent j.1).toNat = 0 := by exact_mod_cast hz
          exact (hj hn).elim
        · exact hz
    rcases Real.log_eq_zero.mp hlogratio with h0 | h1 | hneg
    · linarith
    · exact (div_eq_one_iff_eq (ne_of_gt hprodpos)).mp h1
    · linarith
  · intro hq
    rw [hq, div_self (ne_of_gt hprodpos), one_pow]

end LeanFormal.IUT.XiFPaper.S1658ThetaScalarIdentificationActual

end
