import tmp.sheaf.xif.paper.S1964QuotientCFActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual

namespace Scratch

abbrev paperCF : Iut.OrbicurveSignature := S1964HonestQuotientSignature
abbrev paperLabelCF : Iut.OrbicurveSignature := sourceTypeOneOnePlusMinus

theorem coarseCF_ne_paperCF :
    S1964CoarseQuotientSignature ≠ paperCF := by
  intro h
  have hs : S1964CoarseQuotientSignature.stackyOrders =
      paperCF.stackyOrders :=
    congrArg Iut.OrbicurveSignature.stackyOrders h
  rw [show S1964CoarseQuotientSignature.stackyOrders = [] from rfl,
    show (S1964HonestQuotientSignature).stackyOrders = [2, 2, 2] from rfl] at hs
  have hlen := congrArg List.length hs
  simp at hlen

def toIutSignature (s : SourceOrbicurveSignature) : Iut.OrbicurveSignature where
  genus := s.genus
  stackyOrders := s.stackyOrders
  punctures := s.punctures
  stackyOrders_ge_two := s.stackyOrders_ge_two

theorem legacyTypeOneLTorsion_ne_honestXKTors (l : PrimeGeFive) :
    toIutSignature (SourceOrbicurveSignature.typeOneLTorsion l) ≠
      (⟨1, [], l.value, by simp⟩ : Iut.OrbicurveSignature) := by
  intro h
  have hp := congrArg Iut.OrbicurveSignature.punctures h
  rw [show (toIutSignature (SourceOrbicurveSignature.typeOneLTorsion l)).punctures = 0 from rfl,
    show (show Iut.OrbicurveSignature from ⟨1, [], l.value, by simp⟩).punctures = l.value from rfl] at hp
  have h5 := l.ge_five
  omega

theorem sourceSignQuotientData_xK_ne_oncePunctured
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.xK.signature ≠ Iut.OrbicurveSignature.oncePuncturedElliptic := by
  intro h
  have hs := congrArg Iut.OrbicurveSignature.stackyOrders h
  rw [SourceSignQuotientData.xK_signature S,
    show (sourceTypeOneLTorsion l).stackyOrders = [l.value] from rfl,
    show Iut.OrbicurveSignature.oncePuncturedElliptic.stackyOrders = [] from rfl]
    at hs
  simp at hs

theorem sourceSignQuotientData_cK_ne_paperCF
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) : S.cK.signature ≠ paperCF := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  rw [SourceSignQuotientData.cK_signature S,
    show (sourceTypeOneLTorsionPlusMinus l).genus = 1 from rfl,
    show (S1964HonestQuotientSignature).genus = 0 from rfl] at hg
  exact Nat.one_ne_zero hg

end Scratch
