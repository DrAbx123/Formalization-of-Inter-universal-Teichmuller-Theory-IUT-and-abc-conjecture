import tmp.sheaf.xif.paper.S2000D5Mod13CertificateActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1999S1993BridgeActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2001D5LargeImageSubstepsActual

open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2000D5Mod13CertificateActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2055DicksonClassActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual
open LeanFormal.IUT.XiFPaper.S1999S1993BridgeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual

/-- Formalized finite input (1): the mod-13 irreducible certificate for
`2^36 * psi_5`. -/
theorem S2001Mod13Certificate :
    Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 13))) := by
  exact S2000Psi5Z_mod13_irreducible

theorem S2001Mod13Certificate_degree :
    (S2132Psi5Z.map (Int.castRingHom (ZMod 13))).natDegree = 12 := by
  exact S2000Mod13Certificate_spec.2

/-- Formalized finite-group input (5): Dickson's transitive classification
for GL_2(F_5) on the twelve pairs, unconditional. -/
theorem S2001DicksonTransitiveClassification :
    S2009DicksonTransitiveClassification :=
  S2055DicksonTransitiveClassification

theorem S2001DicksonLargeImage (H : Subgroup GL2)
    (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (h102 : HasCycleType102 H) : H = ⊤ :=
  S2055LargeImage_of_dickson H hdet htrans h102

/-- Formalized input (1) in the exact form used by the S1987 proof: the
Galois-equivariant bijection between the twelve roots of prePsi_5 and the
twelve pairs {+P}. -/
theorem S2001RootPairEquiv : Nonempty (S2056Root ≃ S2056Pair) :=
  ⟨S2056RootPairEquiv⟩

theorem S2001RootPairEquiv_equivariant
    (σ : S2056K ≃ₐ[S1720Field] S2056K) (x : S2056Root) :
    S2056RootPairEquiv (S2056RootMap σ x) =
      S2056PairMap σ (S2056RootPairEquiv x) :=
  S2056RootPairEquiv_equivariant σ x

/-- Formalized part of (6): the splitting-field bridge and the S_3 Galois
group of S1687H. -/
theorem S2001S1687SplittingBridge : S1993SplittingFieldH_eq :=
  S1999SplittingFieldH_eq

theorem S2001Gal_S1687H :
    Nonempty (Polynomial.Gal S1687H ≃*
      Equiv.Perm (S1687P.rootSet S1993KP)) :=
  S1999Gal_S1687H

/-- The remaining exact gap for the l = 5 large-image target: the three
range hypotheses at one fixed actual rank-two basis. -/
def S2001RemainingRangeHypotheses
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2057RangeHypothesesData b

theorem S2001Target_of_rangeHypotheses
    (b : S1725TorsionBasis S1987Five)
    (D : S2001RemainingRangeHypotheses b) :
    S1987D5LargeImageFive :=
  s2057Target_of_rangeHypotheses b D

/-- The remaining gap is equivalent to the single-range-hypothesis package
at any actual basis. -/
theorem S2001Remaining_iff (b : S1725TorsionBasis S1987Five) :
    S2001RemainingRangeHypotheses b ↔ S2057RangeHypothesesData b := Iff.rfl

#check S2001Mod13Certificate
#check S2001DicksonTransitiveClassification
#check S2001RootPairEquiv
#check S2001Target_of_rangeHypotheses
#print axioms S2001Mod13Certificate
#print axioms S2001DicksonTransitiveClassification
#print axioms S2001RootPairEquiv
#print axioms S2001Target_of_rangeHypotheses
end LeanFormal.IUT.XiFPaper.S2001D5LargeImageSubstepsActual
end