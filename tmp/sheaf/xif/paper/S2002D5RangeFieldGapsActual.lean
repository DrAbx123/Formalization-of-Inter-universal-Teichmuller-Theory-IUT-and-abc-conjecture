import tmp.sheaf.xif.paper.S2000D5Mod13CertificateActual
import tmp.sheaf.xif.paper.S2001D5LargeImageSubstepsActual
import tmp.sheaf.xif.paper.S2465D5OrbitSizeActual
import tmp.sheaf.xif.paper.S2492Mod29FactorizationActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2203D5RangeActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2002D5RangeFieldGapsActual

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2000D5Mod13CertificateActual
open LeanFormal.IUT.XiFPaper.S2001D5LargeImageSubstepsActual
open LeanFormal.IUT.XiFPaper.S2465D5OrbitSizeActual
open LeanFormal.IUT.XiFPaper.S2492Mod29FactorizationActual
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2055DicksonClassActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

/-- Actual finite input: mod 13 irreducibility. -/
theorem S2002Mod13Certificate :
    Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 13))) :=
  S2000Psi5Z_mod13_irreducible

/-- Actual mod 29 factorization degree multiset. -/
theorem S2002Mod29FactorDegrees :
    factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) =
      ({2, 10} : Multiset ℕ) :=
  S2491FactorDegrees

/-- Actual corrected Dedekind--Frobenius orbit-size theorem. -/
theorem S2002DedekindOrbitSizeTheorem :
    DedekindFrobeniusOrbitSizeTheorem :=
  s2465DedekindFrobeniusOrbitSizeTheorem

/-- Actual root-to-pair bijection for the twelve roots of psi_5. -/
theorem S2002RootPairEquiv : Nonempty (S2056Root ≃ S2056Pair) :=
  ⟨S2056RootPairEquiv⟩

/-- Exact first gap for pair transitivity: the root/division-field to
matrix-range transport. -/
def S2002PairTransitiveRemaining : Prop := S2470Target

def S2002ResidueCertificateRemaining : Prop := S2470ResidueCertificateRequired

def S2002TransportRemaining : Prop := S2470RootToRangeTransport

theorem S2002PairTransitive_of_residueData_transport
    (D : S2470ActualResidueData) (h : S2002TransportRemaining) :
    S2002PairTransitiveRemaining :=
  S2470Target_of_residueData_and_transport D h

/-- Exact first gap for cycle type (10,2): the same transport, plus the
mod-29 residue data. -/
def S2002CycleTypeRemaining : Prop := S2203RangeCycleTypeRequired S1982Basis

theorem S2002PairTransitive_of_certificate_transport
    (hcert : S2002ResidueCertificateRemaining) (h : S2002TransportRemaining) :
    S2002PairTransitiveRemaining :=
  S2470Target_of_certificate_and_transport hcert h

/-- Conditional consumer: pair transitivity plus cycle type gives the D5
large-image target. -/
theorem S2002D5LargeImageFive_of_pair_cycle
    (hpair : S2002PairTransitiveRemaining) (hcycle : S2002CycleTypeRemaining) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle hpair

/-- Exact first gap for determinant surjectivity: no Weil-pairing/
cyclotomic-character interface is currently formalized. -/
def S2002DetSurjectiveRemaining : Prop :=
  DetSurjectiveOn
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range

#check S2002Mod13Certificate
#check S2002Mod29FactorDegrees
#check S2002DedekindOrbitSizeTheorem
#check S2002PairTransitive_of_residueData_transport
#check S2002D5LargeImageFive_of_pair_cycle
#print axioms S2002Mod13Certificate
#print axioms S2002Mod29FactorDegrees
#print axioms S2002DedekindOrbitSizeTheorem
#print axioms S2002D5LargeImageFive_of_pair_cycle
end LeanFormal.IUT.XiFPaper.S2002D5RangeFieldGapsActual
end