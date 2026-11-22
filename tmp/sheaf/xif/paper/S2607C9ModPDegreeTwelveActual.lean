import tmp.sheaf.xif.paper.S2540Mod613CertificateActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S2540Mod613CertificateActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual

namespace LeanFormal.IUT.XiFPaper.S2607C9ModPDegreeTwelveActual

/-- The already actual degree-12 irreducible residue certificate at p = 613. -/
theorem S2607Mod613_irreducible :
    Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 613))) :=
  S2540ResidueCertificate

/-- The p = 613 reduction has degree 12. -/
theorem S2607Mod613_natDegree :
    (S2132Psi5Z.map (Int.castRingHom (ZMod 613))).natDegree = 12 := by
  rw [S2540F_eq_target]
  exact S2540F_natDegree

/-- Prop form of the still-missing p = 13 certificate: the reduction of the
actual integer model of psi_5 modulo 13 is irreducible of degree 12. -/
def S2607Mod13Certificate : Prop :=
  Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 13)))

/-- Prop form of the S2470 residue data at a prime of residue degree one. -/
def S2607ResidueDataAt (p : ℕ) : Prop :=
  Nonempty S2470ActualResidueData ∧ True

/-- Exact plan target: an actual prime of residue degree one whose fbar is the
p = 13 degree-twelve irreducible. -/
def S2607Mod13ResidueTarget : Prop :=
  S2607Mod13Certificate ∧ S2607ResidueDataAt 13

end LeanFormal.IUT.XiFPaper.S2607C9ModPDegreeTwelveActual

end