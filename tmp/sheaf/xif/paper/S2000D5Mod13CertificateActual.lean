import tmp.sheaf.xif.paper.S2551Mod13IrreducibleActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2000D5Mod13CertificateActual

open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2550Mod13IrreducibleActual
open LeanFormal.IUT.XiFPaper.S2551Mod13IrreducibleActual

/-- The explicit reduction `F13` is the reduction of the integer model
`S2132Psi5Z = 2^36 * psi_5` of the S1987 report. -/
theorem S2000F13_eq_model :
    F13 = S2132Psi5Z.map (Int.castRingHom (ZMod 13)) := F13_eq_map

/-- **The mod-13 irreducibility certificate of the S1987 report, formalized.**
The reduction of the integer model `2^36 * psi_5` modulo 13 is irreducible
of degree twelve.  This is kernel-checked, with no sorry/axiom. -/
theorem S2000Psi5Z_mod13_irreducible :
    Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 13))) := by
  rw [← F13_eq_map]
  exact F13_irreducible

/-- The same certificate with the explicit degree-twelve polynomial `F13`. -/
theorem S2000F13_irreducible : Irreducible F13 := F13_irreducible

theorem S2000F13_natDegree : F13.natDegree = 12 := F13_natDegree

theorem S2000S2132Psi5Z_natDegree : S2132Psi5Z.natDegree = 12 := by
  unfold S2132Psi5Z
  compute_degree!

/-- The certificate is exactly the S1987 report's mod-13 finite input. -/
theorem S2000Mod13Certificate_spec :
    Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 13))) ∧
      (S2132Psi5Z.map (Int.castRingHom (ZMod 13))).natDegree = 12 := by
  refine ⟨S2000Psi5Z_mod13_irreducible, ?_⟩
  have hdeg : (S2132Psi5Z.map (Int.castRingHom (ZMod 13))).natDegree =
      F13.natDegree := by rw [← F13_eq_map]
  rw [hdeg, F13_natDegree]

#check S2000Psi5Z_mod13_irreducible
#check S2000Mod13Certificate_spec
#print axioms S2000Psi5Z_mod13_irreducible
#print axioms S2000Mod13Certificate_spec
end LeanFormal.IUT.XiFPaper.S2000D5Mod13CertificateActual
end