import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeFinite

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

abbrev F := S1720Field
abbrev G := F ≃ₐ[ℚ] F

example : Finite G := inferInstance
example : Finite (F →ₐ[ℚ] F) := inferInstance

abbrev φ : G →* Equiv.Perm (S1687P.rootSet F) := MulAction.toPermHom G (S1687P.rootSet F)
abbrev K := φ.ker
example : Finite K := inferInstance

end ProbeFinite
