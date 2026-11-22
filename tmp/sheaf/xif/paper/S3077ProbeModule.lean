import Mathlib
import tmp.sheaf.xif.paper.S3075PhiFixesKActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
namespace LeanFormal.IUT.XiFPaper.S3077Probe
abbrev K := S2844D6F6BaseChangeActual.K
abbrev M := Fin 2 →₀ ℕ
abbrev P := MvPolynomial (Fin 2) K
local instance : Field K := S2847A6.fieldF
#check (inferInstance : Algebra K K)
#check (inferInstance : Algebra K (AddMonoidAlgebra K M))
#check (inferInstance : Algebra K P)
#check AddMonoidAlgebra.algebra
#check Algebra.toModule
#check MvPolynomial.algebra
end LeanFormal.IUT.XiFPaper.S3077Probe
end
