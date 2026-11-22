import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S2650FiveDivisionEmbeddingActual

open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open Polynomial

/-- An embedding of the actual five-division field into the algebraic closure of F'. -/
noncomputable def S2650Embedding :
    S2057FiveDivisionField →ₐ[S1720Field] AlgebraicClosure S1720Field :=
  IsAlgClosed.lift

theorem S2650Embedding_injective : Function.Injective S2650Embedding :=
  S2650Embedding.injective

end LeanFormal.IUT.XiFPaper.S2650FiveDivisionEmbeddingActual
