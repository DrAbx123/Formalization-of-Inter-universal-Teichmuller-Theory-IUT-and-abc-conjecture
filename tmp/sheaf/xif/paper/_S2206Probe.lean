import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Iut.Foundations.Orbicurve
open CategoryTheory Opposite Limits
noncomputable section
namespace P2206
variable {C : Type} [Category C] (J : GrothendieckTopology C)
noncomputable def terminalSheaf : Sheaf J (Type) :=
  ⟨(Functor.const Cᵒᵖ).obj PUnit,
    Presheaf.isSheaf_of_isTerminal J Limits.Types.isTerminalPUnit⟩
noncomputable def coproductSheaf : Sheaf J (Type) :=
  ∐ (fun _ : Iut.SignGroup => terminalSheaf J)
end P2206
end
