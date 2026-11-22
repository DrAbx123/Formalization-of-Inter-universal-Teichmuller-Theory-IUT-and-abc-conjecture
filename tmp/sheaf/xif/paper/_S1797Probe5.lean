import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section
open scoped TensorProduct
namespace S1797Probe
variable {K : Type} [Field K]

-- test 1: haveI with Pi-type instances, then use dependent data elaborated under the originals
example {ι : Type} [Fintype ι] (Ai : ι → Type) (hF : ∀ i, Field (Ai i)) (hA : ∀ i, Algebra K (Ai i))
    (hFin : ∀ i, Module.Finite K (Ai i)) : Module.Finite K (∀ i, Ai i) := by
  haveI hF' : ∀ i, Field (Ai i) := hF
  haveI hA' : ∀ i, Algebra K (Ai i) := hA
  haveI hFin' : ∀ i, Module.Finite K (Ai i) := hFin
  infer_instance

-- test 2: use the original hypotheses directly as instances (obtain-style)
example {ι : Type} [Fintype ι] (Ai : ι → Type) (hF : ∀ i, Field (Ai i)) (hA : ∀ i, Algebra K (Ai i))
    (hFin : ∀ i, Module.Finite K (Ai i)) : Module.Finite K (∀ i, Ai i) := by
  letI hF'' : ∀ i, Field (Ai i) := hF
  letI hA'' : ∀ i, Algebra K (Ai i) := hA
  letI hFin'' : ∀ i, Module.Finite K (Ai i) := hFin
  infer_instance

-- test 3: with an existential that has explicit "_" instance binders
example {ι : Type} [Fintype ι] : True := by
  have key : ∃ (Ai : ι → Type) (_ : ∀ i, Field (Ai i)) (_ : ∀ i, Algebra K (Ai i))
      (_ : ∀ i, Module.Finite K (Ai i)), True := by
    obtain ⟨Ai, hF, hA, hFin⟩ : ∃ (Ai : ι → Type) (_ : ∀ i, Field (Ai i)) (_ : ∀ i, Algebra K (Ai i)),
        True := ⟨fun _ => K, fun _ => inferInstance, fun _ => inferInstance⟩
    exact ⟨Ai, hF, hA, fun _ => inferInstance, trivial⟩
  obtain ⟨Ai, hF, hA, hFin, _⟩ := key
  haveI : ∀ i, Field (Ai i) := hF
  haveI : ∀ i, Algebra K (Ai i) := hA
  haveI : ∀ i, Module.Finite K (Ai i) := hFin
  have : Module.Finite K (∀ i, Ai i) := inferInstance
  trivial

end S1797Probe
