import tmp.sheaf.xif.paper.S2439D9ProofActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2439D9ProofActual

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2440ProbeAdapted

universe v u v' u'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A]

example : Prop := (J.pseudofunctorOver A).IsStack J

example : Prop := (J.pseudofunctorOver A).IsPrestack J

example : Prop := (J.pseudofunctorOver A).IsStackFor (⊥ : Presieve (Classical.choice (inferInstance : Nonempty C)))

#check @LeanFormal.IUT.XiFPaper.S2134D9DescentActual.hasEffectiveDescent_iff_amalgam
#check @LeanFormal.IUT.XiFPaper.S2134D9DescentActual.HasEffectiveDescentPresieve
#check @Pseudofunctor.IsStack.of_isStackFor
#check @Pseudofunctor.isStackFor_iff
#check @Pseudofunctor.fullyFaithfulToDescentData
#check @Pseudofunctor.IsStackFor.essSurj
#check @Sieve.ofArrows_category'

end LeanFormal.IUT.XiFPaper.S2440ProbeAdapted

end
