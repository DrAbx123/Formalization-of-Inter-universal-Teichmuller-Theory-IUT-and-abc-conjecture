import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut

#check @Bicategory.whiskerRightIso
#check @Bicategory.whiskerLeftIso
#check @Bicategory.whiskerRight_comp
#check @Bicategory.comp_whiskerRight
#check @Bicategory.whisker_exchange
#check @Bicategory.associator
#check @Bicategory.whisker_assoc
#check @Bicategory.pentagon
#check @Bicategory.triangle
#print EtalePseudofunctorSquare.Cone
#print EtalePseudofunctorSquare.ConeMorphism
#print EtalePseudofunctorSquare.TwoPullbackWitness
#check @EtalePseudofunctorSquare
#check @Pseudofunctor.StrongTrans.vcomp
#check @Pseudofunctor.StrongTrans.whiskerRight
#check @Cat.ext
#check @Discrete.functor_ext
