import tmp.sheaf.xif.paper.S1896BoundaryCuspActual
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual
noncomputable section
variable (F : Type) [Field F] (X : Iut.EtaleStackOverField F)
#check S1896IdentityBaseChange
example (S : Scheme) : IsFinite (𝟙 S) := inferInstance
example (S : Scheme) : Etale (𝟙 S) := inferInstance
