import tmp.sheaf.xif.paper.S3127G3FullActual
import Mathlib.CategoryTheory.Limits.Shapes.BinaryCofan
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G3FullActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G3ConsumerActual
variable {l : PrimeGeFive}

structure S3127G3ConsumerData
    {X Y : S3127FiniteEtaleOverKFull l} (i : X ⟶ Y) [Mono i] : Type where
  Z : S3127FiniteEtaleOverKFull l
  u : Z ⟶ Y
  colimit : IsColimit (BinaryCofan.mk i u)

noncomputable def S3127G3ConsumerData.of
    {X Y : S3127FiniteEtaleOverKFull l} (i : X ⟶ Y) [Mono i] :
    S3127G3ConsumerData i := by
  rcases S3127G3_full (l := l) i with ⟨Z, u, hne⟩
  rcases hne with ⟨h⟩
  exact ⟨Z, u, h⟩

theorem S3127G3Consumer_exists
    {X Y : S3127FiniteEtaleOverKFull l} (i : X ⟶ Y) [Mono i] :
    ∃ Z u, Nonempty (IsColimit (BinaryCofan.mk i u)) :=
  S3127G3_full (l := l) i

#check S3127G3ConsumerData
#check S3127G3ConsumerData.of
#check S3127G3Consumer_exists
end LeanFormal.IUT.XiFPaper.S3127G3ConsumerActual
end
