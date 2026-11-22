import LeanFormal.IUT.IUTII.Theta.ThetaLinkSourceCover

/-!
# L1-F8 ThetaLinkSourceCover consumer

Stage-2 consumer wrapper for the production categorical model of IUT I,
Example 3.2(v).  It records exactly the donor inputs and consumes
`thetaEquivalence`; it is a generic categorical statement, not a real-source
binding.
-/

open CategoryTheory

noncomputable section

namespace SHEAF.L1F8.ThetaLinkSourceCoverConsumer

universe u

open Iut.SourceSemiGraphOfAnabelioids.CovObject.ThetaLinkSourceCover

/-- The exact inputs of the donor `thetaEquivalence`: a source semigraph, a
root vertex, a connected tempered cover `Yddot`, a base-field model, explicit
product data, and the slice factorization hypothesis. -/
structure ThetaLinkSourceCoverConsumer where
  /-- The source semigraph of anabelioids. -/
  diagram : Iut.SourceSemiGraphOfAnabelioids.{u}
  /-- The chosen root vertex. -/
  root : diagram.base.Vertex
  /-- The distinguished connected tempered cover `Yddot_v`. -/
  Yddot : ConnectedTemperedCover diagram root
  /-- The base-field full subcategory model `B(K_v)^0`. -/
  model : BaseFieldCoverModel diagram root
  /-- Explicit product cones `Yddot_v × A`. -/
  data : ThetaProductData diagram root Yddot model
  /-- The base-field slice factorization hypothesis. -/
  factorization : SliceFactorization data

/-- The donor equivalence `D_v^⊢ ~→ D_v^Θ` for the supplied consumer data. -/
noncomputable def thetaLinkSourceCoverConsumer_equivalence
    (consumer : ThetaLinkSourceCoverConsumer.{u}) :
    BaseCover consumer.model ≌ ThetaCoverSubcategory consumer.data :=
  thetaEquivalence consumer.data consumer.factorization

end SHEAF.L1F8.ThetaLinkSourceCoverConsumer