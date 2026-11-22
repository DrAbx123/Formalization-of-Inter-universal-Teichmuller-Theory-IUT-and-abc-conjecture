/- Route-valid P6 display terms from any accepted display source data. -/
import tmp.sheaf.xif.paper.Mzk1P6DisplayDictionaryActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6DisplayRouteRecordActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
variable (D : P6DisplaySourceData)
noncomputable def routeDisplayTerms : Thm110DisplayTerms := D.toTerms
theorem routeDisplayTerms_def : routeDisplayTerms D = D.toTerms := rfl
#print axioms routeDisplayTerms_def
end LeanFormal.IUT.XiFPaper.Mzk1P6DisplayRouteRecordActual
end
