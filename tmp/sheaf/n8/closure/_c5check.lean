import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C4Actual
universe ua uv upi umon ui uL uG
variable {l : PrimeGeFive} {V0 : Type uv} {LAdd : Type uG} [AddGroup LAdd]
variable {I : OriginalInput.{ua,uv,upi,umon,ui} l V0}
variable {C1 : SourceInputBinding I}
variable {C2 : SourceLogKummerData I C1}
variable {C3 : SourcePilotRegionData (l:=l) (V:=V0) I}
variable {C4 : SourceWitnessedOutputData (l:=l) (V:=V0) I (Multiplicative LAdd)}
#check (fun (C5 : LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility.SourceAlgorithmCompatibilityData (LAdd:=LAdd) I C1 C2 C3 C4) => C5)
