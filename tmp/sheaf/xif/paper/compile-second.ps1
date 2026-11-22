$ErrorActionPreference="Continue"
Set-Location "D:\lean"
$files=@(
"QPilotIdentificationActual",
"ThetaHullIdentificationActual",
"SignedHullNormalizationActual",
"DeterminantLogVolumeActual",
"ThetaLinkLogKummerActual",
"SHEOutputActual",
"PaperXiFUnconditional",
"PaperXiFAssemblyActual"
)
$log="tmp/sheaf/xif/paper/compile-second.log"
Remove-Item -ErrorAction SilentlyContinue $log
$fail=0
foreach($f in $files){
 $src="tmp/sheaf/xif/paper/$f.lean"
 $olean=".lake/build/lib/lean/tmp/sheaf/xif/paper/$f.olean"
 New-Item -ItemType Directory -Force -Path (Split-Path $olean) | Out-Null
 $out=& lake env lean -j1 -R "D:\lean" -o $olean $src 2>&1
 $code=$LASTEXITCODE
 Add-Content $log "=== $f EXIT $code"
 if($out){Add-Content $log ($out|Out-String)}
 if($code -ne 0){$fail++}
}
Add-Content $log "FAIL_COUNT $fail"
Get-Content $log
exit $fail
