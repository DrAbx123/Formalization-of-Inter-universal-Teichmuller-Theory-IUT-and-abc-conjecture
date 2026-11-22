# Unified paper-level xi-f compile gate (emits oleans so later imports work).
$ErrorActionPreference = "Continue"
Set-Location "D:\lean"
$files = @(
  "tmp/sheaf/xif/paper/PaperXiFSpec.lean",
  "tmp/sheaf/xif/PaperQPilotObject.lean",
  "tmp/sheaf/xif/PaperQPilotLogVolume.lean",
  "tmp/sheaf/xif/PaperSignedHull.lean",
  "tmp/sheaf/xif/paper/QPilotObjectActual.lean",
  "tmp/sheaf/xif/paper/ThetaHullActual.lean",
  "tmp/sheaf/xif/paper/SignedHullLogActual.lean",
  "tmp/sheaf/xif/paper/OModuleActual.lean",
  "tmp/sheaf/xif/paper/IndeterminaciesActual.lean",
  "tmp/sheaf/xif/paper/SHELandingActual.lean",
  "tmp/sheaf/xif/paper/IPLAPTActual.lean",
  "tmp/sheaf/xif/paper/ThetaLinkActual.lean",
  "tmp/sheaf/xif/PaperXiFInclusion.lean",
  "tmp/sheaf/xif/PaperCertificate.lean",
  "tmp/sheaf/xif/paper/PaperXiFTheorem.lean",
  "tmp/sheaf/xif/paper/PaperXiFProof.lean",
  "tmp/sheaf/xif/PaperAssembly.lean"
)
$log = "tmp/sheaf/xif/paper/compile-all.log"
Remove-Item -ErrorAction SilentlyContinue $log
$fail = 0
foreach ($f in $files) {
  if (-not (Test-Path $f)) {
    Add-Content $log "MISSING $f"
    $fail++
    continue
  }
  $rel = ($f -replace "\\", "/")
  $olean = ".lake/build/lib/lean/" + ($rel -replace "\.lean$", ".olean")
  New-Item -ItemType Directory -Force -Path (Split-Path $olean) | Out-Null
  $out = & lake env lean -j1 -R "D:\lean" -o $olean $f 2>&1
  $code = $LASTEXITCODE
  Add-Content $log "=== $f EXIT $code"
  if ($out) { Add-Content $log ($out | Out-String) }
  if ($code -ne 0) { $fail++ }
}
Add-Content $log "FAIL_COUNT $fail"
Get-Content $log
exit $fail
