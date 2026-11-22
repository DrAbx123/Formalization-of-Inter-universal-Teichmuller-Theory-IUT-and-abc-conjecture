$log = 'D:\lean\tmp\sheaf\xif\paper\S1413Run.log'
"START $(Get-Date -Format o)" | Out-File -Encoding utf8 $log
Set-Location 'D:\lean'
$ok = $false
for ($i = 1; $i -le 10; $i++) {
  "=== attempt $i ===" | Out-File -Append -Encoding utf8 $log
  $out = & lake env lean tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.lean 2>&1
  $rc = $LASTEXITCODE
  $out | Out-File -Append -Encoding utf8 $log
  "EXIT=$rc" | Out-File -Append -Encoding utf8 $log
  if ($rc -eq 0) { $ok = $true; break }
  Start-Sleep -Seconds 10
}
"DONE ok=$ok" | Out-File -Append -Encoding utf8 $log
