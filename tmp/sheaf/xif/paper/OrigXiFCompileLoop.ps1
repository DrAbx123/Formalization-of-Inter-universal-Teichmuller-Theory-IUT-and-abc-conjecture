param([int]$MaxAttempts = 15, [int]$MaxWaitMinutes = 60)
$log = "D:\lean\tmp\origxif_loop.log"
$hdr = "D:\lean\tmp\origxif_header.bin"
Set-Content -LiteralPath $log -Value ""
$deadline = (Get-Date).AddMinutes($MaxWaitMinutes)
for ($i = 1; $i -le $MaxAttempts; $i++) {
  while ((Get-Date) -lt $deadline) {
    $n = (Get-Process lean -ErrorAction SilentlyContinue | Measure-Object).Count
    if ($n -le 8) { break }
    Start-Sleep -Milliseconds 1500
  }
  $n = (Get-Process lean -ErrorAction SilentlyContinue | Measure-Object).Count
  $hasHdr = (Test-Path -LiteralPath $hdr) -and ((Get-Item -LiteralPath $hdr).Length -gt 0)
  Add-Content -LiteralPath $log -Value ("attempt " + $i + " at " + (Get-Date -Format o) + " lean=" + $n + " hdr=" + $hasHdr)
  if ($hasHdr) {
    & lake env lean --incr-load=$hdr -j1 tmp/sheaf/xif/paper/OrigXiFNormalizedBridgeExact.lean *>> $log
  } else {
    & lake env lean --incr-header-save=$hdr -j1 tmp/sheaf/xif/paper/OrigXiFNormalizedBridgeExact.lean *>> $log
  }
  $code = $LASTEXITCODE
  Add-Content -LiteralPath $log -Value ("EXIT=" + $code)
  if ($code -eq 0) { break }
  $tail = Get-Content -LiteralPath $log -Tail 12
  if ($tail -match 'failed to read file') {
    Start-Sleep -Seconds 8
    $deadline = (Get-Date).AddMinutes(10)
    continue
  }
  if ($hasHdr -and ($tail -match 'incremental|snapshot|header|incr')) {
    Remove-Item -LiteralPath $hdr -Force -ErrorAction SilentlyContinue
    Start-Sleep -Seconds 5
    $deadline = (Get-Date).AddMinutes(10)
    continue
  }
  break
}
