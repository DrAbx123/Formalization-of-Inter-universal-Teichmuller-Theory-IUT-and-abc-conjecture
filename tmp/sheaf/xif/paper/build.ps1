
param([string]$list)
$mods = $list -split ','
foreach ($m in $mods) {
  $rel = $m -replace '\.', '\'
  $lean = "$rel.lean"
  $olean = ".lake/build/lib/lean/$rel.olean"
  $log = ".lake/build/" + ($m -replace '\.', '_') + ".log"
  Write-Output "=== compiling $m"
  & lake env lean -j1 -R D:\lean -M 8192 -o $olean $lean *> $log
  if ($LASTEXITCODE -ne 0) {
    Write-Output "FAILED $m"
    Get-Content $log | Select-Object -Last 80
    exit 1
  }
  Get-Content $log | Select-Object -Last 10
  Write-Output "OK $m"
}
Write-Output "ALLDONE"
