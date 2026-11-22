$deadline = (Get-Date).AddSeconds(480)
$root = 'D:\lean\.lake\build\lib\lean\ContinuousKummerTheory.olean'
while ((Get-Date) -lt $deadline) {
  if (Test-Path $root) { break }
  Start-Sleep -Seconds 10
}
if (Test-Path $root) {
  $i = Get-Item $root
  Write-Output ('ROOT_PRESENT ' + $i.Length + ' ' + $i.LastWriteTime.ToString('s') + ' SHA256=' + (Get-FileHash $root -Algorithm SHA256).Hash)
} else { Write-Output 'ROOT_MISSING' }
Get-ChildItem 'D:\lean\.lake\build\lib\lean\ContinuousKummerTheory' -Recurse -File -Filter *.olean | Select-Object Name,Length,LastWriteTime | Sort-Object LastWriteTime | Format-Table -AutoSize | Out-String -Width 200
Get-CimInstance Win32_Process -Filter "Name='lean.exe'" | Where-Object { $_.CommandLine -match 'ContinuousKummerTheory' } | Select-Object ProcessId,CreationDate,@{n='Args';e={$_.CommandLine.Substring(0,[Math]::Min(200,$_.CommandLine.Length))}} | Format-List | Out-String -Width 250
