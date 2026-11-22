# Launch DeepSeek Harness with a larger Node/V8 heap (default crashes near 4GB).
$env:NODE_OPTIONS = "--max-old-space-size=8192"
$exe = 'D:\Users\Administrator\AppData\Local\Programs\DeepSeek Harness\DeepSeek Harness.exe'
if (-not (Test-Path -LiteralPath $exe)) { Write-Error "DeepSeek Harness.exe not found: $exe"; exit 1 }
Start-Process -FilePath $exe
Write-Output "Started DeepSeek Harness with NODE_OPTIONS=$env:NODE_OPTIONS"
