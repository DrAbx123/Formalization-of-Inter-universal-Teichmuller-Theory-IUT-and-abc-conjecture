@echo off
cd /d D:\lean
lake env lean -j1 -R D:/lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/_S1912Check.olean tmp/sheaf/xif/paper/S1912EqualRankTraceRetractionActual.lean > "D:\lean\tmp\sheaf\xif\paper\_S1912_build4.log" 2>&1
echo EXIT=%errorlevel% >> "D:\lean\tmp\sheaf\xif\paper\_S1912_build4.log"
