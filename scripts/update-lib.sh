git ls-files 'ArkLib/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > ArkLib.lean
# git ls-files 'Examples/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > Examples.lean
