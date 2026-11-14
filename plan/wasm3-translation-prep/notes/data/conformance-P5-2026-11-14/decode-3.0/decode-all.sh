#!/bin/sh
# EXPERIMENT: run decode-one.lsp for every script of the spec-test-3 data.
# sh decode-all.sh ACL2 JOBS TIMEOUT  (from this directory)
acl2=$1; jobs=${2:-8}; timeout=${3:-1800}; data=$(cat data-path)/
mkdir -p d3; sed -n 's/^ "\(.*\)"$/\1/p' $data/index.lsp > d3/NAMES
export acl2 timeout data
xargs -P "$jobs" -I{} sh -c '
  { echo "(assign d3-name \"{}\")"; echo "(assign d3-data \"$data\")"; cat decode-one.lsp; } |
    timeout "$timeout" "$acl2" > "d3/{}.out" 2>&1
  echo "D3-EXIT $?" >> "d3/{}.out"' < d3/NAMES
