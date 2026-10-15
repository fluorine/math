#!/bin/sh
set -eu
vix_script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
vix_formal_dir="$vix_script_dir/../formal"
python3 "$vix_script_dir/generate_certificate.py" --check
if [ -z "${VIX_LEAN:-}" ] && ! command -v lean >/dev/null 2>&1; then
  vix_local_lean=/Volumes/2tb/math/.research-cache/toolchains/lean-4.34.1-darwin_aarch64/bin/lean
  if [ -x "$vix_local_lean" ]; then
    VIX_LEAN=$vix_local_lean
    export VIX_LEAN
  fi
fi
exec python3 "$vix_formal_dir/build.py" "$@"
