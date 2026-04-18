#!/usr/bin/env bash
# Print a Markdown table of remaining `sorry` occurrences per chapter.
set -euo pipefail
cd "$(dirname "$0")/.."

{
  printf '| Chapter | `sorry` |\n| --- | ---: |\n'
  total=0
  for f in Rudin/Ch*.lean; do
    n=$( { grep -ow 'sorry' "$f" || true; } | wc -l | tr -d ' ')
    total=$((total + n))
    printf '| %s | %d |\n' "$(basename "$f" .lean)" "$n"
  done
  printf '| **Total** | **%d** |\n' "$total"
}
