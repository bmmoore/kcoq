#!/bin/bash
find . -maxdepth 1 -mindepth 1 -type d -print0 | while IFS= read -r -d '' dir; do
  (cd "${dir}"; ./test.sh)
done
