#!/bin/bash
DIR="$(cd "$(dirname "$BASH_SOURCE")" && pwd)"
cd "$DIR"/test/regression
./test.sh
