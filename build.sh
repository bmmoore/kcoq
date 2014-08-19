#!/bin/sh
cd $(dirname $0)
cabal "${@:-build}"
