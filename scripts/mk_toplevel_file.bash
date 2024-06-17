#!/usr/bin/env bash

# Creates the toplevel Compfiles.lean file.

# (borrowed from
# https://github.com/YaelDillies/LeanAPAP/blob/master/scripts/mk_all.sh)

# remove an initial `./`
# replace all `/` with `.`
# remove the `.lean` suffix
# prepend `import `
find Compfiles -name \*.lean \
  | sed 's,^\./,,;s,/,.,g;s,\.lean$,,;s,^,import ,' \
  | sort -V -t . -k 2 > Compfiles.lean
