#!/usr/bin/env bash

OUTPUT=$(git status --porcelain)

if [[ -z $OUTPUT ]]; then
    echo "Working directory is clean."
else
    echo "Working directory is not clean."
    echo $OUTPUT
    git diff
    exit 1
fi
