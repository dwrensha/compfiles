#! /usr/bin/bash

set -x

TACTIC="${1:-exact?}"

OUTFILE=~/Desktop/tryAtEachStep.txt

rm $OUTFILE

for f in `find Compfiles -name "*.lean" | shuf`
do
    echo >> $OUTFILE
    echo "FILE : " $f >> $OUTFILE
    lake exe tryAtEachStep "$TACTIC" $f >> $OUTFILE
done
