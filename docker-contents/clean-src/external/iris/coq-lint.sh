#!/bin/bash
set -e
## A simple shell script checking for some common Coq issues.

FILE="$1"

if egrep -n '^\s*((Existing\s+|Program\s+)Instance|Arguments|Remove|Hint\s+(Extern|Constructors|Resolve|Immediate|Mode|Opaque|Transparent|Unfold)|(Open|Close)\s+Scope|Opaque|Transparent)\b' "$FILE"; then
    echo "ERROR: $FILE contains 'Instance'/'Arguments'/'Hint' or another side-effect without locality (see above)."
    echo "Please add 'Global' or 'Local' as appropriate."
    echo
    exit 1
fi
