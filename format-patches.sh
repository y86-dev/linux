#!/usr/bin/env bash

dir="$1"
base="$2"

shift 2

echo "Formatting patches for \"$dir\" from \"$base\"."

if [ ! -d "$dir" ]; then
    echo "Directory \"$dir\" does not exist."
    exit 1
fi

set -e

mkdir "patches/$dir"
git -C "$dir" format-patch --output-directory="../patches/$dir" --base "$base" "$base" $@
