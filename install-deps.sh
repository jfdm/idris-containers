#!/usr/bin/env bash

# There must be a deps-dir and at least one dep
if [ "$#" -lt 2 ]; then
    echo "Usage $0 [deps-dir] [dep ...]"
    exit 1
fi

# Create the deps dir
DEPS_DIR="$1"
echo "===> Creating deps directory: $DEPS_DIR"
mkdir -p "$DEPS_DIR"

for dep in "${@:2}"; do    
    if [ -d "$DEPS_DIR/$dep" ]; then
        # If the dependency directory already exists, fetch the repo
        echo "===> Fetching $dep"
        git fetch "$DEPS_DIR/$dep"
    else
        # Otherwise, clone it
        echo "===> Cloning $dep"
        git clone "git@github.com:$dep.git" "$DEPS_DIR/$dep"
    fi

    # Install the dependency
    echo "===> Installing $dep"
    make -C "$DEPS_DIR/$dep" install
done
