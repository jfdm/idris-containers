#!/bin/bash

echo "Creating Dir"
mkdir -p dependancies/
cd dependancies/

echo "Fetching Deps for Containers"

echo "Fetching testing"
git clone git@github.com:jfdm/idris-testing.git testing
cd testing/
idris --install test.ipkg
cd ../

cd ../
