#!/bin/bash

echo "Creating Dir"
mkdir -p dependencies/
cd dependencies/

echo "Fetching Deps for Containers"

echo "Fetching testing"
git clone https://github.com/jfdm/idris-testing.git testing
cd testing/
idris --build test.ipkg
cd ../

cd ../
