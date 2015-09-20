#!/bin/bash

echo "Creating Dir"
mkdir -p dependancies/
cd dependancies/

echo "Fetching Deps for Containers"

echo "Fetching lightyear "
git clone git@github.com:ziman/lightyear.git lightyear
cd lightyear/
make install
cd ../

echo "Fetching testing"
git clone git@github.com:jfdm/idris-testing.git testing
cd testing/
make install
cd ../

cd ../
