# This is used in the Travis build to install the Idris compiler.
let
  pkgs = import <nixpkgs> {};
  stdenv = pkgs.stdenv;
in {
  idris-containers = stdenv.mkDerivation {
    name = "idris-containers";
    src = ./.;
    buildInputs = with pkgs; [ idris gmp ];
  };
}
