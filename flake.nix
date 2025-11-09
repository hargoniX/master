{
  description = "LMU Master";

  inputs.utils.url = "github:numtide/flake-utils";
  # https://www.nixhub.io/packages/typst, 0.14
  inputs.nixpkgs.url = "github:nixos/nixpkgs/3b63975e4cfdec14118a1b7e2527614269ccfd93";

  outputs = {
    nixpkgs,
    utils,
    ...
  }:
    utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs { system = system; config.allowUnfree = true; };
      typst-shell = pkgs.mkShell {
        nativeBuildInputs = [
          pkgs.tinymist
          pkgs.typst
          pkgs.drawio
          pkgs.pdf2svg
        ];
      };
    in {
      devShells.default = typst-shell;
      legacyPackages = pkgs;
    });
}
