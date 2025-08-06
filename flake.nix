{
  description = "LMU Master";

  inputs.utils.url = "github:numtide/flake-utils";
  # https://www.nixhub.io/packages/typst, 0.13
  inputs.nixpkgs.url = "github:nixos/nixpkgs/6c5c5f5100281f8f4ff23f13edd17d645178c87c";

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
