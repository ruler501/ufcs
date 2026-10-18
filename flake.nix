{
  description = "Development environment for ufcs";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          clang = pkgs.llvmPackages_latest.clang;
        in
        {
          default = pkgs.mkShell {
            packages = [ clang pkgs.cmake pkgs.ninja ];
            CC = "${clang}/bin/clang";
            CXX = "${clang}/bin/clang++";
          };
        });
    };
}