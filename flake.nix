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
          pkgs = import nixpkgs {
            inherit system;
            config.allowUnfree = true;
          };
          llvmPkgs = pkgs.llvmPackages_latest;
        in
        {
          default = pkgs.mkShell {
            packages = [
              llvmPkgs.clang
              llvmPkgs.clang-tools
              pkgs.include-what-you-use
              pkgs.cmake
              pkgs.ninja
              pkgs.github-copilot-cli
            ];
            CC = "${llvmPkgs.clang}/bin/clang";
            CXX = "${llvmPkgs.clang}/bin/clang++";
          };
        });
    };
}