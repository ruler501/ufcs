{
  description = "Development environment for ufcs";

  inputs = {
    systems.url = "github:nix-systems/triplet";
    flake-utils = {
      url = "github:numtide/flake-utils/main";
      inputs.systems.follows = "systems";
    };
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    nix-github-actions = {
      url = "github:nix-community/nix-github-actions";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, flake-utils, nixpkgs, nix-github-actions, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
        llvmPkgs = pkgs.llvmPackages_latest;
        buildPackages = [
          llvmPkgs.clang
          llvmPkgs.clang-tools
          pkgs.include-what-you-use
          pkgs.cmake
          pkgs.ninja
        ];
      in
      {
        checks = {
          clang-tidy = (pkgs.runCommandLocal
          "clang-tidy"
          {
            src = ./.;
            nativeBuildInputs = buildPackages;
          }
          ''
            cmake -S . -B build-nix -G Ninja -DCMAKE_CXX_COMPILER=clang++
            cmake --build build-nix --target clang-tidy
          '');
        };
        
        devShells = {
          default = pkgs.mkShell {
            packages = buildPackages ++ [
              pkgs.github-cli
              pkgs.github-copilot-cli
            ];
            CC = "${llvmPkgs.clang}/bin/clang";
            CXX = "${llvmPkgs.clang}/bin/clang++";
          };
        };
    }) // {
      githubActions = nix-github-actions.lib.mkGithubMatrix {
        checks = nixpkgs.lib.getAttrs [ "x86_64-linux" ] self.checks;
      };
    };
}
