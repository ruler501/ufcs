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
          pkgs.catch2_3
        ];
      in
      {
        checks = (nixpkgs.lib.genAttrs
          [
            "clang-format"
            "clang-tidy"
            "include-what-you-use"
          ]
          (target: 
            (pkgs.runCommandLocal
              target
              {
                src = ./.;
                nativeBuildInputs = buildPackages;
              # Copy Catch2 source into place before CMake runs
              preConfigure = ''
                mkdir -p external/Catch2
                cp -r ${pkgs.catch2_3}/* external/Catch2/
                chmod -R +w external/Catch2  # Ensure writable for CMake
              '';
              }
              ''
                cmake -S ${./.} -B . -G Ninja -DCMAKE_CXX_COMPILER=clang++
                cmake --build . --target ${target}
                mkdir "$out"
              ''
            )
          )
        ) // {
          tests = (pkgs.runCommandLocal
            "tests"
            {
              src = ./.;
              nativeBuildInputs = buildPackages;
              # Copy Catch2 source into place before CMake runs
              preConfigure = ''
                mkdir -p external/Catch2
                cp -r ${pkgs.catch2_3}/* external/Catch2/
                chmod -R +w external/Catch2  # Ensure writable for CMake
              '';
            }
            ''
              cmake -S ${./.} -B . -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DUFCS_BUILD_TESTS=ON
              cmake --build . --target ufcs-tests
              ctest --test-dir . --output-on-failure
              mkdir "$out"
            ''
          );
        };
        
        devShells = {
          default = pkgs.mkShell {
            # Copy Catch2 source into place before CMake runs
            shellHook = ''
              rm -rf external/Catch2
              mkdir -p external/Catch2
              cp -r ${pkgs.catch2_3}/* external/Catch2/
              chmod -R +w external/Catch2  # Ensure writable for CMake
            '';
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
