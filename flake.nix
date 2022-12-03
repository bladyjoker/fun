{
  description = "Fun";
  nixConfig.bash-prompt = "\[nix-develop\]$ ";
  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.agda.url = github:agda/agda;

  outputs = { self, nixpkgs, flake-utils, agda }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          devShells.agda = pkgs.mkShell {
            name = "agda-shell-with-stdlib";
            buildInputs = [
              agda.packages."${system}".Agda
              pkgs.nixpkgs-fmt
              pkgs.haskellPackages.cabal-fmt
            ];
            # buildInputs = [ agda.packages.${system}.Agda ];
            # The build environment's $AGDA_DIR is set through this call.
            # See https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html#example-using-the-standard-library
            # AGDA_DIR = pkgs.agdaPackages.standard-library;
            shellHook = "cd learning-agda";
          };
        }
      );
}
