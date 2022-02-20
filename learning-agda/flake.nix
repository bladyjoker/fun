{
  description = "my project description";

  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let pkgs = nixpkgs.legacyPackages.${system}; in
        {
          devShell = with pkgs; mkShell {
            name = "agda-shell-with-stdlib";
            packages = [ agda-pkg haskellPackages.Agda nixpkgs-fmt haskellPackages.cabal-fmt ];

            # The build environment's $AGDA_DIR is set through this call.
            #AGDA_DIR = agdaDir;
          };
        }
      );
}
