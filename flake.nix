{
  description = "Fun";

  outputs = { self, nixpkgs }:
    let pkgs = import nixpkgs { system = "x86_64-linux"; };
    in {

      inherit pkgs;
      devShells.x86_64-linux.prolog =
        pkgs.mkShell { buildInputs = [ pkgs.swiPrologWithGui pkgs.nixfmt ]; };

    };
}
