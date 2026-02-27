{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    treefmt-nix.url = "github:numtide/treefmt-nix";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";
  };
  outputs =
    {
      self,
      nixpkgs,
      treefmt-nix,
    }:
    let
      eachSystem = nixpkgs.lib.genAttrs [
        "x86_64-linux"
        "aarch64-linux"
      ];

      treefmtEval = eachSystem (
        system:
        (treefmt-nix.lib.evalModule nixpkgs.legacyPackages.${system} {
          programs.nixfmt.enable = true;
          settings.on-unmatched = "info";
        })
      );
    in
    {
      devShells = eachSystem (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          lean4 = pkgs.lean4;
        in
        {
          default = pkgs.stdenv.mkDerivation {
            name = "lean-model-checking";
            nativeBuildInputs = [ lean4 ];
          };
        }
      );

      formatter = eachSystem (system: treefmtEval.${system}.config.build.wrapper);

      checks = eachSystem (system: {
        treefmt = treefmtEval.${system}.config.build.check self;
      });
    };
}
