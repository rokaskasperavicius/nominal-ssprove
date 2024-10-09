let
  pkgs = import ./pin.nix { };
  coqPackages = pkgs.coqPackages.overrideScope' (cfinal: cprev: {
      coq = cprev.coq.override { version = "8.18"; };
      mathcomp = cprev.mathcomp.override { version = "2.1.0"; };
      mathcomp-analysis = cprev.mathcomp-analysis.override { version = "1.0.0"; };
  });
  coqDeps = with coqPackages;
    [ deriving equations extructures mathcomp.ssreflect mathcomp-analysis ];
  ssprove = coqPackages.callPackage ( { coq, stdenv, fetchFromGitHub }:
    stdenv.mkDerivation {
      name = "coq${coq.coq-version}-ssprove";

      src = fetchFromGitHub {
        owner = "SSProve";
        repo = "ssprove";
        rev = "09e6d9ed06da92bde0d49cb187d22999b062abe1";
        sha256 = "GDkWH0LUsW165vAUoYC5of9ndr0MbfBtmrPhsJVXi3o=";
      };

      propagatedBuildInputs = [ coq ] ++ coqDeps;
      enableParallelBuilding = true;
      installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
    }
  ) { } ;
  disdis = coqPackages.callPackage ( { coq, stdenv }:
    stdenv.mkDerivation {
      name = "coq${coq.coq-version}-disdis";

      src = ./.;

      propagatedBuildInputs = [ coq ] ++ coqDeps ++ [ ssprove ];
      enableParallelBuilding = true;
      installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
    }
  ) { } ;
in pkgs // { inherit ssprove disdis; }
