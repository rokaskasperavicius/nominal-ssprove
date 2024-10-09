# This file can be used to pin the used packages to a specific version.
# https://nixos.wiki/wiki/FAQ/Pinning_Nixpkgs
# Update the pin with (also update 21.11 to be the current stable channel):
# nix-prefetch-git https://github.com/nixos/nixpkgs.git refs/heads/nixos-21.11 > pin.json
with builtins;
let data = fromJSON (readFile ./pin.json);
in import (fetchTarball {
  name = "nixos-pin-${substring 0 10 data.date}";
  url = "https://github.com/nixos/nixpkgs/archive/${data.rev}.tar.gz";
  inherit (data) sha256;
})
