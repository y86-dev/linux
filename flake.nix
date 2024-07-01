{
  nixConfig = {
    extra-substituters = [
      "https://nix-community.cachix.org"
    ];
    extra-trusted-public-keys = [
      "nix-community.cachix.org-1:mB9FSh9qf2dCimDSUo8Zy7bkq5CX+/rkCWyvRCYg3Fs="
    ];
  };
  inputs = {
    nixpkgs.url = "github:nixoS/nixpkgs/nixos-unstable";
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs = {
    nixpkgs,
    fenix,
    ...
  }: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {
      overlays = [fenix.overlays.default];
      inherit system;
    };
  in {
    devShells."${system}".default = pkgs.mkShell {
      name = "kernel";
      packages = with pkgs; [
        fenix.packages."${system}".stable.toolchain
        rust-analyzer-nightly
        stdenv
        git
        gnumake
        ncurses
        bc
        flex
        bison
        elfutils
        openssl
        qemu_full
        debootstrap
        gcc
        gdb
        clang_16
        clang-tools_16
        lld_16
        llvmPackages_16.libllvm
        python3Packages.pyaml
        rust-bindgen
        perl
        sphinx
        graphviz
        texlive.combined.scheme-full
      ];
      shellHook = ''exec fish'';
      hardeningDisable = pkgs.linux.hardeningDisable ++ ["strictoverflow"];
    };
  };
}
