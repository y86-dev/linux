{
  inputs = {
    nixpkgs.url = "github:nixoS/nixpkgs/nixos-unstable";
  };
  outputs = {nixpkgs, ...}: let
    system = "x86_64-linux";
    pkgs = import nixpkgs {
      inherit system;
    };
  in {
    devShells."${system}".default = pkgs.mkShell {
      name = "kernel";
      packages = with pkgs; [
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
