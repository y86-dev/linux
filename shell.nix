with import <nixpkgs> {};
{
     testEnv = stdenv.mkDerivation {
       name = "kernel-dev";
       buildInputs = [
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
           # libelf
           # rust-bindgen
           (rust-bindgen.override {
               rust-bindgen-unwrapped = (pkgs.rust-bindgen-unwrapped.override { clang = clang_16; });
           })
           perl
           sphinx
           graphviz
           texlive.combined.scheme-full
       ];
     };
}
