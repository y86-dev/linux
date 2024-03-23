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
           (let
  rust-bindgen-unwrapped = pkgs.rust-bindgen-unwrapped.overrideAttrs (prev: rec {
    version = "0.69.1";
    src = pkgs.fetchCrate {
      pname = "bindgen-cli";
      inherit version;
      sha256 = "sha256-zqyIc07RLti2xb23bWzL7zFjreEZuUstnYSp+jUX8Lw=";
    };
    cargoDeps = prev.cargoDeps.overrideAttrs {
      name = "${prev.pname}-${version}-vendor.tar.gz";
      inherit src;
      outputHash = "sha256-o1B8jq7Ze97pBLE9gvNsmCaD/tsW4f6DL0upzQkxbA4=";
    };
  });
in
  rust-bindgen.override {inherit rust-bindgen-unwrapped;})

           #(rust-bindgen.override {
           #    rust-bindgen-unwrapped = (pkgs.rust-bindgen-unwrapped.override { clang = clang_16; });
           #})
           perl
           sphinx
           graphviz
           texlive.combined.scheme-full
       ];
       hardeningDisable = pkgs.linux.hardeningDisable ++ [ "strictoverflow" ];
     };
}
