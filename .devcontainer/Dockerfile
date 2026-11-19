# A container in which the *official* CIRCT release binaries load, and in which CIRCT could be
# rebuilt from source.
#
# Ubuntu 24.04 is not a preference, it is the requirement, and the 1.164.0 release says so in two
# independent ways. Measured with `readelf` on the published tarball:
#
#   - `bin/circt-verilog` has a `.relr.dyn` section and a dependency on the version
#     `GLIBC_ABI_DT_RELR`. That marker is defined by glibc 2.36 and later. The build host is
#     Ubuntu 22.04 with glibc 2.35, which does not define it, so the loader refuses the binary
#     before resolving a single symbol. Worth noting because it is counter-intuitive: the
#     executable's *ordinary* requirements top out at GLIBC_2.34 and GLIBCXX_3.4.29, both of which
#     22.04 satisfies. Nothing in it is too new; the relocation format is.
#   - `lib/libCIRCTImportVerilog.so` -- the slang frontend, the reason for all of this -- requires
#     GLIBCXX_3.4.31. The host's libstdc++ stops at 3.4.30, so that one is an ordinary
#     too-old-library failure and would bite even without the first.
#
# Noble ships glibc 2.39 and libstdc++ from GCC 14, clearing both.
FROM ubuntu:24.04

# `CIRCT_VERSION` is both the release tag and the name of the single top-level directory inside
# the tarball, which is why one variable can serve as both. Verified against the published asset:
# `circt-full-shared-linux-x64.tar.gz` unpacks to `firtool-1.164.0/{bin,lib,include}`.
ARG CIRCT_VERSION=firtool-1.164.0
ARG CIRCT_PREFIX=/opt/circt

ENV DEBIAN_FRONTEND=noninteractive

# Three groups, and they are here for different reasons:
#
#   - build-essential .. ccache: a C/C++ toolchain good enough to build CIRCT and slang in here.
#     That is the second half of the brief; nothing in the Lean build needs them.
#   - libz3-dev: `circt-lec` resolves Z3 through the JIT and needs `--shared-libs=<path>/libz3.so`
#     passed explicitly. On noble this package ships exactly /usr/lib/x86_64-linux-gnu/libz3.so,
#     which is the path AGENTS.md already names. Z3 is *not* bundled in the release tarball -- it
#     carries FindZ3.cmake and libCIRCTSMTToZ3LLVM.so and no Z3 of its own.
#   - zlib1g, libtinfo6, libxml2: runtime dependencies of the 738 shared libraries in the release.
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential cmake ninja-build clang lld ccache \
        python3 python3-venv git curl ca-certificates xz-utils unzip \
        libz3-dev zlib1g libtinfo6 libxml2 \
        sudo less procps \
    && rm -rf /var/lib/apt/lists/*

# Noble ships a stock `ubuntu` user at uid/gid 1000. Removing it frees 1000 so the `vscode` user
# below can take it cleanly, and -- more to the point -- so that `updateRemoteUserUID` has no
# existing account in its way when it remaps `vscode` onto the host user. The host account here is
# uid 116366 with gid 1000, so the group half of that remap would otherwise collide with `ubuntu`.
ARG USERNAME=vscode
ARG USER_UID=1000
ARG USER_GID=${USER_UID}
RUN userdel -r ubuntu 2>/dev/null || true; \
    groupdel ubuntu 2>/dev/null || true; \
    groupadd --gid ${USER_GID} ${USERNAME} && \
    useradd --uid ${USER_UID} --gid ${USER_GID} --create-home --shell /bin/bash ${USERNAME} && \
    echo "${USERNAME} ALL=(root) NOPASSWD:ALL" > /etc/sudoers.d/${USERNAME} && \
    chmod 0440 /etc/sudoers.d/${USERNAME}

# The release is a *shared* build: bin/ is thin drivers against 738 .so files in a sibling lib/,
# resolved by an RPATH of $ORIGIN/../lib. So the tree has to be installed whole and kept together;
# copying binaries out of bin/ alone would produce something that cannot start.
RUN mkdir -p ${CIRCT_PREFIX} && \
    curl -fsSL \
      https://github.com/llvm/circt/releases/download/${CIRCT_VERSION}/circt-full-shared-linux-x64.tar.gz \
      | tar -xz -C ${CIRCT_PREFIX} && \
    test -x ${CIRCT_PREFIX}/${CIRCT_VERSION}/bin/circt-verilog

# `scripts/arccheck.sh` and `scripts/firrtl.sh` both read `CIRCT_BIN`, defaulting to the host's
# 1.113.0 install. Setting it here is the whole of what those scripts need to run unmodified --
# deliberately set *only* here, derived from the ARG, so a version bump is one edit rather than
# two places that can drift apart. `Z3_LIB` is a convenience for `circt-lec --shared-libs=`.
ENV CIRCT_BIN=${CIRCT_PREFIX}/${CIRCT_VERSION}/bin
ENV Z3_LIB=/usr/lib/x86_64-linux-gnu/libz3.so

# elan goes first so `lean`/`lake` resolve to its shims. CIRCT goes *last*, which is the point:
# its bin/ carries a full LLVM (`opt`, `llc`, `count`, `not`, `dsymutil`, `llvm-ar`), and putting
# that ahead of /usr/bin would shadow host tools for anyone building CIRCT from source in here.
ENV ELAN_HOME=/opt/elan
ENV PATH=${ELAN_HOME}/bin:${PATH}:${CIRCT_PREFIX}/${CIRCT_VERSION}/bin

# `--default-toolchain none` is the reason this image does not name a Lean version. The pin lives
# in the repository's `lean-toolchain`, which is not in the build context and should not be baked
# into a layer; devcontainer.json's postCreateCommand reads it from the mounted workspace. ELAN_HOME
# is world-writable because `updateRemoteUserUID` changes the running uid after the image is built,
# so a directory chowned to a build-time uid would stop being writable exactly when a toolchain
# needs installing.
RUN mkdir -p ${ELAN_HOME} && \
    curl -fsSL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh && \
    sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain none && \
    rm /tmp/elan-init.sh && \
    chmod -R a+rwX ${ELAN_HOME}

# A build-time gate rather than a comment claiming the image works. Each line below is one of the
# things this container exists to provide, so a release that moves its layout, an elan that ignores
# ELAN_HOME, or a base image that cannot load the binaries fails `docker build` here instead of
# failing silently the first time someone runs the backend.
RUN set -eux; \
    circt-verilog --version; \
    firtool --version; \
    test -x "${CIRCT_BIN}/arcilator"; \
    test -x "${CIRCT_BIN}/circt-opt"; \
    test -x "${CIRCT_BIN}/circt-lec"; \
    test -x "${CIRCT_BIN}/circt-bmc"; \
    test -f "${Z3_LIB}"; \
    elan --version; \
    command -v lake; \
    cmake --version | head -1; \
    ninja --version

USER ${USERNAME}
