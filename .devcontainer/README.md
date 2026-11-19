# The CircuitHdl devcontainer

A container in which the official upstream CIRCT binaries load, which the build host cannot do.
It exists for one missing tool -- `circt-verilog` -- and is sized so that CIRCT could also be
rebuilt from source inside it.

## Why the container exists

`AGENTS.md` records that Verilog is an export format here: the install at
`tools/circt-1.113.0` has no `circt-verilog`, slang is absent, and there is no `verilator`,
`iverilog` or `sv2v` on the host, so FIRRTL is the only real HDL that can be *read*. That is a
property of the release, not of the host -- slang was not enabled in CIRCT's published builds
until later, and 1.113.0 and 1.122.0 ship no `circt-verilog` at all.

The releases that do ship it will not load on Ubuntu 22.04, and it is worth being precise about
why, because the obvious reading is wrong. Measured with `readelf` on the published 1.164.0
tarball:

| Artefact | Requires | Host (glibc 2.35, libstdc++ 3.4.30) |
|---|---|---|
| `bin/circt-verilog` | `GLIBC_2.34`, `GLIBCXX_3.4.29` | satisfied |
| `bin/circt-verilog` | `GLIBC_ABI_DT_RELR`, `.relr.dyn` section | **not defined before glibc 2.36** |
| `lib/libCIRCTImportVerilog.so` | `GLIBCXX_3.4.31` | **libstdc++ stops at 3.4.30** |

So nothing in the executable is *functionally* too new: its ordinary symbol requirements are all
met. It is linked with RELR relocations, and a loader that does not advertise `GLIBC_ABI_DT_RELR`
refuses it outright before resolving a symbol. The slang frontend library then fails a second,
ordinary way on `GLIBCXX_3.4.31`, which is a GCC 13 symbol. Ubuntu 24.04 ships glibc 2.39 and
libstdc++ from GCC 14 and clears both.

## What it provides

- **Ubuntu 24.04** (noble) as the base, for the two reasons above.
- **CIRCT `firtool-1.164.0`**, the `circt-full-shared-linux-x64` release, unpacked whole at
  `/opt/circt/firtool-1.164.0`. This is the first line of releases carrying `circt-verilog`, and
  it is also past the glibc boundary -- those two facts are the same boundary, which is the whole
  argument for the container. It brings `firtool`, `arcilator`, `circt-opt`, `circt-lec`,
  `circt-bmc`, `circt-translate` and `mlir-opt` with it.
- **elan**, with *no* default toolchain. See below.
- **A C/C++ toolchain**: `build-essential`, `cmake`, `ninja-build`, `clang`, `lld`, `ccache`,
  `python3`, `git`, `curl`. Nothing in the Lean build needs these; they are there so CIRCT and
  slang can be built from source in the same container.
- **`libz3-dev`**, which on noble ships exactly `/usr/lib/x86_64-linux-gnu/libz3.so` -- the path
  `circt-lec` needs passed as `--shared-libs=`, and the one `AGENTS.md` already names. Z3 is not
  bundled in the release; the tarball carries `FindZ3.cmake` and `libCIRCTSMTToZ3LLVM.so` and no
  Z3 of its own. `$Z3_LIB` is set to that path as a convenience.

The release is a *shared* build: `bin/` holds thin drivers against 738 `.so` files in a sibling
`lib/`, found by an RPATH of `$ORIGIN/../lib`. The tree is installed whole and must stay that
way; copying binaries out of `bin/` alone yields something that cannot start.

## `CIRCT_BIN`

`scripts/arccheck.sh` and `scripts/firrtl.sh` both read `CIRCT_BIN` and fall back to the host's
1.113.0 path. The image sets

```
CIRCT_BIN=/opt/circt/firtool-1.164.0/bin
```

which is all those scripts need to run unmodified. It is set **only** in the `Dockerfile`, derived
from the `CIRCT_VERSION` build arg, and deliberately not repeated in `devcontainer.json`: two
copies of a path that have to agree are two copies that can stop agreeing.

Note that this points the cross-checks at a *different CIRCT* from the one the results in
`AGENTS.md` were measured against. 1.164.0 is 51 releases on from 1.113.0, so a disagreement found
in here is a question about which of the two is right, not automatically a regression.

## The `../veir` mount, and why the layout is what it is

`lakefile.toml` takes a **path** dependency on the sibling checkout:

```toml
[[require]]
name = "VeIR"
path = "../veir"
```

That path is relative to the repository root, so a devcontainer that mounted only the CircuitHdl
folder could not resolve VeIR and would fail in `lake build` -- and VeIR is on the proving path,
not an optional extra: the netlist refinement theorems execute `Veir.Netlist`.

The configuration reproduces the host layout rather than mounting the parent:

```
/workspaces/CircuitHdl   <- ${localWorkspaceFolder}      (workspaceFolder)
/workspaces/veir         <- ${localWorkspaceFolder}/../veir
```

so `../veir` resolves with nothing in the repository edited. Mounting the parent directory and
treating CircuitHdl as a subfolder is the more common recipe and is rejected here on inspection:
the parent is the user's scratch area -- 131 entries, many unrelated checkouts, and a private
`.pem` key. Binding one named sibling gives the container what the build needs and nothing else.

The sibling mount fails loudly if `../veir` is missing. That is the behaviour to want; a container
that came up without it would fail later and less clearly.

## The Lean toolchain is not pinned here

`lean-toolchain` pins `leanprover/lean4:v4.35.0-rc4` (and `../veir` pins the same). The image does
**not** name that version anywhere. elan is installed with `--default-toolchain none`, and
`postCreateCommand` runs

```sh
elan toolchain install "$(cat lean-toolchain)"
```

in the mounted workspace, so the file stays the single source of the pin and a toolchain bump
needs no change in here. The cost is that the first container start downloads a toolchain, which
is not quick. `ELAN_HOME` is `/opt/elan` and world-writable, because `updateRemoteUserUID` changes
the running uid *after* the image is built -- a directory chowned to a build-time uid would stop
being writable exactly when a toolchain needed installing.

## User and file ownership

The host account is uid 116366 with gid 1000, on shared `/proj` storage. Running as root would
leave everything `lake` writes under `.lake/` owned by uid 0 on the host, where the user could not
delete it. So the image creates a `vscode` user and `updateRemoteUserUID` remaps it onto the host
uid/gid at container start. The Dockerfile first removes noble's stock `ubuntu` account, which
occupies uid/gid 1000 and would otherwise collide with the group half of that remap.

## Verification status -- read this

In the spirit of "Verify, do not assert": **the image has not been built.** Docker is installed on
this host but the daemon is unreachable from the user account, so the claim that these files
produce a working container is a claim and not a result.

```
$ docker build -f .devcontainer/Dockerfile -t circuithdl-dev .devcontainer
ERROR: permission denied while trying to connect to the Docker daemon socket at
unix:///var/run/docker.sock: Head "http://%2Fvar%2Frun%2Fdocker.sock/_ping":
dial unix /var/run/docker.sock: connect: permission denied
```

`devcontainer build` fails the same way. The socket is `root:root` mode 660 -- membership of the
`docker` group (gid 10519) does not help, because the socket's group is `root` -- `sudo` requires
a password, and rootless Docker is not available either: there is no `newuidmap`/`newgidmap` and
no `/etc/subuid` entry for the account, so no uid range can be mapped.

What *was* checked without a daemon, by measurement rather than assumption:

- the release asset exists and is 143,219,539 bytes;
- it unpacks to a single top-level `firtool-1.164.0/` containing `bin/`, `lib/`, `include/`, and
  `bin/circt-verilog` is present (full `tar tz` listing, 8420 entries);
- the glibc and libstdc++ requirements in the table above, by `readelf` on the extracted
  `circt-verilog`, `firtool` and `libCIRCTImportVerilog.so`;
- Z3 is absent from the tarball, and noble's `libz3-dev` provides
  `/usr/lib/x86_64-linux-gnu/libz3.so`;
- every apt package named exists in noble;
- `elan-init.sh` is reachable and accepts `-y --no-modify-path --default-toolchain none`;
- `devcontainer.json` parses, and the `${localWorkspaceFolder}` substitutions are well formed.

Because the build could not be run, the `Dockerfile`'s **last layer is a self-check rather than a
comment**: it runs `circt-verilog --version`, `firtool --version`, `elan --version`, `cmake
--version`, `ninja --version`, resolves `lake`, and tests for `arcilator`, `circt-opt`,
`circt-lec`, `circt-bmc` and `libz3.so`. Every one of those is a thing this container exists to
provide, so a release that moves its layout or an elan that ignores `ELAN_HOME` fails
`docker build` loudly instead of producing an image that looks fine until the backend is run.

When someone with daemon access first builds this, the things to confirm are that
`circt-verilog --version` reports a slang version (expected: slang 11.0.0), that `lake test`
passes with `../veir` mounted, and that `scripts/arccheck.sh` and `scripts/firrtl.sh` find their
binaries through `CIRCT_BIN`.
