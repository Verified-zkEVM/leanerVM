# Dependency policy

The scaffold currently has five tracked upstreams and three Lake packages:

| Component | Tracked ref | Role |
| --- | --- | --- |
| Lean | `v4.33.1` | Root toolchain |
| leanVM | `a386121f84292f6fa663aaa3e570c15bc0240ea2` | Audited Rust/specification target; not a Lake dependency |
| CompPoly | `3468b38c8fd270f93f55a259220a8abc544e7437` | Computable polynomial and field infrastructure; Mathlib arrives through it |
| Clean | `93c9d1ef45be9f687214625d7857889cf2485504` | Circuit, AIR, channel, and witness-generation infrastructure for the leanISA tables |
| ArkLib | `dca90385fb40dd5eb8da9145da6348ed17f5cd8b` | Interactive oracle reductions, their security definitions and composition, sumcheck, multilinear theory; VCVio arrives through it |

CompPoly supplies leanVM's fields (see [leanvm-target.md](leanvm-target.md)):

- `K = GF(2^64)`: `CompPoly.Fields.Binary.BF64`, the flat quotient
  `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` on a computable `BitVec 64` carrier, with Rabin-certified
  irreducibility;
- `E = GF(2^192)`: `CompPoly.Fields.Binary.BF64.Ext3`, the cubic extension `K[y]/(y^3 + y + 1)`
  on a `Vector BF64 3` carrier via `CompPoly.Fields.Extension`.

It is pinned to a `main` commit because the `v4.33.1` tag predates these modules. ArkLib pins
the tag (`a09455a2`, fifteen commits earlier); Lake resolves a package once, and the root's
direct requirement wins, so ArkLib's CompPoly-facing modules (`ArkLib/ToCompPoly/`,
`OracleInterface.lean`, a few `Data/` files) are compiled here against `3468b38c`. The diff
between the two CompPoly revisions is additive on every declaration ArkLib imports; a CompPoly
pin bump on either side must re-check that.

The machine-readable baseline is `upstreams.json`; `lake-manifest.json` records the resolved
Lake graph. The weekly drift workflow reports newer releases or commits but never rewrites
dependency files automatically. The leanVM pin names the exact behavior being formalized and
tested even though its branch is monitored for drift. See
[leanvm-target.md](leanvm-target.md) before updating it.

Add a dependency only with a named first-party use and a narrow import. A dependency PR must:

1. update the toolchain/Lake requirement, `upstreams.json`, and manifest together;
2. build and test the complete affected import cone;
3. review API changes used by theorem statements;
4. audit the first-party namespace's transitive kernel dependencies; and
5. record semantic changes separately from mechanical porting.

ArkLib is pinned to `dca90385`, the commit that moved ArkLib to Lean's module system
(PR #897), so every ArkLib file is a `module` and can be imported from `module` files here.
Its Lake package name is `Arklib`, which is what the `[[require]]` must say. It brings VCVio
(`f9dc47d9`), PolyFun (`c0c92369`, owned by VCVio), loom2, cslib and doc-gen4's dependencies
into the manifest; its Mathlib is the same `0df444a3`, so the graph still has one Mathlib. Its
first consumer is `LeanerVM/Protocol/Field.lean`, described in
[roadmap/protocol-blueprint.md](roadmap/protocol-blueprint.md), whose dependency table lists
every ArkLib declaration consumed and whose ledger lists the ArkLib theorems admitted at the pin
that this repository must not depend on: the kernel axiom audit (`axiom-audit-root: LeanerVM`)
rejects `sorryAx`, and ArkLib's `scripts/axiom_baseline.json` is an allowlist, not a proof.
Building ArkLib's import cone loads its build-time lint plugin (`ArkLibLintPlugin:shared`) while
elaborating each ArkLib module; a first `lake build` with several explicit targets was seen to
schedule that plugin twice and fail one link, after which a second invocation proceeds
(status finding E6).

VCVio is not required directly: it arrives through ArkLib, and a direct requirement would be
added only for a first-party consumer of a VCVio declaration that ArkLib does not re-export.

CompPoly is pinned to `3468b38c`, an untagged commit fifteen commits after its `v4.33.1`
release, because the computable `BF64` and `Ext3` fields are newer than the tag. CompPoly's
lakefile sets `preferReleaseBuild`, so on a checkout where CompPoly is not yet built Lake
looks for a release tag at the pin, finds none, logs a warning, and builds from source; under
`--wfail` that warning fails the build. CI and `scripts/validate.sh` therefore run `lake build`
without `--wfail` and with Lake's caches enabled; the lookup costs one warning and changes
nothing else. Mathlib's oleans come from `lake exe cache get`, which CI runs before the build:
compiling Mathlib from source does not fit the job's time limit. Pinning CompPoly to a release
tag that contains the binary fields would let a build download the prebuilt archive instead.

Clean is pinned to `93c9d1ef`, the merge of
[PR #457](https://github.com/Verified-zkEVM/clean/pull/457), which moved Clean to Lean
`v4.33.1` and the same Mathlib revision (`0df444a3`) that CompPoly resolves, so the Lake graph
has one Mathlib. Its first consumers are the leanISA table components and the
`FiniteField BF64` instance described in
[roadmap/leanisa-blueprint.md](roadmap/leanisa-blueprint.md). Clean's core (`Clean/Circuit`,
`Clean/Air`, `Clean/Table`) is generic over `FiniteField F`; its gadget
tree is `ZMod p` with `p > 512` and is not used. Two Clean limitations bind this repository and
are tracked in the blueprint: interactions distinguish push from pull by multiplicity `±1`,
which coincide in characteristic 2, and there is no degree bound on `Expression`. A third shapes
the file policy: Clean's files are not `module`s, and Lean `v4.33.1` refuses to import a
non-`module` from a `module`, so Clean is consumed only from plain files and every file
importing them is plain too; see `CONTRIBUTING.md` and finding C8 in
[roadmap/leanisa-status.md](roadmap/leanisa-status.md).

leanVM's existing `formal/xmss/` project is not imported wholesale. At the target revision it
uses Lean `v4.31.0` and VCVio revision `cbd4144`; moving that reviewed security theorem onto this
repository's current dependency set is a deliberate port and statement/correspondence review,
not a reason to downgrade the root toolchain.
