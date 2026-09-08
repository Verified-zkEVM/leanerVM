# Dependency policy

The scaffold currently has four tracked upstreams and two Lake packages:

| Component | Tracked ref | Role |
| --- | --- | --- |
| Lean | `v4.33.1` | Root toolchain |
| leanVM | `a386121f84292f6fa663aaa3e570c15bc0240ea2` | Audited Rust/specification target; not a Lake dependency |
| CompPoly | `3468b38c8fd270f93f55a259220a8abc544e7437` | Computable polynomial and field infrastructure; Mathlib arrives through it |
| Clean | `93c9d1ef45be9f687214625d7857889cf2485504` | Circuit, AIR, channel, and witness-generation infrastructure for the leanISA tables |

CompPoly supplies leanVM's fields (see [leanvm-target.md](leanvm-target.md)):

- `K = GF(2^64)`: `CompPoly.Fields.Binary.BF64`, the flat quotient
  `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` on a computable `BitVec 64` carrier, with Rabin-certified
  irreducibility;
- `E = GF(2^192)`: `CompPoly.Fields.Binary.BF64.Ext3`, the cubic extension `K[y]/(y^3 + y + 1)`
  on a `Vector BF64 3` carrier via `CompPoly.Fields.Extension`.

It is pinned to a `main` commit because the `v4.33.1` tag predates these modules. ArkLib, when
introduced, currently pins the tag; the two will need reconciling.

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

Expected future Lake dependency roles are:

- ArkLib: generic proof systems and oracle reductions; and
- VCVio: oracle computations and cryptographic security definitions.

Do not add either merely because it is anticipated. Introduce each when the first module
needs it.

Clean is pinned to `93c9d1ef`, the merge of
[PR #457](https://github.com/Verified-zkEVM/clean/pull/457), which moved Clean to Lean
`v4.33.1` and the same Mathlib revision (`0df444a3`) that CompPoly resolves, so the Lake graph
has one Mathlib. Its first consumers are the leanISA table components and the
`FiniteField BF64` instance described in [leanisa-blueprint.md](leanisa-blueprint.md). Clean's
core (`Clean/Circuit`, `Clean/Air`, `Clean/Table`) is generic over `FiniteField F`; its gadget
tree is `ZMod p` with `p > 512` and is not used. Two Clean limitations bind this repository and
are tracked in the blueprint: interactions distinguish push from pull by multiplicity `±1`,
which coincide in characteristic 2, and there is no degree bound on `Expression`.

leanVM's existing `formal/xmss/` project is not imported wholesale. At the target revision it
uses Lean `v4.31.0` and VCVio revision `cbd4144`; moving that reviewed security theorem onto this
repository's current dependency set is a deliberate port and statement/correspondence review,
not a reason to downgrade the root toolchain.
