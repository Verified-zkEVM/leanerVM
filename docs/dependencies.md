# Dependency policy

The repository tracks three upstreams, one of which is a Lake package:

| Component | Tracked ref | Role |
| --- | --- | --- |
| Lean | `v4.33.1` | Root toolchain |
| leanVM | `a386121f84292f6fa663aaa3e570c15bc0240ea2` | Audited Rust/specification target; not a Lake dependency |
| CompPoly | `2aa593725644fb0fe7c578be68cc5ec96bbc8dd2` | Computable polynomial and field infrastructure; Mathlib arrives through it |

CompPoly is consumed by `LeanerVM.Parameters.Field.*`, which uses its Rabin irreducibility
certificates (`CompPoly.Data.Polynomial.Rabin{,Certificate}`), its `GF(2)` bit-vector and
polynomial bridge (`CompPoly.Fields.Binary.Common`), and its computable extension-field
framework (`CompPoly.Fields.Extension.*`). It is pinned to a `main` commit rather than the
`v4.33.1` tag because the tag predates the fast binary-tower work; note that ArkLib, when it
is introduced, currently pins the tag, so the two will need reconciling.

CompPoly's binary *tower* fields build `GF(2^64)` as an iterated quadratic extension. leanVM's
`K` is the flat quotient `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`. The two are abstractly
isomorphic but use different bases, so their bit-level encodings disagree and the tower
instances are not a substitute for the source-faithful base field.

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

- ArkLib: generic proof systems and oracle reductions;
- VCVio: oracle computations and cryptographic security definitions; and
- Clean: circuit, AIR, table, and witness-generation infrastructure.

Do not add all four merely because they are anticipated. Introduce each when the first module
needs it. Clean remains deferred until
[PR #457](https://github.com/Verified-zkEVM/clean/pull/457), or a successor, merges with its
Lean 4.33 tactic/opacity review resolved and passes a focused downstream compatibility branch.

leanVM's existing `formal/xmss/` project is not imported wholesale. At the target revision it
uses Lean `v4.31.0` and VCVio revision `cbd4144`; moving that reviewed security theorem onto this
repository's current dependency set is a deliberate port and statement/correspondence review,
not a reason to downgrade the root toolchain.
