# Dependency policy

The scaffold currently has two tracked upstreams and no third-party Lake packages:

| Component | Tracked ref | Role |
| --- | --- | --- |
| Lean | `v4.33.1` | Root toolchain |
| leanVM | `a386121f84292f6fa663aaa3e570c15bc0240ea2` | Audited Rust/specification target; not a Lake dependency |

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
- VCVio: oracle computations and cryptographic security definitions;
- CompPoly: computable polynomial and field infrastructure; and
- Clean: circuit, AIR, table, and witness-generation infrastructure.

Do not add all four merely because they are anticipated. Introduce each when the first module
needs it. Clean remains deferred until
[PR #457](https://github.com/Verified-zkEVM/clean/pull/457), or a successor, merges with its
Lean 4.33 tactic/opacity review resolved and passes a focused downstream compatibility branch.

leanVM's existing `formal/xmss/` project is not imported wholesale. At the target revision it
uses Lean `v4.31.0` and VCVio revision `cbd4144`; moving that reviewed security theorem onto this
repository's current dependency set is a deliberate port and statement/correspondence review,
not a reason to downgrade the root toolchain.
