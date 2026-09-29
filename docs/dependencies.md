# Dependency policy

The repository tracks eight upstreams and six direct Lake packages:

| Component | Tracked ref | Role |
| --- | --- | --- |
| Lean | `v4.34.1` | Root toolchain |
| Mathlib | `v4.34.1` (`d13f23b7`) | Algebra, finite types, probability measures, and tactics |
| leanVM | `a386121f84292f6fa663aaa3e570c15bc0240ea2` | Audited Rust/specification target; not a Lake dependency |
| CompPoly | `572f997390aa4fc131ef30b1186fa1dcf292ca10` (current main) | Computable polynomial and field infrastructure |
| Clean | `42fe4b268132a46604d40cc73f642a1995f26547` (PR #474, includes current main) | Circuit, AIR, channel, and witness-generation infrastructure |
| ArkLib | `7653a901ed466c88a2e61a3075011b73d7bb2316` (current main) | Oracle reductions, security definitions, composition, sumcheck, and multilinear theory |
| VCVio | `a4232d084aa18aa71f75b92b64082b457ffdb77b` (compatibility fix over current main) | Native probability measures and oracle computation security carriers |
| PolyFun | `41d3b21dcc99817fe4f9f24ca7b2b58f0578083d` (current main) | Polynomial functors and free monads underlying oracle computations |

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

## Lean 4.34 port review

The previous baseline was Lean `v4.33.1`, CompPoly `3468b38c`, ArkLib `dca90385`, and Clean
`93c9d1ef`. Lean `v4.34.1` is the patch release in the requested 4.34 series. Compiled artifacts
from `v4.34.0` have incompatible headers, so Mathlib is now an explicit root requirement at
`v4.34.1`. Existing first-party consumers include `LeanerVM.Parameters.Generator` and the
polynomial and probability bridges under `LeanerVM.Protocol`. This requirement overrides the
`v4.34.0` Mathlib requirements inherited from CompPoly and ArkLib.

Regenerate the graph with `lake update`, then fetch matching artifacts with
`lake exe cache get`. Do not use `lake --keep-toolchain update`: in Lake 4.34 that option also
changes dependency traversal, allowing inherited manifests to resolve a package before later
root requirements. Check the resolved revisions in the manifest after an update.

CompPoly's current main revision overrides ArkLib's `v4.34.0` CompPoly requirement. The
complete first-party import cone must be compiled against that single resolved revision.
`BF64` is now a structure wrapping `BitVec 64`, with characteristic-two natural-number casts:
`(2 : K) = 0`. Encoded words use `K.ofBits n = BF64.ofBitVec (BitVec.ofNat 64 n)` instead.
The generator remains the encoded word `0x2`; BLAKE2s cells, Clean's `val`/`fromNat` interface,
protocol fixtures, and exported Rust contract fixtures retain their original bit coordinates.
Regression tests distinguish casts from encoded words explicitly. `DecidableEq K` compares bit
coordinates through an equivalence proof: the upstream derived wrapper instance makes kernel
checks of computed words stall on dependent transport. The existing register-equality
regression checks this boundary without unchecked evaluation. The `Fintype K` instance is
proof-only; executable samplers use coordinate equivalences without enumerating `2^64` words.

ArkLib's current source supplies native dependent composition and computable sumcheck as well
as the security definitions migrated to VCVio's native measure API. The guarded
verdict, guarded append, and uniform counting bridges use `Pr{let x ← computation}[P x]`
and native event lemmas. Their relations, extraction conditions, and error bounds are retained.
The retired `Pr[P | computation]` interface is no longer used by first-party probability proofs.
Review these statement changes alongside the kernel audit, rather than relying on successful
elaboration alone.

Clean is pinned to the compatibility commit in [PR #474](https://github.com/Verified-zkEVM/clean/pull/474),
with current Clean main (`fba2a29f`) merged into the compatibility branch. Mathlib 4.34 rejects
`ring_nf at ih'` in
`Clean.Air.Balance.balanceOf_active_append_eq` because normalization makes no progress at that
hypothesis. The fix applies the induction equality under addition explicitly and proves the
reassociation goals with `ring`, retaining the theorem statement and assumptions. The affected
Clean import cone is built under the root Lean 4.34.1 toolchain; Clean CI checks the branch under
its own toolchain. The published commit is pinned directly; local package overrides must never
be written into the committed manifest.

VCVio's query-log counting bridge needs one proof adjustment for current PolyFun's sealed
free-monoid trace interface. The compatibility commit in [VCVio #820](https://github.com/Verified-zkEVM/VCVio/pull/820)
over `f5119c64` normalizes the target to
list counting before induction, retaining the theorem statement. The complete source file is
checked against both PolyFun `3710d71b` and current `41d3b21d` under Lean 4.34.1.

## Dependency boundaries

CompPoly supplies leanVM's fields (see [leanvm-target.md](leanvm-target.md)):

- `K = GF(2^64)`: `CompPoly.Fields.Binary.BF64`, the flat quotient
  `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)` on a computable polynomial-basis carrier, with
  Rabin-certified irreducibility;
- `E = GF(2^192)`: `CompPoly.Fields.Binary.BF64.Ext3`, the cubic extension
  `K[y]/(y^3 + y + 1)` on a `Vector BF64 3` carrier via `CompPoly.Fields.Extension`.

ArkLib's Lake package name is `Arklib`, which is what the `[[require]]` must say. Its first
consumer is `LeanerVM/Protocol/Field.lean`. VCVio is an explicit root requirement because
`LeanerVM/Protocol/ToArkLib/KnowledgeAppend.lean` and the probability bridges consume its native
measure and security interfaces. PolyFun is an explicit root requirement for the free-monad carrier of the oracle computations
used by `LeanerVM/Protocol/ToArkLib/Oracles.lean` through VCVio.
These requirements select current source over the older revisions in inherited manifests.
ArkLib also brings cslib, checkdecls, and doc-gen4's dependencies into the graph. Tooling and
Mathlib-owned transitive packages retain the revisions selected by those upstream manifests.
The historical consumer table and trust ledger
are in [roadmap/protocol-blueprint.md](roadmap/protocol-blueprint.md). Upstream admitted results
are not proof evidence: the first-party kernel axiom audit rejects `sorryAx` transitively,
including through upstream theorems. ArkLib's own axiom baseline is an allowlist, not a proof.

Package-level `leanOptions.warningAsError = true` rejects every first-party elaboration warning,
including imported production and test leaves. Tests deliberately remain classic and their
library has `allowNonModules = true` for full-body kernel checks; this does not relax
elaboration warning errors. CI and `scripts/validate.sh` use plain
`lake build` so Lake's dependency release-lookup warnings do not fail the build.
`scripts/test-warning-policy.py` verifies both positive builds and planted imported-leaf
warnings; it does not change upstream options. Mathlib's artifacts come from
`lake exe cache get` before building, since compiling all of Mathlib does not fit CI's time limit.
CompPoly's current source may have no matching release archive; its affected source is rebuilt
under the root Lean patch version.

Clean's first consumers are the leanISA table components and the `FiniteField BF64` instance
in [roadmap/leanisa-blueprint.md](roadmap/leanisa-blueprint.md). Its core is generic over
`FiniteField F`; its `ZMod p` gadget tree is not used. Two limitations remain: push and pull
multiplicities `±1` coincide in characteristic two, and `Expression` has no degree bound.
Clean's pinned source and first-party Clean bridges now use Lean's module system; the
historical import restriction C8 no longer applies. Message-flattening proofs use Clean's
public normalization lemmas for its now sealed struct conversions. Small literal row equations
in the witness tests unfold those conversions explicitly; block equations compare rows
pointwise before applying `List.ofFn`, avoiding enumeration of the `2^16`-row memory block. See
[CONTRIBUTING.md](../CONTRIBUTING.md) and the historical finding C8 in
[roadmap/leanisa-status.md](roadmap/leanisa-status.md).

leanVM's existing `formal/xmss/` project is not imported wholesale. At the target revision it
uses Lean `v4.31.0` and VCVio revision `cbd4144`; moving that reviewed security theorem onto this
repository's dependency set requires a deliberate port and statement/correspondence review.
