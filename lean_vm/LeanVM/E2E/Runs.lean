/-
  LeanVM.E2E.Runs

  The runs of the signature schemes' verification: an `Option` run answered by a lookup is a
  run of the lazy random oracle from any cache agreeing with the lookup, and the monad-generic
  `Concrete.verify` of leanXMSS and leanSPHINCS is the simulation of its free run.
-/

module

public import LeanVM.Spec.NodeWith
public import LeanVM.Protocol.Compile.Rom.Log
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Answered runs and the schemes' verification

The end-to-end theorem's per-key reductions (T5 of `docs/roadmap/e2e-security.md`) start from a
signature valid under the random oracle's final log `ℓ`: the `Option` run
`xmssVerifyWith (look ℓ) pk m σ = some true` (`LeanVM.Spec.NodeWith`), every hash the
verification makes answered by the log. The schemes' security games (`LeanXmss.Security.gameCore`,
`Sphincs.Security.Det.gameCoreDet`) verify the forgery as a computation in `OracleComp HashSpec`
run with VCVio's lazy `randomOracle`, behind the counted oracle of their `experiment`. This module
connects the two.

## Answered runs are cached runs

If the `Option` simulation of `oa : OracleComp spec α` by a lookup `f` returns `some a`, every
query of that run is answered by `f`; so from a state at which an oracle answers every point `f`
answers, with `f`'s answer and without changing the state, the oracle's run of `oa` is `pure (a, s)`
(`run_simulateQ_of_answered`), and with the queries counted, `pure ((a, w), s)` for the run's cost
`w` (`run_simulateQ_withCost_of_answered`). For `randomOracle` such a state is any cache agreeing
with `f` wherever `f` answers (`run_simulateQ_randomOracle_of_answered`,
`run_simulateQ_withAddCost_liftM_of_answered` for the schemes' counted oracle, where the
verification is lifted into `unifSpec + HashSpec`).

## The schemes' verification is natural

`Concrete.verify` of both schemes is written for any monad with `HasQuery HashSpec`. Its run in a
lawful monad `m` with the query `impl` is `simulateQ impl` of its run in `OracleComp HashSpec`
(`Xmss.verify_eq_simulateQ`, `Sphincs.verify_eq_simulateQ`), proved helper by helper (the loops by
induction). So `xmssVerifyWith H` is `simulateQ (fun x ↦ digestBits <$> H x)` of the free run
(`xmssVerifyWith_eq_simulateQ`, `sphincsVerifyWith_eq_simulateQ`).

## Corollaries

* A signature valid under the log `ℓ`, verified with `randomOracle` from a cache holding `ℓ`
  (`CacheHas`), returns `true` and leaves the cache unchanged (`run_verify_of_xmssVerifyWith`,
  `run_verify_of_sphincsVerifyWith`); with the schemes' counted oracle, the final verification
  of their games returns `true` (`run_countedVerify_of_xmssVerifyWith`,
  `run_countedVerify_of_sphincsVerifyWith`).
* The `Option` run of the deployed hash is the deployed verification
  (`xmssVerifyWith_some_blake2s`, `sphincsVerifyWith_some_blake2s`).

The counted oracle is the schemes' `countedOracle` (`LeanXmss/Statement.lean`,
`Sphincs/Statement.lean`), `(unifFwdImpl HashSpec + randomOracle).withAddCost cost`; their
`Statement` modules are not modules of the module system, so the lemmas here are stated for any
`impl₁ + randomOracle` and any cost, and the tests apply them to `countedOracle`.
-/

namespace LeanVM.E2E

open OracleComp OracleSpec
open LeanVM.Node LeanVM.Protocol.Compile.Rom

@[expose] public section

/-! ## Answered runs -/

section Answered

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- **Answered runs are pure runs.** If the `Option` simulation of `oa` by the lookup `f` returns
`some a`, then an oracle `so` that, at the state `s`, answers every point `f` answers with `f`'s
answer and leaves `s` unchanged runs `oa` from `s` to `pure (a, s)`. -/
theorem run_simulateQ_of_answered {σ : Type} {n : Type → Type} [Monad n] [LawfulMonad n]
    (f : QueryImpl spec Option) (so : QueryImpl spec (StateT σ n)) (s : σ)
    (hso : ∀ t u, f t = some u → (so t).run s = pure (u, s)) :
    ∀ (oa : OracleComp spec α) (a : α), simulateQ f oa = some a →
      (simulateQ so oa).run s = pure (a, s) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro a h
    simp only [simulateQ_pure] at h
    cases h
    simp
  | query_bind t k ih =>
    intro a h
    simp only [simulateQ_bind, simulateQ_spec_query] at h ⊢
    cases hf : f t with
    | none => simp [hf] at h
    | some u =>
      rw [hf] at h
      rw [StateT.run_bind, hso t u hf, pure_bind]
      exact ih u a (by simpa using h)

/-- **Answered runs are pure runs, counted.** As `run_simulateQ_of_answered`, with every query
charged by `costFn` in a writer layer: the run returns `a` with some total cost `w` and leaves
the state unchanged. -/
theorem run_simulateQ_withCost_of_answered {σ ω : Type} [Monoid ω] {n : Type → Type} [Monad n]
    [LawfulMonad n] (f : QueryImpl spec Option) (so : QueryImpl spec (StateT σ n)) (s : σ)
    (costFn : spec.Domain → ω) (hso : ∀ t u, f t = some u → (so t).run s = pure (u, s)) :
    ∀ (oa : OracleComp spec α) (a : α), simulateQ f oa = some a →
      ∃ w, ((simulateQ (so.withCost costFn) oa).run).run s = pure ((a, w), s) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro a h
    simp only [simulateQ_pure] at h
    cases h
    exact ⟨1, by simp⟩
  | query_bind t k ih =>
    intro a h
    simp only [simulateQ_bind, simulateQ_spec_query] at h ⊢
    cases hf : f t with
    | none => simp [hf] at h
    | some u =>
      rw [hf] at h
      obtain ⟨w, hw⟩ := ih u a (by simpa using h)
      refine ⟨costFn t * w, ?_⟩
      simp [QueryImpl.withCost_apply, WriterT.run_bind, StateT.run_bind, hso t u hf, hw]

/-- A total lookup answered in a monad `n` through `pure` is the pure run of the total lookup. -/
theorem simulateQ_pure_comp (g : QueryImpl spec Id) {n : Type → Type} [Monad n] [LawfulMonad n] :
    ∀ oa : OracleComp spec α,
      simulateQ (fun t ↦ (pure (g t) : n (spec.Range t))) oa = pure (simulateQ g oa).run := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, pure_bind, ih]
    rfl

variable [DecidableEq ι] [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- The lazy random oracle, at a cache holding the answer `u` at `t`, answers `u` and keeps the
cache. -/
theorem run_randomOracle_of_cached {c : QueryCache spec} {t : spec.Domain} {u : spec.Range t}
    (h : c t = some u) : (spec.randomOracle t).run c = pure (u, c) := by
  rw [randomOracle.run_eq, h]

/-- **Answered runs are cached runs.** If the `Option` simulation of `oa` by `f` returns `some a`,
then from any cache agreeing with `f` wherever `f` answers, the lazy random oracle runs `oa` to
`pure (a, c)`: its support is `{(a, c)}`. -/
theorem run_simulateQ_randomOracle_of_answered (f : QueryImpl spec Option) (c : QueryCache spec)
    (hc : ∀ t u, f t = some u → c t = some u) (oa : OracleComp spec α) (a : α)
    (h : simulateQ f oa = some a) :
    (simulateQ spec.randomOracle oa).run c = pure (a, c) :=
  run_simulateQ_of_answered f _ c (fun t u hu ↦ run_randomOracle_of_cached (hc t u hu)) oa a h

/-- **Answered runs are cached runs, behind the counted oracle.** For `oa : OracleComp spec α`
lifted into `unifSpec + spec` and run with `(impl₁ + randomOracle).withAddCost costFn` (the
schemes' `countedOracle` at `impl₁ = unifFwdImpl spec` and their cost): if the `Option`
simulation of `oa` by `f` returns `some a`, then from any cache agreeing with `f` wherever `f`
answers, the run returns `a` with some cost `w` and leaves the cache unchanged. -/
theorem run_simulateQ_withAddCost_liftM_of_answered
    (impl₁ : QueryImpl unifSpec (StateT (QueryCache spec) ProbComp))
    (costFn : (unifSpec + spec).Domain → Nat) (f : QueryImpl spec Option) (c : QueryCache spec)
    (hc : ∀ t u, f t = some u → c t = some u) (oa : OracleComp spec α) (a : α)
    (h : simulateQ f oa = some a) :
    ∃ w, ((simulateQ (QueryImpl.withAddCost (impl₁ + spec.randomOracle) costFn)
      (liftM oa : OracleComp (unifSpec + spec) α)).run).run c = pure ((a, w), c) := by
  let f' : QueryImpl (unifSpec + spec) Option := (fun _ ↦ none : QueryImpl unifSpec Option) + f
  have h' : simulateQ f' (liftM oa : OracleComp (unifSpec + spec) α) = some a := by
    rw [QueryImpl.simulateQ_add_liftM_right]
    exact h
  refine run_simulateQ_withCost_of_answered f' (impl₁ + spec.randomOracle) c _ ?_ _ a h'
  rintro (t | t) u hu
  · simp [f'] at hu
  · exact run_randomOracle_of_cached (hc t u hu)

end Answered

/-! ## The naturality of leanXMSS's verification -/

namespace Xmss

open LeanXmss LeanXmss.Concrete

/-- leanXMSS's hash. -/
local notation "HS" => LeanXmss.HashSpec

/-- `sequenceFin` commutes with `simulateQ`. -/
theorem simulateQ_sequenceFin {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) {α : Type} :
    ∀ {n : Nat} (c : Fin n → OracleComp spec α),
      simulateQ impl (sequenceFin c) = sequenceFin fun i ↦ simulateQ impl (c i)
  | 0, _ => rfl
  | n + 1, c => by
    simp only [sequenceFin, simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin impl (n := n)]

variable {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl HS m)

/-- `oracleHash`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_oracleHash (x : HashInput) : simulateQ impl (oracleHash x : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; oracleHash x) := simulateQ_HasQuery_query impl x

/-- `tweakableHash`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_tweakableHash (p : PublicParameter) (d : HashDomain) (x : HashInput) :
    simulateQ impl (tweakableHash p d x : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; tweakableHash p d x) := by
  simp only [tweakableHash, simulateQ_bind, simulateQ_pure, simulateQ_oracleHash]

/-- `chainWalk`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_chainWalk (p : PublicParameter) (lay : Layer) (key : KeyIndex) (c : ChainIndex)
    (start : Nat) : ∀ (steps : Nat) (v : Digest),
    simulateQ impl (chainWalk p lay key c start steps v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; chainWalk p lay key c start steps v)
  | 0, _ => rfl
  | steps + 1, v => by
    simp only [chainWalk, simulateQ_bind, simulateQ_chainWalk p lay key c start steps v]
    congr 1
    funext prev
    split_ifs
    · exact simulateQ_tweakableHash impl _ _ _
    · rfl

/-- `recoverChain`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_recoverChain (p : PublicParameter) (lay : Layer) (key : KeyIndex) (c : ChainIndex)
    (d : Digit) (v : Digest) :
    simulateQ impl (recoverChain p lay key c d v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; recoverChain p lay key c d v) :=
  simulateQ_chainWalk impl _ _ _ _ _ _ _

/-- `leafHash`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_leafHash (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (e : ChainIndex → Digest) :
    simulateQ impl (leafHash p lay key e : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; leafHash p lay key e) :=
  simulateQ_tweakableHash impl _ _ _

/-- `messageDigest`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_messageDigest (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (msg : HashInput) (r : Randomness) :
    simulateQ impl (messageDigest p lay key msg r : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; messageDigest p lay key msg r) :=
  simulateQ_tweakableHash impl _ _ _

/-- `otsLeaf`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_otsLeaf (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (msg : HashInput) (r : Randomness) (values : ChainIndex → Digest) :
    simulateQ impl (otsLeaf p lay key msg r values : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; otsLeaf p lay key msg r values) := by
  simp only [otsLeaf, simulateQ_bind, simulateQ_messageDigest]
  congr 1
  funext digest
  split
  · simp only [simulateQ_bind, simulateQ_sequenceFin, simulateQ_recoverChain, simulateQ_leafHash,
      simulateQ_pure]
  · rfl

/-- `treeFold`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_treeFold (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) : ∀ (levels : Nat) (v : Digest),
    simulateQ impl (treeFold p lay key path levels v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; treeFold p lay key path levels v)
  | 0, _ => rfl
  | levels + 1, v => by
    simp only [treeFold, simulateQ_bind, simulateQ_treeFold p lay key path levels v]
    congr 1
    funext current
    split_ifs <;> exact simulateQ_tweakableHash impl _ _ _

/-- `layerRoot`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_layerRoot (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (msg : HashInput) (part : LayerSignature) :
    simulateQ impl (layerRoot p lay key msg part : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; layerRoot p lay key msg part) := by
  simp only [layerRoot, simulateQ_bind, simulateQ_otsLeaf]
  congr 1
  funext leaf
  split
  · simp only [simulateQ_bind, simulateQ_treeFold, simulateQ_pure]
  · rfl

/-- **The verification is natural**: run in a lawful monad `m` with the query `impl`, it is the
simulation by `impl` of its run in `OracleComp HashSpec` (the free query). -/
theorem verify_eq_simulateQ (pk : PublicKey) (msg : Message) (σ : Signature) :
    (letI : HasQuery HS m := ⟨impl⟩; Concrete.verify pk msg σ) =
    simulateQ impl (Concrete.verify pk msg σ : OracleComp HS Bool) := by
  symm
  simp only [Concrete.verify, simulateQ_bind, simulateQ_layerRoot]
  congr 1
  funext bottom
  split
  · simp only [simulateQ_bind, simulateQ_layerRoot]
    congr 1
    funext root
    split <;> rfl
  · rfl

end Xmss

/-! ## The naturality of leanSPHINCS's verification -/

namespace Sphincs

open _root_.Sphincs _root_.Sphincs.Concrete

/-- leanSPHINCS's hash. -/
local notation "HS" => _root_.Sphincs.HashSpec

/-- `sequenceFin` commutes with `simulateQ`. -/
theorem simulateQ_sequenceFin {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) {α : Type} :
    ∀ {n : Nat} (c : Fin n → OracleComp spec α),
      simulateQ impl (sequenceFin c) = sequenceFin fun i ↦ simulateQ impl (c i)
  | 0, _ => rfl
  | n + 1, c => by
    simp only [sequenceFin, simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin impl (n := n)]

variable {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl HS m)

/-- `oracleHash`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_oracleHash (x : HashInput) : simulateQ impl (oracleHash x : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; oracleHash x) := simulateQ_HasQuery_query impl x

/-- `tweakableHash`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_tweakableHash (p : PublicParameter) (d : HashDomain) (x : HashInput) :
    simulateQ impl (tweakableHash p d x : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; tweakableHash p d x) := by
  simp only [tweakableHash, simulateQ_bind, simulateQ_pure, simulateQ_oracleHash]

/-- `chainWalk`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_chainWalk (p : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (c : ChainIndex) (start : Nat) : ∀ (steps : Nat) (v : Digest),
    simulateQ impl (chainWalk p lay tree leaf c start steps v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; chainWalk p lay tree leaf c start steps v)
  | 0, _ => rfl
  | steps + 1, v => by
    simp only [chainWalk, simulateQ_bind, simulateQ_chainWalk p lay tree leaf c start steps v]
    congr 1
    funext prev
    split_ifs
    · exact simulateQ_tweakableHash impl _ _ _
    · rfl

/-- `recoverChain`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_recoverChain (p : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (c : ChainIndex) (d : Digit) (v : Digest) :
    simulateQ impl (recoverChain p lay tree leaf c d v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; recoverChain p lay tree leaf c d v) :=
  simulateQ_chainWalk impl _ _ _ _ _ _ _ _

/-- `leafHash`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_leafHash (p : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (e : ChainIndex → Digest) :
    simulateQ impl (leafHash p lay tree leaf e : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; leafHash p lay tree leaf e) :=
  simulateQ_tweakableHash impl _ _ _

/-- `encode`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_encode (p : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (msg : Digest) (ctr : Counter) :
    simulateQ impl (encode p lay tree leaf msg ctr : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; encode p lay tree leaf msg ctr) := by
  simp only [encode, simulateQ_bind, simulateQ_pure, simulateQ_tweakableHash]

/-- `otsLeaf`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_otsLeaf (p : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (msg : Digest) (ctr : Counter) (values : ChainIndex → Digest) :
    simulateQ impl (otsLeaf p lay tree leaf msg ctr values : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; otsLeaf p lay tree leaf msg ctr values) := by
  simp only [otsLeaf, simulateQ_bind, simulateQ_encode]
  congr 1
  funext enc
  split
  · simp only [simulateQ_bind, simulateQ_sequenceFin, simulateQ_recoverChain, simulateQ_leafHash,
      simulateQ_pure]
  · rfl

/-- `treeFold`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_treeFold (p : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) : ∀ (levels : Nat) (v : Digest),
    simulateQ impl (treeFold p lay tree leaf path levels v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; treeFold p lay tree leaf path levels v)
  | 0, _ => rfl
  | levels + 1, v => by
    simp only [treeFold, simulateQ_bind, simulateQ_treeFold p lay tree leaf path levels v]
    congr 1
    funext current
    split_ifs <;> exact simulateQ_tweakableHash impl _ _ _

/-- `forestWalk`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_forestWalk (p : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (i : FChain) (start : Nat) : ∀ (steps : Nat) (v : Digest),
    simulateQ impl (forestWalk p index c s j a i start steps v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; forestWalk p index c s j a i start steps v)
  | 0, _ => rfl
  | steps + 1, v => by
    simp only [forestWalk, simulateQ_bind, simulateQ_forestWalk p index c s j a i start steps v]
    congr 1
    funext prev
    split_ifs
    · exact simulateQ_tweakableHash impl _ _ _
    · rfl

/-- `childRecover`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_childRecover (p : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (word : Codeword) (values : FChain → Digest) :
    simulateQ impl (childRecover p index c s j a word values : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; childRecover p index c s j a word values) := by
  simp only [childRecover, childLeafHash, forestRecoverChain, simulateQ_bind, simulateQ_sequenceFin,
    simulateQ_forestWalk, simulateQ_tweakableHash]

/-- `subFold`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_subFold (p : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (path : Fin subHeight → Digest) : ∀ (levels : Nat) (v : Digest),
    simulateQ impl (subFold p index c s j a path levels v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; subFold p index c s j a path levels v)
  | 0, _ => rfl
  | levels + 1, v => by
    simp only [subFold, simulateQ_bind, simulateQ_subFold p index c s j a path levels v]
    congr 1
    funext current
    split_ifs
    · exact simulateQ_tweakableHash impl _ _ _
    · exact simulateQ_tweakableHash impl _ _ _
    · rfl

/-- `topFold`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_topFold (p : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (path : Fin topHeight → Digest) : ∀ (levels : Nat) (v : Digest),
    simulateQ impl (topFold p index c s path levels v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; topFold p index c s path levels v)
  | 0, _ => rfl
  | levels + 1, v => by
    simp only [topFold, simulateQ_bind, simulateQ_topFold p index c s path levels v]
    congr 1
    funext current
    split_ifs
    · exact simulateQ_tweakableHash impl _ _ _
    · exact simulateQ_tweakableHash impl _ _ _
    · rfl

/-- `coordRecover`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_coordRecover (p : PublicParameter) (index : Index) (c : Coord) (mark : CoordMark)
    (opening : CoordOpening) :
    simulateQ impl (coordRecover p index c mark opening : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; coordRecover p index c mark opening) := by
  simp only [coordRecover, superHash, simulateQ_bind, simulateQ_sequenceFin, simulateQ_childRecover,
    simulateQ_subFold, simulateQ_topFold, simulateQ_tweakableHash, simulateQ_pure]

/-- `forestRecover`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_forestRecover (p : PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (opening : Coord → CoordOpening) :
    simulateQ impl (forestRecover p index marks opening : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; forestRecover p index marks opening) := by
  simp only [forestRecover, simulateQ_bind, simulateQ_sequenceFin, simulateQ_coordRecover,
    simulateQ_tweakableHash]

/-- `messageDigest`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_messageDigest (p : PublicParameter) (root : Digest) (msg : Message)
    (r : Randomness) :
    simulateQ impl (messageDigest p root msg r : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; messageDigest p root msg r) := by
  simp only [messageDigest, messageDigestCall, simulateQ_bind, simulateQ_pure, simulateQ_oracleHash]

/-- `verifyLayers`'s free run, simulated by `impl`, is its run with the query `impl`. -/
theorem simulateQ_verifyLayers (p : PublicParameter) (index : Index) (σ : Signature) :
    ∀ (remaining : Nat) (v : Digest),
    simulateQ impl (verifyLayers p index σ remaining v : OracleComp HS _) =
    (letI : HasQuery HS m := ⟨impl⟩; verifyLayers p index σ remaining v)
  | 0, _ => rfl
  | remaining + 1, v => by
    simp only [verifyLayers]
    split_ifs
    · simp only [simulateQ_bind, simulateQ_otsLeaf]
      congr 1
      funext leaf
      split
      · simp only [simulateQ_bind, simulateQ_treeFold, simulateQ_verifyLayers p index σ remaining]
      · rfl
    · rfl

/-- **The verification is natural**: run in a lawful monad `m` with the query `impl`, it is the
simulation by `impl` of its run in `OracleComp HashSpec` (the free query). -/
theorem verify_eq_simulateQ (pk : PublicKey) (msg : Message) (σ : Signature) :
    (letI : HasQuery HS m := ⟨impl⟩; Concrete.verify pk msg σ) =
    simulateQ impl (Concrete.verify pk msg σ : OracleComp HS Bool) := by
  symm
  simp only [Concrete.verify, simulateQ_bind, simulateQ_messageDigest, simulateQ_forestRecover,
    simulateQ_verifyLayers]
  congr 1
  funext digest
  congr 1
  funext fts
  congr 1
  funext root
  split <;> rfl

end Sphincs

/-! ## The `…With` verifications and the random oracle -/

section With

open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier

section Natural

variable {m : Type → Type} [Monad m] [LawfulMonad m] (H : List UInt8 → m Digest)

/-- **`xmssVerifyWith H` is the free verification simulated by `H`**, its digests read as bits. -/
theorem xmssVerifyWith_eq_simulateQ (pk : LeanXmss.PublicKey) (msg : LeanXmss.Message)
    (σ : LeanXmss.Signature) :
    xmssVerifyWith H pk msg σ =
      simulateQ (fun x ↦ Node.digestBits <$> H x : QueryImpl LeanXmss.HashSpec m)
        (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) :=
  Xmss.verify_eq_simulateQ _ pk msg σ

/-- **`sphincsVerifyWith H` is the free verification simulated by `H`**, its digests read as
bits. -/
theorem sphincsVerifyWith_eq_simulateQ (pk : _root_.Sphincs.PublicKey)
    (msg : _root_.Sphincs.Message) (σ : _root_.Sphincs.Signature) :
    sphincsVerifyWith H pk msg σ =
      simulateQ (fun x ↦ Node.digestBits <$> H x : QueryImpl _root_.Sphincs.HashSpec m)
        (_root_.Sphincs.Concrete.verify pk msg σ : OracleComp _root_.Sphincs.HashSpec Bool) :=
  Sphincs.verify_eq_simulateQ _ pk msg σ

end Natural

/-- **The `Option` run of the deployed hash is the deployed leanXMSS verification.** -/
theorem xmssVerifyWith_some_blake2s (pk : LeanXmss.PublicKey) (msg : LeanXmss.Message)
    (σ : LeanXmss.Signature) :
    xmssVerifyWith (fun x ↦ some (blake2sBytes x)) pk msg σ = some (xmssVerify pk msg σ) := by
  rw [xmssVerifyWith_eq_simulateQ]
  exact (simulateQ_pure_comp (n := Option) (blake2sBits : QueryImpl LeanXmss.HashSpec Id) _).trans
    (congrArg (fun r : Id Bool ↦ some r.run) (Xmss.verify_eq_simulateQ (m := Id) _ pk msg σ).symm)

/-- **The `Option` run of the deployed hash is the deployed leanSPHINCS verification.** -/
theorem sphincsVerifyWith_some_blake2s (pk : _root_.Sphincs.PublicKey)
    (msg : _root_.Sphincs.Message) (σ : _root_.Sphincs.Signature) :
    sphincsVerifyWith (fun x ↦ some (blake2sBytes x)) pk msg σ = some (sphincsVerify pk msg σ) := by
  rw [sphincsVerifyWith_eq_simulateQ]
  exact (simulateQ_pure_comp (n := Option) (blake2sBits : QueryImpl _root_.Sphincs.HashSpec Id)
    _).trans (congrArg (fun r : Id Bool ↦ some r.run)
      (Sphincs.verify_eq_simulateQ (m := Id) _ pk msg σ).symm)

/-- The schemes' hash, `List UInt8 →ₒ BitVec 256` (`LeanXmss.HashSpec`, `Sphincs.HashSpec`). -/
abbrev BitsSpec : OracleSpec (List UInt8) := List UInt8 →ₒ BitVec 256

/-- **The cache `c` holds the answers of `H`** (for the random oracle's log `ℓ`, `H = look ℓ`):
every input `H` answers, `c` answers, with the digest's bits. -/
def CacheHas (c : QueryCache BitsSpec) (H : List UInt8 → Option Digest) : Prop :=
  ∀ x d, H x = some d → c x = some (Node.digestBits d)

/-- The cache of the answers of `H`, read as bits. -/
def bitsCache (H : List UInt8 → Option Digest) : QueryCache BitsSpec :=
  QueryCache.ofFn fun x ↦ Node.digestBits <$> H x

/-- The cache of `H`'s answers holds them. -/
theorem cacheHas_bitsCache (H : List UInt8 → Option Digest) : CacheHas (bitsCache H) H := by
  intro x d h
  simp [bitsCache, h]

/-- A cache holding the answers of `H` agrees with the bit lookup of `H` wherever it answers. -/
theorem CacheHas.answers {c : QueryCache BitsSpec} {H : List UInt8 → Option Digest}
    (hc : CacheHas c H) :
    ∀ t u, (Node.digestBits <$> H t : Option (BitVec 256)) = some u → c t = some u := by
  intro t u h
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
  exact hc t d hd

variable {H : List UInt8 → Option Digest} {c : QueryCache BitsSpec}

/-- **A leanXMSS signature valid under the answers `H` (the log) verifies with the lazy random
oracle from a cache holding them**: the run returns `true` and leaves the cache unchanged. -/
theorem run_verify_of_xmssVerifyWith (hc : CacheHas c H) {pk : LeanXmss.PublicKey}
    {msg : LeanXmss.Message} {σ : LeanXmss.Signature} (h : xmssVerifyWith H pk msg σ = some true) :
    (simulateQ (randomOracle : QueryImpl LeanXmss.HashSpec
        (StateT (QueryCache LeanXmss.HashSpec) ProbComp))
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool)).run c =
      pure (true, c) :=
  run_simulateQ_randomOracle_of_answered _ c hc.answers _ true
    ((xmssVerifyWith_eq_simulateQ H pk msg σ).symm.trans h)

/-- **A leanSPHINCS signature valid under the answers `H` (the log) verifies with the lazy random
oracle from a cache holding them**: the run returns `true` and leaves the cache unchanged. -/
theorem run_verify_of_sphincsVerifyWith (hc : CacheHas c H) {pk : _root_.Sphincs.PublicKey}
    {msg : _root_.Sphincs.Message} {σ : _root_.Sphincs.Signature}
    (h : sphincsVerifyWith H pk msg σ = some true) :
    (simulateQ (randomOracle : QueryImpl _root_.Sphincs.HashSpec
        (StateT (QueryCache _root_.Sphincs.HashSpec) ProbComp))
      (_root_.Sphincs.Concrete.verify pk msg σ : OracleComp _root_.Sphincs.HashSpec Bool)).run c =
      pure (true, c) :=
  run_simulateQ_randomOracle_of_answered _ c hc.answers _ true
    ((sphincsVerifyWith_eq_simulateQ H pk msg σ).symm.trans h)

/-- **The final verification of leanXMSS's game returns `true`.** A signature valid under the
answers `H` (the log), verified as `LeanXmss.Security.gameCore` verifies the forgery (lifted into
`OracleWorld`) behind the counted oracle (`countedOracle` at `impl₁ = unifFwdImpl HashSpec`) from a
cache holding them, returns `true` with some cost and leaves the cache unchanged. -/
theorem run_countedVerify_of_xmssVerifyWith
    (impl₁ : QueryImpl unifSpec (StateT (QueryCache LeanXmss.HashSpec) ProbComp))
    (costFn : LeanXmss.OracleWorld.Domain → Nat) (hc : CacheHas c H) {pk : LeanXmss.PublicKey}
    {msg : LeanXmss.Message} {σ : LeanXmss.Signature} (h : xmssVerifyWith H pk msg σ = some true) :
    ∃ w, ((simulateQ (QueryImpl.withAddCost (impl₁ + (randomOracle : QueryImpl LeanXmss.HashSpec
        (StateT (QueryCache LeanXmss.HashSpec) ProbComp))) costFn)
      (liftM (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) :
        OracleComp LeanXmss.OracleWorld Bool)).run).run c = pure ((true, w), c) :=
  run_simulateQ_withAddCost_liftM_of_answered impl₁ costFn _ c hc.answers _ true
    ((xmssVerifyWith_eq_simulateQ H pk msg σ).symm.trans h)

/-- **The final verification of leanSPHINCS's game returns `true`.** A signature valid under the
answers `H` (the log), verified as `Sphincs.Security.Det.gameCoreDet` verifies the forgery (lifted
into `OracleWorld`) behind the counted oracle (`countedOracle` at `impl₁ = unifFwdImpl HashSpec`)
from a cache holding them, returns `true` with some cost and leaves the cache unchanged. -/
theorem run_countedVerify_of_sphincsVerifyWith
    (impl₁ : QueryImpl unifSpec (StateT (QueryCache _root_.Sphincs.HashSpec) ProbComp))
    (costFn : _root_.Sphincs.OracleWorld.Domain → Nat) (hc : CacheHas c H)
    {pk : _root_.Sphincs.PublicKey} {msg : _root_.Sphincs.Message} {σ : _root_.Sphincs.Signature}
    (h : sphincsVerifyWith H pk msg σ = some true) :
    ∃ w, ((simulateQ (QueryImpl.withAddCost (impl₁ + (randomOracle : QueryImpl
        _root_.Sphincs.HashSpec (StateT (QueryCache _root_.Sphincs.HashSpec) ProbComp))) costFn)
      (liftM (_root_.Sphincs.Concrete.verify pk msg σ : OracleComp _root_.Sphincs.HashSpec Bool) :
        OracleComp _root_.Sphincs.OracleWorld Bool)).run).run c = pure ((true, w), c) :=
  run_simulateQ_withAddCost_liftM_of_answered impl₁ costFn _ c hc.answers _ true
    ((sphincsVerifyWith_eq_simulateQ H pk msg σ).symm.trans h)

end With

end
end LeanVM.E2E
