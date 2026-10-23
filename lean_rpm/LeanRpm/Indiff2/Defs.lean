import LeanRpm.Transfer

/-!
# The two-oracle model: a hash `H` and a random function `F`

Besides the sponge, a protocol may call the permutation directly: leanVM's Fiat–Shamir duplex
(`crates/verifier/src/transcript.rs`) does. Its random-oracle-model proofs use two independent
oracles: a random oracle `H : Msg → Dg` for the sponge, and a random function `F : S → S` for the
direct calls (`hfSpec`). In the random-permutation model both are the permutation: `H` the
sponge over `π`, `F` the permutation `π` itself.

The game's oracles in the two-oracle model (`dSpec2`): coins, `H`, `π` and `π⁻¹` (the
adversary's), and `F` (the honest parties' direct calls).

* **The real world** (`realGame2`): `H = sponge^π`, `π`, `π⁻¹` and `F = π` for the lazily sampled
  random permutation.
* **The ideal world** (`idealGame2`): `H` and `F` independent random oracles, and `π`, `π⁻¹`
  answered by the simulator `simulator2`, which queries `H` and `F`: a fresh forward query at a
  rooted node whose path pads a message `m` gets `H m` completed by uniform bits; any other fresh
  forward query `π x` gets `F x`; a fresh inverse query a uniform state.

The two worlds are indistinguishable for games in which the honest parties' direct calls follow
a *duplex discipline* (`DuplexOK`): each call `F x` is at a state absorbing a non-final block
(`NF`, a block that no padding ends with) into the initial state or into an earlier answer of
`F`. Without such a discipline the ideal `F` cannot agree with the simulator at the end of a
sponge path, where the simulator must answer with `H`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace LeanRpm

/-- The random function of the two-oracle model: states to states. -/
abbrev fSpec (St : Type) : OracleSpec St := St →ₒ St

/-- The random oracles of the two-oracle model: `H` and `F`. -/
abbrev hfSpec (Msg Dg St : Type) := roSpec Msg Dg + fSpec St

/-- The game's oracles in the two-oracle model: coins, `H`, `π` and `π⁻¹`, and `F`. -/
abbrev dSpec2 (Msg Dg St : Type) := unifSpec + (roSpec Msg Dg + (permSpec St + fSpec St))

/-- The cost of a two-oracle query: a hash query costs its padded length in blocks, a
permutation query and a direct call cost one, a coin nothing. -/
def queryCost2 {Msg Dg Blk St : Type} (P : Padding Msg Blk) :
    (dSpec2 Msg Dg St).Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => (P.pad m).length
  | .inr (.inr _) => 1

section Setting

variable {Dg E C Msg : Type}
  [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpState Dg E C)

/-! ## The worlds -/

/-- The game's direct calls become permutation queries. -/
def toOne : QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
    (OracleComp (dSpec Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr (.inl m) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inl m)))
  | .inr (.inr (.inl q)) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inr q)))
  | .inr (.inr (.inr x)) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inr (.fwd x))))

/-- **The real world** of the two-oracle model: `F` is the random permutation. -/
noncomputable def realGame2 {α : Type} (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) :
    ProbComp α :=
  realGame P iv (simulateQ (toOne (E := E) (C := C)) D)

/-- An `H` query of the two-oracle ROM. -/
abbrev hQuery (m : Msg) : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) Dg :=
  hq (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl m)

/-- An `F` query of the two-oracle ROM. -/
abbrev fQuery (x : SpState Dg E C) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) (SpState Dg E C) :=
  hq (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x)

/-- The answer of the two-oracle simulator at a fresh rooted node `x` with path `β`: when `β`
pads a message `m`, `H m` completed by uniform bits; otherwise `F x`. -/
noncomputable def rootedAnswer2 (β : List (Dg × E)) (x : SpState Dg E C) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) (SpState Dg E C) :=
  match P.unpad β with
  | some m => do
    let d ← hQuery (E := E) (C := C) m
    let ec ← (liftM ($ᵗ (E × C)) : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
    pure ((d, ec.1), ec.2)
  | none => fQuery (Dg := Dg) x

/-- **The two-oracle simulator**: answers `π` and `π⁻¹` with oracle access to `H` and `F`. -/
noncomputable def simulator2 : QueryImpl (permSpec (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .fwd x => StateT.mk fun σ ↦
      match fwdLookup σ.edges x with
      | some y => pure (y, σ)
      | none =>
        match chainOf σ.chains x with
        | some (s, β) => do
          let y ← rootedAnswer2 P (β ++ [blockTo s x]) x
          pure (y, ⟨(x, y) :: σ.edges, (y, β ++ [blockTo s x]) :: σ.chains⟩)
        | none => do
          let y ← fQuery (Dg := Dg) x
          pure (y, ⟨(x, y) :: σ.edges, σ.chains⟩)
  | .inv y => StateT.mk fun σ ↦
      match invLookup σ.edges y with
      | some x => pure (x, σ)
      | none => do
        let x ← (liftM ($ᵗ (SpState Dg E C)) :
          OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
        pure (x, ⟨(x, y) :: σ.edges, σ.chains⟩)

/-- The ideal world of the two-oracle model: coins forwarded, `H` and `F` the random oracles,
`π` and `π⁻¹` the simulator. -/
noncomputable def idealImpl2 : QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
  | .inr (.inl m) => liftM (hQuery (Msg := Msg) (Dg := Dg) (E := E) (C := C) m)
  | .inr (.inr (.inl q)) => simulator2 P q
  | .inr (.inr (.inr x)) => liftM (fQuery (Msg := Msg) (Dg := Dg) x)

/-- **The ideal world** of the two-oracle model. -/
noncomputable def idealGame2 {α : Type} (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) :
    ProbComp α :=
  (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl
    ((simulateQ (idealImpl2 P) D).run' (SimState.init iv))).run' ∅

/-! ## The duplex discipline -/

/-- A direct call at `x` is admissible after the answers `hist` of earlier direct calls: `x`
absorbs a non-final block into the initial state or into an earlier answer. -/
def Admissible (NF : (Dg × E) → Prop) (hist : List (SpState Dg E C)) (x : SpState Dg E C) :
    Prop :=
  (x.2 = iv.2 ∧ NF (blockTo iv x)) ∨ ∃ y ∈ hist, x.2 = y.2 ∧ NF (blockTo y x)

/-- **The duplex discipline**: along every run, every direct call `F x` is admissible after the
answers of the earlier direct calls (`hist`, newest first). -/
def DuplexOK (NF : (Dg × E) → Prop) {α : Type} :
    OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α → List (SpState Dg E C) → Prop
  | .pure _, _ => True
  | .liftBind (.inr (.inr (.inr x))) k, hist =>
      Admissible iv NF hist x ∧ ∀ y, DuplexOK NF (k y) (y :: hist)
  | .liftBind _ k, hist => ∀ u, DuplexOK NF (k u) hist

end Setting

end LeanRpm
