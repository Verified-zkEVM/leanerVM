import Common.Sponge
import Common.RomComm

/-!
# Indifferentiability: the two worlds and the simulator

The setting is the abstract sponge of `Common.Sponge` over states `(Dg × E) × C` (rate `Dg × E`,
digest `Dg`, capacity `C`), a padding `P` of messages `Msg` into rate blocks, and an initial state
`iv`.

A *distinguisher* is an oracle computation `D : OracleComp (dSpec Msg Dg St) α` with three kinds
of query (`dSpec`): uniform coins, the hash `H m`, and the permutation `π x`, `π⁻¹ y`.

* **The real world** (`realGame`): `π` is the lazily sampled random permutation `lazyPerm`, and
  `H` is the sponge over it (`spongeWith P iv π`), sharing its state.
* **The ideal world** (`idealGame`): `H` is a lazily sampled random oracle `Msg → Dg`
  (`romImpl`), and `π`, `π⁻¹` are answered by the simulator `simulator P`, which queries the
  random oracle.

## The simulator

The simulator (Bertoni, Daemen, Peeters, Van Assche, EUROCRYPT 2008, Section 4) keeps the
edges `(x, y)` it has answered (`SimState.edges`) and the *rooted* states with their paths
(`SimState.chains`): the initial state `iv` with the empty path, and every answer `y` to a
forward query at a rooted node, with the node's path. A state `x` is a rooted node when its
capacity equals the capacity of some rooted state `s` with path `β`; its path is then
`β ++ [B]` with `B = blockTo s x` the block taking `s` to `x` (`chainOf`). A fresh forward query
at a rooted node whose path is the padding of a message `m` is answered with the random oracle's
`H m` as digest, completed by uniform bits (`rootedAnswer`); any other fresh query, forward or
inverse, is answered uniformly. Answers are recorded and repeated queries answered from the
records, in both directions.
-/

open OracleComp OracleSpec

namespace Common

/-- The random oracle `Msg → Dg`. -/
abbrev roSpec (Msg Dg : Type) : OracleSpec Msg := Msg →ₒ Dg

/-- The distinguisher's oracles: uniform coins, the hash `H : Msg → Dg`, and the permutation
`π` and its inverse. -/
abbrev dSpec (Msg Dg St : Type) := unifSpec + (roSpec Msg Dg + permSpec St)

/-- The cost of a distinguisher query: a hash query costs the number of blocks of its padded
message (the permutation calls the sponge makes), a permutation query costs one, a coin costs
nothing. -/
def queryCost {Msg Dg Blk St : Type} (P : Padding Msg Blk) :
    (dSpec Msg Dg St).Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => (P.pad m).length
  | .inr (.inr _) => 1

section Setting

variable {Dg E C Msg : Type}
  [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]

/-! ## The real world -/

/-- The real world: coins forwarded, `H` the sponge over the lazy random permutation, `π` and
`π⁻¹` the lazy random permutation. -/
noncomputable def realImpl (P : Padding Msg (Dg × E)) (iv : SpState Dg E C) :
    QueryImpl (dSpec Msg Dg (SpState Dg E C)) (StateT (PermLog (SpState Dg E C)) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl m) => spongeWith P iv (fun x ↦ lazyPerm (.fwd x)) m
  | .inr (.inr q) => lazyPerm q

/-- **The real world** run of a distinguisher, from the empty permutation. -/
noncomputable def realGame (P : Padding Msg (Dg × E)) (iv : SpState Dg E C) {α : Type}
    (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) : ProbComp α :=
  (simulateQ (realImpl P iv) D).run' []

/-! ## The simulator and the ideal world -/

/-- The simulator's state: the edges it has answered, newest first, and the rooted states with
their paths, newest first, ending with the initial state and the empty path. -/
structure SimState (Dg E C : Type) where
  /-- The answered edges `(x, π x)`, newest first. -/
  edges : PermLog (SpState Dg E C)
  /-- The rooted states with their block paths, newest first. -/
  chains : List (SpState Dg E C × List (Dg × E))

/-- The initial simulator state: no edges, and the initial state rooted at the empty path. -/
def SimState.init (iv : SpState Dg E C) : SimState Dg E C := ⟨[], [(iv, [])]⟩

/-- The rooted state whose capacity is that of `x`, with its path: the first such chain. -/
def chainOf (VC : List (SpState Dg E C × List (Dg × E))) (x : SpState Dg E C) :
    Option (SpState Dg E C × List (Dg × E)) :=
  VC.find? fun p ↦ decide (p.1.2 = x.2)

/-- The answer of the simulator at a fresh rooted node with path `β`: when `β` pads a message `m`,
the random oracle's digest `H m` completed by uniform bits; otherwise a uniform state. -/
noncomputable def rootedAnswer (P : Padding Msg (Dg × E)) (β : List (Dg × E)) :
    OracleComp (unifSpec + roSpec Msg Dg) (SpState Dg E C) :=
  match P.unpad β with
  | some m => do
    let d ← ((roSpec Msg Dg).query m : OracleComp (unifSpec + roSpec Msg Dg) Dg)
    let ec ← (liftM ($ᵗ (E × C)) : OracleComp (unifSpec + roSpec Msg Dg) (E × C))
    pure ((d, ec.1), ec.2)
  | none => liftM ($ᵗ (SpState Dg E C))

/-- **The simulator** (Bertoni et al., EUROCRYPT 2008): answers `π` and `π⁻¹` with oracle access
to the random oracle `H`. -/
noncomputable def simulator (P : Padding Msg (Dg × E)) :
    QueryImpl (permSpec (SpState Dg E C))
      (StateT (SimState Dg E C) (OracleComp (unifSpec + roSpec Msg Dg)))
  | .fwd x => StateT.mk fun σ ↦
      match fwdLookup σ.edges x with
      | some y => pure (y, σ)
      | none =>
        match chainOf σ.chains x with
        | some (s, β) => do
          let y ← rootedAnswer P (β ++ [blockTo s x])
          pure (y, ⟨(x, y) :: σ.edges, (y, β ++ [blockTo s x]) :: σ.chains⟩)
        | none => do
          let y ← (liftM ($ᵗ (SpState Dg E C)) : OracleComp (unifSpec + roSpec Msg Dg) _)
          pure (y, ⟨(x, y) :: σ.edges, σ.chains⟩)
  | .inv y => StateT.mk fun σ ↦
      match invLookup σ.edges y with
      | some x => pure (x, σ)
      | none => do
        let x ← (liftM ($ᵗ (SpState Dg E C)) : OracleComp (unifSpec + roSpec Msg Dg) _)
        pure (x, ⟨(x, y) :: σ.edges, σ.chains⟩)

/-- The ideal world: coins forwarded, `H` the random oracle, `π` and `π⁻¹` the simulator. -/
noncomputable def idealImpl (P : Padding Msg (Dg × E)) :
    QueryImpl (dSpec Msg Dg (SpState Dg E C))
      (StateT (SimState Dg E C) (OracleComp (unifSpec + roSpec Msg Dg)))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + roSpec Msg Dg) _)
  | .inr (.inl m) => liftM ((roSpec Msg Dg).query m : OracleComp (unifSpec + roSpec Msg Dg) Dg)
  | .inr (.inr q) => simulator P q

/-- **The ideal world** run of a distinguisher: the simulator from its initial state, the random
oracle from the empty cache. -/
noncomputable def idealGame (P : Padding Msg (Dg × E)) (iv : SpState Dg E C) {α : Type}
    (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) : ProbComp α :=
  (simulateQ (roSpec Msg Dg).romImpl ((simulateQ (idealImpl P) D).run' (SimState.init iv))).run' ∅

end Setting

end Common
