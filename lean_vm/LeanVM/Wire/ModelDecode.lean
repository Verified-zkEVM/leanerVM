/-
  LeanVM.Wire.ModelDecode

  Decoding an honest proof's bytes hashes only inputs its paths climb through: the decoding with a
  hash that logs its inputs logs only `climbInput`s of the proof, and returns what the decoding
  with the bare hash returns.
-/

module

public import LeanVM.Wire.RoundTrip
public import LeanVM.Wire.CompleteSpec
import LeanVM.Wire.UnpruneList

/-!
# The hash inputs of decoding

For a proof that survives its encoding with `h` (`WireDecodable h proof`), decoding its bytes with
`h` that also logs `g x` for each input `x` (`tagHash g h`) returns the decoding with `h`, and logs
only `g (climbInput h path level)` for paths of the proof and levels up to their length
(`logsIn_fromBytesWithHash`): the leaves' bytes, at level `0`, and at each level of the climb each
parent's input, a node and its sibling as the path through it climbs (`parentInput_eq`). The climb's
invariant is rtunprune's (`NodesAt`, `climbLevel_spec`, `LeanVM/Wire/Unprune.lean`); the parent's
input is `parentDigest_eq`'s argument one hash earlier.

`LogsIn P c v`: the logging computation `c` returns `v` from every log and appends only entries
satisfying `P`.
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-! ## Logging computations -/

section Logs

variable {γ : Type} (P : γ → Prop)

/-- The logging computation `c` returns `v` from every log and appends only entries in `P`. -/
def LogsIn {α : Type} (c : StateM (List γ) α) (v : α) : Prop :=
  ∀ l₀, ∃ d, c.run l₀ = (v, l₀ ++ d) ∧ ∀ y ∈ d, P y

variable {P}

theorem LogsIn.pure' {α : Type} (v : α) : LogsIn P (pure v) v :=
  fun l₀ ↦ ⟨[], by simp; rfl, by simp⟩

theorem LogsIn.bind' {α β : Type} {c : StateM (List γ) α} {X : Id α}
    {k : α → StateM (List γ) β} {k' : α → Id β} (hc : LogsIn P c X)
    (hk : LogsIn P (k X) (k' X)) : LogsIn P (c >>= k) (X >>= k') := by
  intro l₀
  obtain ⟨d₁, h₁, hd₁⟩ := hc l₀
  obtain ⟨d₂, h₂, hd₂⟩ := hk (l₀ ++ d₁)
  refine ⟨d₁ ++ d₂, ?_, fun y hy ↦ (List.mem_append.1 hy).elim (hd₁ y) (hd₂ y)⟩
  rw [← List.append_assoc, StateT.run_bind, h₁]
  exact h₂

theorem LogsIn.mapM' {α β : Type} {f : α → StateM (List γ) β} {f' : α → Id β} :
    ∀ {l : List α}, (∀ a ∈ l, LogsIn P (f a) (f' a)) → LogsIn P (l.mapM f) (l.mapM f')
  | [], _ => LogsIn.pure' _
  | a :: l, h => by
    simp only [List.mapM_cons]
    exact LogsIn.bind' (h a List.mem_cons_self) (LogsIn.bind'
      (LogsIn.mapM' fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) (LogsIn.pure' _))

theorem LogsIn.mono {α : Type} {Q : γ → Prop} {c : StateM (List γ) α} {v : α} (h : LogsIn P c v)
    (hPQ : ∀ y, P y → Q y) : LogsIn Q c v := fun l₀ ↦
  let ⟨d, hc, hd⟩ := h l₀
  ⟨d, hc, fun y hy ↦ hPQ y (hd y hy)⟩

end Logs

/-- The hash `h`, logging `g x` for its input `x`. -/
def tagHash {γ : Type} (g : Bytes → γ) (h : Bytes → Digest) (x : Bytes) :
    StateM (List γ) Digest := do
  modify (· ++ [g x])
  pure (h x)

theorem logsIn_tagHash {γ : Type} {P : γ → Prop} (g : Bytes → γ) (h : Bytes → Digest) {x : Bytes}
    (hx : P (g x)) : LogsIn P (tagHash g h x) (h x) :=
  fun l₀ ↦ ⟨[g x], rfl, by simpa using hx⟩

/-! ## The climb's inputs -/

/-- The bytes `climbLevel` hashes for the parent of `node`, its digest `digest` and its sibling. -/
def parentInput (node : ℕ) (digest sibling : Digest) : Bytes :=
  if node % 2 = 0 then digestBytes digest ++ digestBytes sibling
  else digestBytes sibling ++ digestBytes digest

theorem parentDigest_eq_parentInput (h : Bytes → Digest) (node : ℕ) (digest sibling : Digest) :
    parentDigest h node digest sibling = h (parentInput node digest sibling) := by
  unfold parentDigest parentInput
  split <;> rfl

/-- `climbLevel` with any hash, in the explicit form of `climbLevelWithHash_id`. -/
theorem climbLevelWithHash_eq {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
    (nodes carried : List (ℕ × Digest)) :
    climbLevelWithHash H nodes carried = (do
      let parents ← (nodes.filter fun x ↦ x.1 % 2 = 0 ∨ x.1 ^^^ 1 ∉ nodes.map Prod.fst).mapM
        fun x ↦ do
          let parent ← H (parentInput x.1 x.2 (siblingAt nodes carried x.1))
          pure (x.1 >>> 1, parent)
      pure (nodes.map fun x ↦ (x.1, siblingAt nodes carried x.1), parents)) := by
  unfold climbLevelWithHash
  have hs : ∀ node : ℕ, ((nodes.lookup (node ^^^ 1)).orElse fun _ ↦ carried.lookup node).getD
      default = siblingAt nodes carried node := by
    intro node
    simp only [siblingAt]
    cases nodes.lookup (node ^^^ 1) <;> rfl
  simp only [hs]
  congr 2
  funext x
  rcases x with ⟨node, digest⟩
  simp only [parentInput]
  split <;> rfl

variable {h : Bytes → Digest} {paths : List Opening} {height leafWords : ℕ}

/-- The paths' inputs, logged as `g` of them. -/
def InputOf {γ : Type} (g : Bytes → γ) (h : Bytes → Digest) (paths : List Opening) (y : γ) :
    Prop :=
  ∃ p ∈ paths, ∃ level ≤ p.path.length, y = g (climbInput h p level)

section Climb

variable (hp : PhaseDecodable h paths height leafWords)
include hp

/-- **The parent's input at a first child is a path's input** one level up: `parentDigest_eq`
(rtunprune), one hash earlier. -/
theorem parentInput_eq {k : ℕ} (hk : k < height) {nodes : List (ℕ × Digest)}
    (hn : NodesAt h paths k nodes) {x : ℕ × Digest} (hx : x ∈ nodes)
    (hfirst : x.1 % 2 = 0 ∨ x.1 ^^^ 1 ∉ nodes.map Prod.fst) {p : Opening} (hpm : p ∈ paths)
    (hpx : p.leafIndex >>> (k + 1) = x.1 >>> 1) :
    parentInput x.1 x.2 (siblingAt nodes (carriedAt paths k) x.1) = climbInput h p (k + 1) := by
  have hxns : x.1 ∈ levelNodes (distinctPositions (paths.map Opening.leafIndex)) k :=
    hn.1 ▸ List.mem_map_of_mem hx
  obtain ⟨p', hp', hp'k⟩ := exists_of_mem_levelNodes hxns
  have hsx : siblingAt nodes (carriedAt paths k) x.1 = p'.path.getD k default := by
    rw [← hp'k]; exact siblingAt_eq hp hk hn hp'
  have hdx : x.2 = climbTo h p' k := hn.2 x hx p' hp' hp'k
  rw [Nat.shiftRight_add, shiftRight_one_eq_iff] at hpx
  show _ = if (p.leafIndex >>> k) % 2 = 0 then
      digestBytes (climbTo h p k) ++ digestBytes (p.path.getD k default)
    else digestBytes (p.path.getD k default) ++ digestBytes (climbTo h p k)
  rcases hpx with hc | hc
  · have hsame := hp.same_node p' hp' p hpm k hk (hp'k.trans hc.symm)
    rw [parentInput, hsx, hdx, hc, hsame.1, hsame.2]
  · have hne := mem_levelNodes_of_mem hpm k
    have heven : x.1 % 2 = 0 :=
      hfirst.resolve_right (by rw [hn.1, ← hc]; exact not_not.2 hne)
    have hc' : p.leafIndex >>> k = x.1 + 1 := by rw [hc, xor_one_eq]; simp only [heven, ↓reduceIte]
    have hs : siblingAt nodes (carriedAt paths k) x.1 = climbTo h p k :=
      hsx.trans (hp.sibling_node p' hp' p hpm k hk (by rw [hp'k, hc]))
    have hback : (p.leafIndex >>> k) ^^^ 1 = p'.leafIndex >>> k := by
      have hodd : ¬ (x.1 + 1) % 2 = 0 := by omega
      rw [hp'k, hc', xor_one_eq]
      simp only [hodd, ↓reduceIte]
      omega
    have hd : x.2 = p.path.getD k default :=
      hdx.trans (hp.sibling_node p hpm p' hp' k hk hback).symm
    have hodd : ¬ (p.leafIndex >>> k) % 2 = 0 := by omega
    simp only [parentInput, heven, hodd, hs, hd, ↓reduceIte]

/-- **One level of the climb, logged**: from the nodes of level `k`, it logs only the paths'
inputs at level `k + 1`, and returns the climb with `h`. -/
theorem logsIn_climbLevel {γ : Type} (g : Bytes → γ) {k : ℕ} (hk : k < height)
    {nodes : List (ℕ × Digest)} (hn : NodesAt h paths k nodes) :
    LogsIn (InputOf g h paths) (climbLevelWithHash (tagHash g h) nodes (carriedAt paths k))
      (climbLevelWithHash (m := Id) h nodes (carriedAt paths k)) := by
  rw [climbLevelWithHash_eq, climbLevelWithHash_eq]
  refine LogsIn.bind' (LogsIn.mapM' fun x hx ↦ ?_) (LogsIn.pure' _)
  have hx' := List.mem_filter.1 hx
  have hfirst : x.1 % 2 = 0 ∨ x.1 ^^^ 1 ∉ nodes.map Prod.fst := by simpa using hx'.2
  obtain ⟨p, hpm, hpk⟩ := exists_of_mem_levelNodes (hn.1 ▸ List.mem_map_of_mem hx'.1)
  have hpx : p.leafIndex >>> (k + 1) = x.1 >>> 1 := by rw [Nat.shiftRight_add, hpk]
  refine LogsIn.bind' (logsIn_tagHash g h ⟨p, hpm, k + 1, ?_, ?_⟩) (LogsIn.pure' _)
  · rw [(hp.shape p hpm).1]; omega
  · rw [parentInput_eq hp hk hn hx'.1 hfirst hpm hpx]

/-- **The climb, logged**: from the nodes of level `k`, it logs only the paths' inputs, and
returns the climb with `h`. -/
theorem logsIn_climbLevels {γ : Type} (g : Bytes → γ) : ∀ (r k : ℕ) (nodes : List (ℕ × Digest)),
    k + r ≤ height → NodesAt h paths k nodes →
    LogsIn (InputOf g h paths)
      (climbLevelsWithHash (tagHash g h) ((List.range' k r).map (carriedAt paths)) nodes)
      (climbLevelsWithHash (m := Id) h ((List.range' k r).map (carriedAt paths)) nodes)
  | 0, _, _, _, _ => LogsIn.pure' _
  | r + 1, k, nodes, hkr, hn => by
    rw [List.range'_succ, List.map_cons]
    unfold climbLevelsWithHash
    refine LogsIn.bind' (logsIn_climbLevel hp g (by omega) hn) ?_
    exact LogsIn.bind' (logsIn_climbLevels g r (k + 1) _ (by omega)
      (climbLevel_spec hp (by omega) hn).2) (LogsIn.pure' _)

/-- **A phase's unpruning, logged**: it logs only the paths' inputs, and returns the unpruning
with `h`. -/
theorem logsIn_unprunePhase {γ : Type} (g : Bytes → γ) :
    LogsIn (InputOf g h paths) (unprunePhaseWithHash (tagHash g h) (prunePhase paths))
      (unprunePhaseWithHash (m := Id) h (prunePhase paths)) := by
  have hheight : (paths.head?.map fun path ↦ path.path.length).getD 0 = height := by
    cases paths with
    | nil => exact absurd rfl hp.nonempty
    | cons p _ => simp [(hp.shape p List.mem_cons_self).1]
  rw [prunePhase_eq]
  simp only [hheight]
  unfold unprunePhaseWithHash
  refine LogsIn.bind' (LogsIn.mapM' fun leaf hleaf ↦ ?_) (LogsIn.bind' ?_ (LogsIn.pure' _))
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hleaf
    exact logsIn_tagHash g h ⟨p, mem_of_mem_distinctPaths hp', 0, Nat.zero_le _, rfl⟩
  · have h0 := nodesAt_zero hp
    rw [List.range_eq_range']
    have e : ((distinctPaths paths).map Opening.leaf).mapM (m := Id)
        (fun leaf ↦ h (leaf.flatMap K.toBytes)) =
        ((distinctPaths paths).map Opening.leaf).map fun leaf ↦ h (leaf.flatMap K.toBytes) :=
      List.idRun_mapM
    rw [e]
    exact logsIn_climbLevels hp g height 0 _ (by omega) h0

end Climb

/-- **Decoding an honest proof's bytes, logged**: it logs only `g` of the inputs its paths climb
through, and returns the decoding with `h`. -/
theorem logsIn_fromBytesWithHash {γ : Type} (g : Bytes → γ) {proof : Proof}
    (hw : WireDecodable h proof) :
    LogsIn (fun y ↦ ∃ phase ∈ proof.openings, InputOf g h phase y)
      (fromBytesWithHash (tagHash g h) proof.toBytes)
      (fromBytesWithHash (m := Id) h proof.toBytes) := by
  rw [fromBytesWithHash_toBytes hw, fromBytesWithHash_toBytes hw]
  refine LogsIn.bind' ?_ (LogsIn.pure' _)
  rw [List.mapM_map, List.mapM_map]
  refine LogsIn.mapM' fun phase hphase ↦ ?_
  obtain ⟨height, leafWords, hp⟩ := hw.phases phase hphase
  exact (logsIn_unprunePhase hp g).mono fun y hy ↦ ⟨phase, hphase, hy⟩

end LeanVM.Wire

end
