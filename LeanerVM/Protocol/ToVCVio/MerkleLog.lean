/-
  LeanerVM.Protocol.ToVCVio.MerkleLog

  Merkle trees read off a log of hash queries, and their binding: a pruned opening whose hashes
  the log answers opens the leaves read off the adversary's part of the log, unless the log shows
  a collision, an input asked with two answers, or a fresh answer equal to a digest already
  known. Deterministic, over any encoding of leaves and nodes into one query domain. Candidate
  for VCVio.
-/

module

public import LeanerVM.Protocol.ToVCVio.Merkle
public import LeanerVM.Protocol.ToVCVio.QueryLog
public import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

/-!
# Merkle trees read off a query log

A log is a list of queries with their answers, VCVio's `MerkleTreeExtractor.QueryLog`. A node is
hashed as one query `nodeEnc l r` on its children, and a leaf as a query that parses back to its
payload; `node?` and `leaf?` parse a query as a node and as a leaf. The two encodings may overlap
(a query may parse as both), as they do in an untagged tree.

`extractTree` reads a tree top-down off a log: a node's children are those of the first logged
query answered by the node's digest that parses as a node (`nodePreimage`), and the leaf at
position `p` is reached by the bits of `p`, the top bit choosing the root's child. `leafPreimage`
reads a leaf's payload as the first logged query answered by its digest that parses as a leaf,
and `extractLeaf` composes the two. `extractLeaves` reads every position in one pass over the log,
by hash maps from answers to parses, and `extractLeaves_eq` equates it with `extractLeaf`.

`binding_of_log` is binding by replaying the log. Split the log into the adversary's queries
`logA` and those that follow, `logV` (the verifier's own, say). If the walk over a pruned opening
at strictly increasing positions, with every hash answered from the log, reaches `root`, then
every opened payload is the one `extractLeaf` reads off `logA` at its position, unless one of three
things shows on the finite log:

* the log is not `Consistent`: an input appears with two answers;
* it `HasCollision`: two different inputs with one answer;
* it has a `FreshHit`: a query of `logV` that is `Fresh` with respect to `logA` (`logA` never
  asks it) is answered by a digest `Known` from `logA` and the roots: a root, or a child of a
  query of `logA` that parses as a node.

All three are decidable. An answer of `logA` need not be known, since a fresh query answered by
one is a collision, and the opening's siblings need not be, since the extraction never descends
into a sibling. Several commitments, each opened once, are the instance with `roots` all their
roots: the hypotheses on the log are shared, and each opening is bound to its own root.

`not_freshHit_of_not_hasHit`: a fresh hit is a hit (`QueryLog.HasHit`) on any values in play that
grow along the log and hold every child of a logged node query and the roots, so a log with no hit
has no fresh hit.

`extractLeaf_determined`: with a consistent log and no fresh hit, the leaves read off the whole
log under a root are those read off `logA`, so no leaf joins a root once the root is known.
-/

namespace LeanerVM.Protocol.MerkleTree

open MerkleTreeExtractor (QueryLog)

@[expose] public section

variable {Q D P : Type}

/-! ## The log -/

section Log

/-- The answer a log gives to a query: the answer of its first logged occurrence. -/
def logAnswer [DecidableEq Q] (log : QueryLog Q D) (q : Q) : Option D :=
  (log.find? fun e ↦ e.1 = q).map (·.2)

/-- An answer the log gives is a logged entry. -/
theorem mem_of_logAnswer_eq_some [DecidableEq Q] {log : QueryLog Q D} {q : Q} {d : D}
    (h : logAnswer log q = some d) : ⟨q, d⟩ ∈ log := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain rfl : e.1 = q := by simpa using List.find?_some he
  exact List.mem_of_find?_eq_some he

/-- A log is consistent when no input appears in it with two answers: it is the trace of a
function. -/
def Consistent (log : QueryLog Q D) : Prop :=
  ∀ e₁ ∈ log, ∀ e₂ ∈ log, e₁.1 = e₂.1 → e₁.2 = e₂.2

/-- A collision: two different inputs of the log with one answer. -/
def HasCollision (log : QueryLog Q D) : Prop :=
  ∃ e₁ ∈ log, ∃ e₂ ∈ log, e₁.1 ≠ e₂.1 ∧ e₁.2 = e₂.2

/-- A query is fresh with respect to a log when the log never asks it. -/
def Fresh (log : QueryLog Q D) (q : Q) : Prop := ∀ e ∈ log, e.1 ≠ q

/-- The children a query names when it parses as a node: none, or both. -/
def queryChildren (node? : Q → Option (D × D)) (q : Q) : List D :=
  match node? q with
  | some (l, r) => [l, r]
  | none => []

/-- A digest is known from a log and a list of roots when it is a root or a child of a logged
query that parses as a node. -/
def Known (node? : Q → Option (D × D)) (roots : List D) (log : QueryLog Q D) (d : D) : Prop :=
  d ∈ roots ∨ ∃ e ∈ log, d ∈ queryChildren node? e.1

/-- A fresh hit: a query of `logV` fresh with respect to `logA`, answered by a digest known from
`logA` and the roots. -/
def FreshHit (node? : Q → Option (D × D)) (roots : List D) (logA logV : QueryLog Q D) : Prop :=
  ∃ e ∈ logV, Fresh logA e.1 ∧ Known node? roots logA e.2

variable [DecidableEq Q] [DecidableEq D]

instance (log : QueryLog Q D) : Decidable (Consistent log) := by
  unfold Consistent; infer_instance

instance (log : QueryLog Q D) : Decidable (HasCollision log) := by
  unfold HasCollision; infer_instance

instance (log : QueryLog Q D) (q : Q) : Decidable (Fresh log q) := by
  unfold Fresh; infer_instance

instance (node? : Q → Option (D × D)) (roots : List D) (log : QueryLog Q D) (d : D) :
    Decidable (Known node? roots log d) := by
  unfold Known; infer_instance

instance (node? : Q → Option (D × D)) (roots : List D) (logA logV : QueryLog Q D) :
    Decidable (FreshHit node? roots logA logV) := by
  unfold FreshHit; infer_instance

/-! ### Moving the split -/

variable {node? : Q → Option (D × D)} {roots roots' : List D}
  {log log' logA logV logV' : QueryLog Q D}

omit [DecidableEq Q] [DecidableEq D] in
/-- A query fresh with respect to a log is fresh with respect to any part of it. -/
theorem Fresh.anti {q : Q} (h : log ⊆ log') : Fresh log' q → Fresh log q :=
  fun hf e he ↦ hf e (h he)

omit [DecidableEq Q] [DecidableEq D] in
/-- A digest known from some roots and a log is known from more roots and a larger log. -/
theorem Known.mono {d : D} (hroots : roots ⊆ roots') (hlog : log ⊆ log') :
    Known node? roots log d → Known node? roots' log' d
  | .inl h => .inl (hroots h)
  | .inr ⟨e, he, hc⟩ => .inr ⟨e, hlog he, hc⟩

omit [DecidableEq Q] [DecidableEq D] in
/-- A fresh hit stays one in a larger `logV`. -/
theorem FreshHit.mono_logV (h : logV ⊆ logV') :
    FreshHit node? roots logA logV → FreshHit node? roots logA logV' :=
  fun ⟨e, he, hf, hk⟩ ↦ ⟨e, h he, hf, hk⟩

omit [DecidableEq Q] [DecidableEq D] in
/-- A fresh hit stays one with more roots. -/
theorem FreshHit.mono_roots (h : roots ⊆ roots') :
    FreshHit node? roots logA logV → FreshHit node? roots' logA logV :=
  fun ⟨e, he, hf, hk⟩ ↦ ⟨e, he, hf, hk.mono h (List.Subset.refl _)⟩

omit [DecidableEq D] in
/-- In a consistent log, a fresh hit is a hit at the first occurrence of its input: that query
of `logV` is fresh, no earlier query of `logV` asks it, and its answer is the same known
digest. -/
theorem FreshHit.first (hcons : Consistent (logA ++ logV))
    (h : FreshHit node? roots logA logV) :
    ∃ (k : ℕ) (hk : k < logV.length), Fresh logA logV[k].1 ∧
      (∀ (j : ℕ) (hj : j < k), logV[j].1 ≠ logV[k].1) ∧ Known node? roots logA logV[k].2 := by
  obtain ⟨e, he, hf, hkn⟩ := h
  have hk := List.findIdx_lt_length_of_exists (p := fun x ↦ decide (x.1 = e.1)) ⟨e, he, by simp⟩
  have hfirst : logV[logV.findIdx fun x ↦ decide (x.1 = e.1)].1 = e.1 := by
    simpa using List.findIdx_getElem (w := hk)
  refine ⟨_, hk, by rwa [hfirst], fun j hj ↦ by simpa [hfirst] using List.not_of_lt_findIdx hj, ?_⟩
  rwa [hcons _ (List.mem_append_right _ (List.getElem_mem hk)) e (List.mem_append_right _ he)
    hfirst]

omit [DecidableEq D] in
/-- **No hit, no fresh hit.** Let `inPlay` give the values in play after each prefix of a log,
growing along it, every child of a logged query that parses as a node in play once the query is
asked. In a consistent log `logA ++ logV` with no hit (`QueryLog.HasHit`), there is no fresh hit
with respect to `logA` and roots in play after `logA`. -/
theorem not_freshHit_of_not_hasHit {inPlay : QueryLog Q D → List D}
    (hmono : ∀ l₁ l₂, l₁ <+: l₂ → ∀ d ∈ inPlay l₁, d ∈ inPlay l₂)
    (hchild : ∀ l e, ∀ d ∈ queryChildren node? e.1, d ∈ inPlay (l ++ [e]))
    (hcons : Consistent (logA ++ logV)) (hhit : ¬ QueryLog.HasHit inPlay (logA ++ logV))
    (hroots : ∀ r ∈ roots, r ∈ inPlay logA) : ¬ FreshHit node? roots logA logV := by
  intro h
  obtain ⟨k, hk, hfresh, hfirst, hknown⟩ := h.first hcons
  have htake : (logA ++ logV).take (logA.length + k) = logA ++ logV.take k := by
    simp [List.take_append]
  have hget : (logA ++ logV)[logA.length + k]'(by simp; omega) = logV[k] := by
    simp [List.getElem_append_right]
  refine hhit ⟨⟨logA.length + k, by simp; omega⟩, fun e he ↦ ?_, ?_⟩
  · simp only [Fin.getElem_fin, htake, hget, List.mem_append] at he ⊢
    rcases he with he | he
    · exact hfresh e he
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
      simp only [List.length_take] at hj
      simpa using hfirst j (by omega)
  · simp only [Fin.getElem_fin, htake, hget]
    rcases hknown with hr | ⟨e, he, hd⟩
    · exact hmono _ _ (List.prefix_append _ _) _ (hroots _ hr)
    · obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp he
      refine hmono (logA.take p ++ [logA[p]]) _ ?_ _ (hchild _ _ _ hd)
      rw [← List.take_succ_eq_append_getElem hp]
      exact (List.take_prefix _ _).trans (List.prefix_append _ _)

end Log

/-! ## Extraction -/

section Extract

variable [DecidableEq D]

/-- The children of the first logged query answered by `d` whose input parses as a node. -/
def nodePreimage (node? : Q → Option (D × D)) (log : QueryLog Q D) (d : D) : Option (D × D) :=
  log.findSome? fun e ↦ if e.2 = d then node? e.1 else none

/-- The payload of the first logged query answered by `d` whose input parses as a leaf. -/
def leafPreimage (leaf? : Q → Option P) (log : QueryLog Q D) (d : D) : Option P :=
  log.findSome? fun e ↦ if e.2 = d then leaf? e.1 else none

/-- The digest of leaf `p` of the subtree of height `h` under `top`, read top-down off the log:
a node's children are its `nodePreimage`, and bit `h - 1` of `p` chooses the child at height
`h`. Only the low `h` bits of `p` are read. -/
def extractTree (node? : Q → Option (D × D)) (log : QueryLog Q D) : D → ℕ → ℕ → Option D
  | top, 0, _ => some top
  | top, h + 1, p => (nodePreimage node? log top).bind fun c ↦
      extractTree node? log (if p.testBit h then c.2 else c.1) h p

/-- The payload of leaf `p` of the tree of depth `depth` under `root`, read off the log. -/
def extractLeaf (node? : Q → Option (D × D)) (leaf? : Q → Option P) (log : QueryLog Q D)
    (root : D) (depth p : ℕ) : Option P :=
  (extractTree node? log root depth p).bind (leafPreimage leaf? log)

end Extract

/-! ## Extraction in one pass -/

section Fast

variable [DecidableEq D] [Hashable D]

/-- A step of `parseIndex`: a query that parses records its parse under its answer, unless the
answer already has one. -/
def indexStep {R : Type} (parse : Q → Option R) (index : Std.HashMap D R) (e : (_ : Q) × D) :
    Std.HashMap D R :=
  match parse e.1 with
  | some c => index.insertIfNew e.2 c
  | none => index

/-- Each answer of a log mapped to the parse of the first logged query it answers that parses,
in one pass over the log, into a map with room for every entry. -/
def parseIndex {R : Type} (parse : Q → Option R) (log : QueryLog Q D) : Std.HashMap D R :=
  log.foldl (indexStep parse) (.emptyWithCapacity log.length)

/-- The digests of the `2^h` leaves of the subtree of height `h` under `top`, in position order,
read off a node index. -/
def leafDigests (index : Std.HashMap D (D × D)) : D → (h : ℕ) → List (Option D)
  | top, 0 => [some top]
  | top, h + 1 =>
    match index[top]? with
    | none => List.replicate (2 ^ (h + 1)) none
    | some (l, r) => leafDigests index l h ++ leafDigests index r h

/-- The payloads of all `2^depth` leaves of the tree under `root`, in position order, read off
the log in one pass: `extractLeaf` at every position (`extractLeaves_eq`). -/
def extractLeaves (node? : Q → Option (D × D)) (leaf? : Q → Option P) (log : QueryLog Q D)
    (root : D) (depth : ℕ) : List (Option P) :=
  let leaves := parseIndex leaf? log
  (leafDigests (parseIndex node? log) root depth).map fun d? ↦ d?.bind fun d ↦ leaves[d]?

private theorem getElem?_foldl_indexStep {R : Type} (parse : Q → Option R) (d : D) :
    ∀ (log : QueryLog Q D) (index : Std.HashMap D R),
      (log.foldl (indexStep parse) index)[d]? =
        index[d]?.or (log.findSome? fun e ↦ if e.2 = d then parse e.1 else none)
  | [], index => by simp
  | e :: log, index => by
    rw [List.foldl_cons, getElem?_foldl_indexStep parse d log, List.findSome?_cons, indexStep]
    rcases parse e.1 with _ | c
    · simp
    · rw [Std.HashMap.getElem?_insertIfNew]
      by_cases he : e.2 = d
      · subst he
        by_cases hm : e.2 ∈ index <;> simp [hm]
      · simp [he]

/-- The index maps an answer to the parse of the first logged query it answers that parses. -/
theorem getElem?_parseIndex {R : Type} (parse : Q → Option R) (log : QueryLog Q D) (d : D) :
    (parseIndex parse log)[d]? = log.findSome? fun e ↦ if e.2 = d then parse e.1 else none := by
  simp [parseIndex, getElem?_foldl_indexStep]

omit [Hashable D] in
private theorem extractTree_two_pow_add (node? : Q → Option (D × D)) (log : QueryLog Q D)
    (H p : ℕ) : ∀ (h : ℕ) (top : D), h ≤ H →
      extractTree node? log top h (2 ^ H + p) = extractTree node? log top h p
  | 0, _, _ => rfl
  | h + 1, top, hh => by
    simp only [extractTree, Nat.testBit_two_pow_add_gt (show h < H by omega)]
    exact congrArg _ (funext fun _ ↦ extractTree_two_pow_add node? log H p h _ (by omega))

private theorem leafDigests_eq (node? : Q → Option (D × D)) (log : QueryLog Q D) :
    ∀ (h : ℕ) (top : D), leafDigests (parseIndex node? log) top h =
      (List.range (2 ^ h)).map (extractTree node? log top h)
  | 0, top => by simp [leafDigests, extractTree]
  | h + 1, top => by
    rw [leafDigests, getElem?_parseIndex, ← nodePreimage]
    rcases hn : nodePreimage node? log top with _ | ⟨l, r⟩
    · simp [extractTree, hn, List.map_const']
    · dsimp only
      rw [leafDigests_eq node? log h l, leafDigests_eq node? log h r, Nat.pow_succ, Nat.mul_two,
        List.range_add, List.map_append, List.map_map]
      congr 1 <;> refine List.map_congr_left fun p hp ↦ ?_ <;>
        simp [extractTree, hn, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow
          (List.mem_range.mp hp), extractTree_two_pow_add node? log h p h r le_rfl]

/-- The one-pass extraction is `extractLeaf` at every position. -/
theorem extractLeaves_eq (node? : Q → Option (D × D)) (leaf? : Q → Option P)
    (log : QueryLog Q D) (root : D) (depth : ℕ) :
    extractLeaves node? leaf? log root depth =
      (List.range (2 ^ depth)).map (extractLeaf node? leaf? log root depth) := by
  rw [extractLeaves, leafDigests_eq, List.map_map]
  refine List.map_congr_left fun p _ ↦ ?_
  simp only [Function.comp_apply, extractLeaf, getElem?_parseIndex]
  rfl

end Fast

/-! ## Binding -/

section Binding

/-- `v` stands at height `h` above the leaf at `p` of digest `d`: every node on the way down is
answered by `hash` on its children, and bit `h - 1` of `p` chooses the child at height `h`. -/
private def Chain (hash : D → D → Option D) : ℕ → D → ℕ → D → Prop
  | 0, v, _, d => v = d
  | h + 1, v, p, d => ∃ l r, hash l r = some v ∧ Chain hash h (if p.testBit h then r else l) p d

private theorem consParent_eq_some {U : Type} {i : ℕ} {parent : Option U}
    {rest : Option (Option (List (ℕ × U) × List D))} {ps : List (ℕ × U)} {sibs : List D}
    (h : consParent i parent rest = some (some (ps, sibs))) :
    ∃ p ps', parent = some p ∧ rest = some (some (ps', sibs)) ∧ ps = (i, p) :: ps' := by
  rcases parent with _ | p <;> rcases rest with _ | _ | ⟨ps', sibs'⟩ <;> cases h
  exact ⟨p, ps', rfl, rfl, rfl⟩

private theorem withNext_eq_some {X : Type} {sibs : List D}
    {k : D → List D → Option (Option X)} {x : X} (h : withNext sibs k = some (some x)) :
    ∃ s rest, sibs = s :: rest ∧ k s rest = some (some x) := by
  cases sibs with
  | nil => cases h
  | cons s rest => exact ⟨s, rest, rfl, h⟩

/-- The parent of node `i` and a supplied sibling, in `Option`: the hash of the two children in
index order. -/
private theorem withSupplied_eq_some {hash : D → D → Option D} {h i : ℕ} {a s v : D}
    (hv : withSupplied (NodeAlgebra.ofHash hash) (h := h) i a s = some v) :
    ∃ l r, hash l r = some v ∧ (if i % 2 = 1 then r else l) = a := by
  unfold withSupplied at hv
  split at hv
  · exact ⟨a, s, hv, ite_eq_right (by omega)⟩
  · exact ⟨s, a, hv, ite_eq_left (by omega)⟩

/-- One level of the walk in `Option`: each parent has a child among the nodes, the parents
strictly increase when the nodes do, and every node's parent is answered by `hash` on two
children, the node on its side. -/
private theorem levelStep_parents (hash : D → D → Option D) {h : ℕ} :
    ∀ (nodes : List (ℕ × D)) (sibs : List D) (ps : List (ℕ × D)) (rest : List D),
      levelStep (NodeAlgebra.ofHash hash) (h := h) nodes sibs = some (some (ps, rest)) →
      (∀ y ∈ ps, ∃ x ∈ nodes, y.1 = x.1 / 2) ∧
      (nodes.Pairwise (fun x y ↦ x.1 < y.1) → ps.Pairwise (fun x y ↦ x.1 < y.1)) ∧
      ∀ x ∈ nodes, ∃ v, (x.1 / 2, v) ∈ ps ∧
        ∃ l r, hash l r = some v ∧ (if x.1 % 2 = 1 then r else l) = x.2
  | [], sibs, ps, rest, hs => by
    cases hs
    exact ⟨nofun, fun _ ↦ .nil, nofun⟩
  | (i, a) :: (j, b) :: tl, sibs, ps, rest, hs => by
    by_cases hp : i % 2 = 0 ∧ j = i + 1
    · simp only [levelStep, hp, and_self, ↓reduceIte] at hs
      obtain ⟨p, ps', hpar, hrest, rfl⟩ := consParent_eq_some hs
      obtain ⟨ih1, ih2, ih3⟩ := levelStep_parents hash tl sibs ps' rest hrest
      refine ⟨List.forall_mem_cons.mpr ⟨⟨_, List.mem_cons_self, rfl⟩, fun y hy ↦ ?_⟩,
        fun hsort ↦ .cons (fun y hy ↦ ?_) (ih2 hsort.tail.tail), List.forall_mem_cons.mpr
          ⟨⟨p, List.mem_cons_self, a, b, hpar, ite_eq_right (by omega)⟩, List.forall_mem_cons.mpr
            ⟨⟨p, by rw [show j / 2 = i / 2 by omega]; exact List.mem_cons_self, a, b, hpar,
              ite_eq_left (by omega)⟩, fun x hx ↦ ?_⟩⟩⟩
      · obtain ⟨x, hx, hxy⟩ := ih1 y hy
        exact ⟨x, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx), hxy⟩
      · obtain ⟨x, hx, hxy⟩ := ih1 y hy
        have := List.rel_of_pairwise_cons hsort.tail hx
        dsimp only at this ⊢
        omega
      · obtain ⟨v, hv, hc⟩ := ih3 x hx
        exact ⟨v, List.mem_cons_of_mem _ hv, hc⟩
    · simp only [levelStep, hp, ↓reduceIte] at hs
      obtain ⟨s, sibs', rfl, hs⟩ := withNext_eq_some hs
      obtain ⟨p, ps', hpar, hrest, rfl⟩ := consParent_eq_some hs
      obtain ⟨ih1, ih2, ih3⟩ := levelStep_parents hash ((j, b) :: tl) sibs' ps' rest hrest
      refine ⟨List.forall_mem_cons.mpr ⟨⟨_, List.mem_cons_self, rfl⟩, fun y hy ↦ ?_⟩,
        fun hsort ↦ .cons (fun y hy ↦ ?_) (ih2 hsort.tail), List.forall_mem_cons.mpr
          ⟨⟨p, List.mem_cons_self, withSupplied_eq_some hpar⟩, fun x hx ↦ ?_⟩⟩
      · obtain ⟨x, hx, hxy⟩ := ih1 y hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩
      · obtain ⟨x, hx, hxy⟩ := ih1 y hy
        have hij := List.rel_of_pairwise_cons hsort List.mem_cons_self
        have hjx : j ≤ x.1 := by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_rfl
          · exact (List.rel_of_pairwise_cons hsort.tail hx).le
        dsimp only at hij ⊢
        omega
      · obtain ⟨v, hv, hc⟩ := ih3 x hx
        exact ⟨v, List.mem_cons_of_mem _ hv, hc⟩
  | [(i, a)], sibs, ps, rest, hs => by
    simp only [levelStep] at hs
    obtain ⟨s, sibs', rfl, hs⟩ := withNext_eq_some hs
    obtain ⟨p, ps', hpar, hrest, rfl⟩ := consParent_eq_some hs
    cases hrest
    exact ⟨List.forall_mem_singleton.mpr ⟨_, List.mem_singleton_self _, rfl⟩,
      fun _ ↦ List.pairwise_singleton _ _,
      List.forall_mem_singleton.mpr ⟨p, List.mem_singleton_self _, withSupplied_eq_some hpar⟩⟩

/-- The walk in `Option`: if it reaches `r` from nodes that strictly increase and stand above
the leaves, then every leaf in the tree has a chain up to `r`. -/
private theorem fold_chains (hash : D → D → Option D) (leaves : List (ℕ × D)) :
    ∀ (k h t : ℕ) (e : h + k = t) (nodes : List (ℕ × D)) (sibs : List D) (r : D),
      fold (NodeAlgebra.ofHash hash) k h t e nodes sibs = some (some r) →
      nodes.Pairwise (fun x y ↦ x.1 < y.1) →
      (∀ x ∈ leaves, ∃ v, (x.1 / 2 ^ h, v) ∈ nodes ∧ Chain hash h v x.1 x.2) →
      ∀ x ∈ leaves, x.1 < 2 ^ t → Chain hash t r x.1 x.2
  | 0, h, t, e, nodes, sibs, r, hf, hsort, hinv => by
    subst e
    intro x hx hlt
    obtain ⟨v, hv, hc⟩ := hinv x hx
    rw [Nat.add_zero] at hlt
    rw [Nat.div_eq_of_lt hlt] at hv
    rcases nodes with _ | ⟨⟨i₀, a⟩, tl⟩
    · cases hv
    rcases sibs with _ | _
    · cases hf
      rcases List.mem_cons.mp hv with hv | hv
      · cases hv
        exact hc
      · exact absurd (List.rel_of_pairwise_cons hsort hv) (Nat.not_lt_zero _)
    · cases hf
  | k + 1, h, t, e, nodes, sibs, r, hf, hsort, hinv => by
    simp only [fold, Option.bind_eq_bind] at hf
    obtain ⟨res, hres, hf⟩ := Option.bind_eq_some_iff.mp hf
    rcases res with _ | ⟨ps, rest⟩
    · cases hf
    obtain ⟨_, hps, hpar⟩ := levelStep_parents hash nodes sibs ps rest hres
    refine fold_chains hash leaves k (h + 1) t (by omega) ps rest r hf (hps hsort) fun x hx ↦ ?_
    obtain ⟨v, hv, hc⟩ := hinv x hx
    obtain ⟨v', hv', l, r', hlr, hside⟩ := hpar _ hv
    refine ⟨v', by rwa [Nat.pow_succ, ← Nat.div_div_eq_div_mul], l, r', hlr, ?_⟩
    dsimp only at hside
    rw [← hside] at hc
    simpa only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] using hc

/-- A search that every element answers with `none` or `c`, and some element with `c`,
returns `c`. -/
private theorem findSome?_eq_of_forall {α β : Type} {f : α → Option β} {c : Option β}
    {l : List α} (hall : ∀ x ∈ l, f x = none ∨ f x = c) (hex : ∃ x ∈ l, f x = c) :
    l.findSome? f = c := by
  cases hfs : l.findSome? f with
  | none =>
    obtain ⟨x, hx, rfl⟩ := hex
    exact (List.findSome?_eq_none_iff.mp hfs x hx).symm
  | some b =>
    obtain ⟨y, hy, hfy⟩ := List.exists_of_findSome?_eq_some hfs
    exact hfy.symm.trans ((hall y hy).resolve_left (hfy ▸ Option.some_ne_none b))

variable {node? : Q → Option (D × D)} {logA logV : QueryLog Q D} {ans : Q → Option D}
  {roots : List D}

/-- With no collision, the first query of `logA` answered by the answer `v` of its query `q`
that parses is `q`'s parse. -/
private theorem findSome?_eq_parse [DecidableEq D] (hcoll : ¬ HasCollision (logA ++ logV))
    {R : Type} (parse : Q → Option R) {q : Q} {v : D} (hmem : ⟨q, v⟩ ∈ logA) :
    logA.findSome? (fun e ↦ if e.2 = v then parse e.1 else none) = parse q := by
  refine findSome?_eq_of_forall (fun e he ↦ ?_) ⟨⟨q, v⟩, hmem, ite_eq_left rfl⟩
  by_cases hv : e.2 = v
  · refine .inr ?_
    rw [ite_eq_left hv, Classical.not_not.mp fun hne ↦
      hcoll ⟨e, List.mem_append_left _ he, ⟨q, v⟩, List.mem_append_left _ hmem, hne, hv⟩]
  · exact .inl (ite_eq_right hv)

/-- An entry of the log answered by a known digest is an entry of `logA`. -/
private theorem mem_logA (hcons : Consistent (logA ++ logV))
    (hhit : ¬ FreshHit node? roots logA logV) {e : (_ : Q) × D} (he : e ∈ logA ++ logV)
    (hk : Known node? roots logA e.2) : e ∈ logA := by
  rcases List.mem_append.mp he with h | h
  · exact h
  by_cases hf : Fresh logA e.1
  · exact absurd ⟨e, h, hf, hk⟩ hhit
  simp only [Fresh, not_forall, not_not] at hf
  obtain ⟨e', he', h1⟩ := hf
  exact Sigma.ext h1 (heq_of_eq (hcons _ (List.mem_append_left _ he') _ he h1)) ▸ he'

/-- A child of a query of `logA` that parses as a node is known. -/
private theorem known_child {e : (_ : Q) × D} (he : e ∈ logA) {l r : D}
    (hn : node? e.1 = some (l, r)) (b : Bool) : Known node? roots logA (if b then r else l) :=
  .inr ⟨e, he, by cases b <;> simp [queryChildren, hn]⟩

/-- Down a chain from a known digest, `extractTree` reads the chain's leaf digest off `logA`,
and that digest is known. -/
private theorem extractTree_of_chain [DecidableEq D] {nodeEnc : D → D → Q}
    (hnode : ∀ l r, node? (nodeEnc l r) = some (l, r))
    (hans : ∀ q d, ans q = some d → ⟨q, d⟩ ∈ logA ++ logV)
    (hcons : Consistent (logA ++ logV)) (hcoll : ¬ HasCollision (logA ++ logV))
    (hhit : ¬ FreshHit node? roots logA logV) (p : ℕ) (d : D) :
    ∀ (h : ℕ) (v : D), Chain (fun l r ↦ ans (nodeEnc l r)) h v p d →
      Known node? roots logA v → extractTree node? logA v h p = some d ∧ Known node? roots logA d
  | 0, _, rfl, hk => ⟨rfl, hk⟩
  | h + 1, v, ⟨l, r, hlr, hc⟩, hk => by
    have hmem := mem_logA hcons hhit (hans _ _ hlr) hk
    have hpre : nodePreimage node? logA v = some (l, r) := by
      rw [nodePreimage, findSome?_eq_parse hcoll node? hmem, hnode]
    simp only [extractTree, hpre, Option.bind_some]
    exact extractTree_of_chain hnode hans hcons hcoll hhit p d h _ hc
      (known_child hmem (hnode l r) _)

/-- Binding by log replay. A pruned opening of a tree of depth `depth` under `root`: payloads at
strictly increasing positions in the tree, each hashed by a query that parses back to it, and
siblings, over which the walk with every node hashed as `nodeEnc` of its children reaches `root`,
with every hash answered by `ans` from the log `logA ++ logV`. If the log is consistent, has no
collision and no fresh hit with respect to `logA` and roots containing `root`, then every opened
payload is the one read off `logA` at its position. -/
theorem binding_of_log [DecidableEq D] (node? : Q → Option (D × D)) (nodeEnc : D → D → Q)
    (hnode : ∀ l r, node? (nodeEnc l r) = some (l, r)) (leaf? : Q → Option P)
    (logA logV : QueryLog Q D) (ans : Q → Option D)
    (hans : ∀ q d, ans q = some d → ⟨q, d⟩ ∈ logA ++ logV) (roots : List D) (root : D)
    (hroot : root ∈ roots) (depth : ℕ) (positions : List ℕ) (payloads : List P)
    (digests sibs : List D) (hlen : positions.length = payloads.length)
    (hsorted : positions.Pairwise (· < ·)) (hlt : ∀ p ∈ positions, p < 2 ^ depth)
    (hleaves : List.Forall₂ (fun x d ↦ ∃ q, leaf? q = some x ∧ ans q = some d) payloads digests)
    (hwalk : prunedRoot (fun l r ↦ ans (nodeEnc l r)) depth (positions.zip digests) sibs =
      some (some root))
    (hcons : Consistent (logA ++ logV)) (hcoll : ¬ HasCollision (logA ++ logV))
    (hhit : ¬ FreshHit node? roots logA logV) :
    positions.map (extractLeaf node? leaf? logA root depth) = payloads.map some := by
  have hld : positions.length = digests.length := hlen.trans hleaves.length_eq
  have hsort : (positions.zip digests).Pairwise (fun x y ↦ x.1 < y.1) := by
    rwa [← List.pairwise_map (f := Prod.fst), List.map_fst_zip (le_of_eq hld)]
  have hchains := fold_chains (fun l r ↦ ans (nodeEnc l r)) (positions.zip digests) depth 0 depth
    (Nat.zero_add depth) _ sibs root hwalk hsort (fun x hx ↦ ⟨x.2, by simpa using hx, rfl⟩)
  refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ ↦ ?_
  simp only [List.length_map] at h₁ h₂
  have hd : i < digests.length := hld ▸ h₁
  have hx : (positions[i], digests[i]) ∈ positions.zip digests := by
    rw [← List.getElem_zip (h := by simp [h₁, hd])]
    exact List.getElem_mem _
  obtain ⟨hext, hk⟩ := extractTree_of_chain hnode hans hcons hcoll hhit positions[i] digests[i]
    depth root (hchains _ hx (hlt _ (List.getElem_mem _))) (.inl hroot)
  obtain ⟨q, hq, ha⟩ := List.forall₂_iff_get.mp hleaves |>.2 i h₂ hd
  simp only [List.get_eq_getElem] at hq ha
  simp only [List.getElem_map, extractLeaf, hext, Option.bind_some, leafPreimage]
  rw [findSome?_eq_parse hcoll leaf? (mem_logA hcons hhit (hans _ _ ha) hk), hq]

/-- With no fresh hit, the first query answered by a known digest that parses is in `logA`. -/
private theorem findSome?_append_of_known [DecidableEq D] {R : Type} (parse : Q → Option R)
    (hcons : Consistent (logA ++ logV)) (hhit : ¬ FreshHit node? roots logA logV) {v : D}
    (hk : Known node? roots logA v) :
    (logA ++ logV).findSome? (fun e ↦ if e.2 = v then parse e.1 else none) =
      logA.findSome? (fun e ↦ if e.2 = v then parse e.1 else none) := by
  rw [List.findSome?_append]
  rcases hA : logA.findSome? (fun e ↦ if e.2 = v then parse e.1 else none) with _ | x
  · rw [hA, Option.none_or]
    refine List.findSome?_eq_none_iff.mpr fun e he ↦ ?_
    by_cases hv : e.2 = v
    · exact List.findSome?_eq_none_iff.mp hA e
        (mem_logA hcons hhit (List.mem_append_right _ he) (hv ▸ hk))
    · exact ite_eq_right hv
  · rw [hA, Option.some_or]

/-- Down the tree from a known digest, `extractTree` reads the same off the log as off `logA`,
and the digests it reads off `logA` are known. -/
private theorem extractTree_append [DecidableEq D] (hcons : Consistent (logA ++ logV))
    (hhit : ¬ FreshHit node? roots logA logV) (p : ℕ) :
    ∀ (h : ℕ) (top : D), Known node? roots logA top →
      extractTree node? (logA ++ logV) top h p = extractTree node? logA top h p ∧
        ∀ d, extractTree node? logA top h p = some d → Known node? roots logA d
  | 0, _, hk => ⟨rfl, fun _ hd ↦ Option.some_injective _ hd ▸ hk⟩
  | h + 1, top, hk => by
    simp only [extractTree, nodePreimage, findSome?_append_of_known node? hcons hhit hk]
    rcases hc : logA.findSome? (fun e ↦ if e.2 = top then node? e.1 else none) with _ | ⟨l, r⟩
    · rw [hc]
      exact ⟨rfl, nofun⟩
    · obtain ⟨e, he, hfe⟩ := List.exists_of_findSome?_eq_some hc
      rw [hc]
      exact extractTree_append hcons hhit p h _
        (known_child he (Option.ite_none_right_eq_some.mp hfe).2 _)

/-- The leaves read off a log are those read off `logA`, its part up to a point, when the
log is consistent and has no fresh hit with respect to `logA` and roots containing `root`: no
leaf joins a root after the root is known. -/
theorem extractLeaf_determined [DecidableEq D] (node? : Q → Option (D × D))
    (leaf? : Q → Option P) (logA logV : QueryLog Q D) (roots : List D) (root : D)
    (hroot : root ∈ roots) (hcons : Consistent (logA ++ logV))
    (hhit : ¬ FreshHit node? roots logA logV) (depth p : ℕ) :
    extractLeaf node? leaf? (logA ++ logV) root depth p =
      extractLeaf node? leaf? logA root depth p := by
  obtain ⟨htree, hknown⟩ := extractTree_append hcons hhit p depth root (.inl hroot)
  rw [extractLeaf, extractLeaf, htree]
  rcases hd : extractTree node? logA root depth p with _ | d
  · rfl
  · exact findSome?_append_of_known leaf? hcons hhit (hknown d hd)

end Binding

end
end LeanerVM.Protocol.MerkleTree
