/-
  LeanVM.Protocol.Compile.Rom.Prover

  The honest prover of a compiled verifier program with the hash in any monad: the prover of
  `LeanVM.Protocol.Compile.Prover` written so that it runs against the random oracle, with its
  `Id` instance the pure prover, its commutation with simulation, and its query bound.
-/

module

public import LeanVM.Protocol.Compile.Prover
public import LeanVM.Protocol.Compile.Cost

/-!
# The honest prover against the random oracles

`proveM H F P S seed fuel` is the honest prover `prove` (`LeanVM.Protocol.Compile.Prover`) with
the hash `H : Bytes → m Digest` and the permutation `F : KState → m KState` in any monad `m`, as
the verifier `run` is. Its `Id` instance is `prove` (`proveM_id`); at `H = queryH` and
`F = queryF` it is an oracle computation, the honest prover of the random-oracle model.

* The Merkle tree is built level by level as lists (`parentsM`, `rootOfLevelM`, `pathOfLevelM`);
  an opening rebuilds the tree it opens, as `openingAt` does.
* The proof-of-work search tries the nonces `0, 1, …` in order, each absorbed into the sponge
  with tag `4` and a challenge squeezed (`powStepM`, `searchM`).
* `simulateQ_proveM`: interpreting the queries of `proveM queryH queryF` by any implementation is
  running `proveM` with that implementation as the hash and the permutation.
* `simulateQ_id_of_look`: a computation whose run against a log's answers returns `r` returns
  `r` against every hash function and permutation that agree with the log.
* `isTotalQueryBound_proveM`: a program of cost `n` at height `h` (`Prog.CostLE`, in quarters)
  makes the prover query the oracles at most `n · (2^(h + 1) + 2 · fuel + 2)` times, after the
  seed.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleComp OracleSpec

@[expose] public section

/-! ## The prover with the hash in any monad -/

section ProverM

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KState → m KState)

/-- The first `n` parents of a level: parent `j` hashes nodes `2j` and `2j + 1`. -/
def parentsM (level : List Digest) (n : ℕ) : m (List Digest) :=
  (List.range n).mapM fun j ↦
    H (digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))

/-- The root of a level of `2^k` nodes. -/
def rootOfLevelM : ℕ → List Digest → m Digest
  | 0, level => pure (level.getD 0 default)
  | k + 1, level => do rootOfLevelM k (← parentsM H level (2 ^ k))

/-- The authentication path of node `i` of a level of `2^k` nodes. -/
def pathOfLevelM : ℕ → List Digest → ℕ → m (List Digest)
  | 0, _, _ => pure []
  | k + 1, level, i => do
    let up ← parentsM H level (2 ^ k)
    let rest ← pathOfLevelM k up (i / 2)
    pure (level.getD (MerkleTree.sibling i) default :: rest)

/-- The leaf hashes of the `2^height` rows of a word. -/
def leafHashesM (height : ℕ) (word : Word) : m (List Digest) :=
  (List.range (2 ^ height)).mapM fun i ↦ H ((word i).flatMap kBytes)

/-- The Merkle root of the `2^height` rows of a word. -/
def treeRootM (height : ℕ) (word : Word) : m Digest := do
  rootOfLevelM H height (← leafHashesM H height word)

/-- The opening of a word's tree at position `q`. -/
def openingAtM (height : ℕ) (word : Word) (q : ℕ) : m Opening := do
  let path ← pathOfLevelM H height (← leafHashesM H height word) (q % 2 ^ height)
  pure ⟨word (q % 2 ^ height), path⟩

/-- The proof-of-work step of a nonce: absorbed with tag `4`, then a challenge squeezed. -/
def powStepM (sp : Sponge) (n : E) : m (E × Sponge) := do
  let sp' ← Compile.absorb F sp n dsPowNonce
  squeeze F sp'

/-- The nonce search at the sponge `sp`: the first nonce of `ns` whose challenge passes. -/
def searchM (bits : ℕ) (sp : Sponge) : List ℕ → m (Option E)
  | [] => pure none
  | n :: ns => do
    let r ← powStepM F sp (nonceOf n)
    if powOk bits (nonceOf n) r.1 then pure (some (nonceOf n)) else searchM bits sp ns

/-- The proof-of-work search: at `bits = 0` the nonce `0`; otherwise the first nonce below
`fuel` that passes. -/
def findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) : m (Option E) :=
  if bits = 0 then pure (some (nonceOf 0)) else searchM F bits sp (List.range fuel)

/-- The honest prover from a history `h` at sponge `sp` (`proveFrom`). -/
def proveFromM (S : Strategy) (fuel : ℕ) {α : Type} :
    Prog α → Sponge → List Ev → m (Option (List E × List Opening))
  | .ret _, _, _ => pure (some ([], []))
  | .fail, _, _ => pure (some ([], []))
  | .read k, sp, h => do
    let sp' ← Compile.absorb F sp (S.msg h) dsObserve
    let r ← proveFromM S fuel (k (S.msg h)) sp' (h ++ [Ev.read (S.msg h)])
    pure (r.map fun t ↦ (S.msg h :: t.1, t.2))
  | .sample k, sp, h => do
    let r ← squeeze F sp
    proveFromM S fuel (k r.1) r.2 (h ++ [Ev.sample r.1])
  | .grind bits k, sp, h => do
    match ← findNonceM F bits sp fuel with
    | none => pure none
    | some n => do
      let r ← powStepM F sp n
      let t ← proveFromM S fuel k r.2 (h ++ [Ev.grind bits])
      pure (t.map fun t ↦ (n :: t.1, t.2))
  | .commit ht w k, sp, h => do
    let root ← treeRootM H ht (S.word h)
    let sp0 ← Compile.absorb F sp (digestScalars root).1 dsObserve
    let sp1 ← Compile.absorb F sp0 (digestScalars root).2 dsObserve
    let r ← proveFromM S fuel k sp1 (h ++ [Ev.commit ht w (S.word h)])
    pure (r.map fun t ↦ ((digestScalars root).1 :: (digestScalars root).2 :: t.1, t.2))
  | .query i ps k, sp, h => match (commits h)[i]? with
    | none => pure (some ([], []))
    | some (ht, _, word) => do
      let os ← ps.mapM (openingAtM H ht word)
      let r ← proveFromM S fuel (k (ps.map fun q ↦ word (q % 2 ^ ht))) sp
        (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))])
      pure (r.map fun t ↦ (t.1, os ++ t.2))

/-- **The honest prover**, with the hash and the permutation in any monad (`prove`). -/
def proveM (P : Prog Bool) (S : Strategy) (seed : KState) (fuel : ℕ) : m (Option Proof) := do
  let r ← proveFromM H F S fuel P ⟨seed, []⟩ []
  pure (r.map fun t ↦ ⟨t.1, t.2⟩)

end ProverM

/-! ## The `Id` instance is the pure prover -/

section Pure

variable (H : Bytes → Digest) (F : KState → KState)

theorem parentsM_id (level : List Digest) (n : ℕ) :
    parentsM (m := Id) H level n = (List.range n).map fun j ↦
      H (digestBytes (level.getD (2 * j) default) ++
        digestBytes (level.getD (2 * j + 1) default)) := by
  simp only [parentsM]
  exact List.idRun_mapM

/-- The parents of a level, as lists. -/
theorem parentsM_id_toList {k : ℕ} (level : Vector Digest (2 ^ (k + 1))) :
    parentsM (m := Id) H level.toList (2 ^ k) =
      (MerkleTree.parents (nodeHash H) level).toList := by
  rw [parentsM_id]
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp only [List.length_map, List.length_range] at h1
  have hj1 : 2 * j < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have hj2 : 2 * j + 1 < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  simp only [List.getElem_map, List.getElem_range, Vector.getElem_toList,
    MerkleTree.getElem_parents _ _ _ h1, nodeHash]
  rw [List.getD_eq_getElem _ _ (by simpa using hj1), List.getD_eq_getElem _ _ (by simpa using hj2)]
  simp

theorem rootOfLevelM_id :
    ∀ (k : ℕ) (level : Vector Digest (2 ^ k)),
      rootOfLevelM (m := Id) H k level.toList = MerkleTree.rootOfLevel (nodeHash H) k level
  | 0, level => by
    simp only [rootOfLevelM, MerkleTree.rootOfLevel]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp only [Vector.getElem_toList]
    rfl
  | k + 1, level => by
    simp only [rootOfLevelM, MerkleTree.rootOfLevel]
    show rootOfLevelM (m := Id) H k (parentsM (m := Id) H level.toList (2 ^ k)) = _
    rw [parentsM_id_toList, rootOfLevelM_id k]

theorem pathOfLevelM_id :
    ∀ (k : ℕ) (level : Vector Digest (2 ^ k)) (i : Fin (2 ^ k)),
      pathOfLevelM (m := Id) H k level.toList i =
        MerkleTree.pathOfLevel (nodeHash H) k level i
  | 0, _, _ => rfl
  | k + 1, level, i => by
    simp only [pathOfLevelM, MerkleTree.pathOfLevel]
    show (level.toList.getD (MerkleTree.sibling i) default ::
      pathOfLevelM (m := Id) H k (parentsM (m := Id) H level.toList (2 ^ k)) (i / 2)) = _
    rw [parentsM_id_toList, ← pathOfLevelM_id k _ ⟨i.val / 2, MerkleTree.div_two_lt i.isLt⟩,
      List.getD_eq_getElem _ _ (by simpa using MerkleTree.sibling_lt i.isLt)]
    simp

theorem leafHashesM_id (height : ℕ) (word : Word) :
    leafHashesM (m := Id) H height word = ((leavesOf height word).map (leafHash H)).toList := by
  simp only [leafHashesM]
  change Id.run (List.mapM _ _) = _
  rw [List.idRun_mapM]
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp [leavesOf, leafHash]
  rfl

theorem treeRootM_id (height : ℕ) (word : Word) :
    treeRootM (m := Id) H height word = treeRoot H height word := by
  show rootOfLevelM (m := Id) H height (leafHashesM (m := Id) H height word) = _
  rw [leafHashesM_id, rootOfLevelM_id]
  rfl

theorem openingAtM_id (height : ℕ) (word : Word) (q : ℕ) :
    openingAtM (m := Id) H height word q = openingAt H height word q := by
  show (⟨word (q % 2 ^ height), pathOfLevelM (m := Id) H height
    (leafHashesM (m := Id) H height word) (q % 2 ^ height)⟩ : Opening) = _
  rw [leafHashesM_id]
  have := pathOfLevelM_id H height ((leavesOf height word).map (leafHash H))
    ⟨q % 2 ^ height, Nat.mod_lt _ (Nat.two_pow_pos height)⟩
  simp only at this
  rw [this]
  rfl

theorem powStepM_id (sp : Sponge) (n : E) : powStepM (m := Id) F sp n = powStep F sp n := rfl

theorem searchM_id (bits : ℕ) (sp : Sponge) :
    ∀ ns : List ℕ, searchM (m := Id) F bits sp ns =
      (ns.find? fun n ↦ powOk bits (nonceOf n) (powStep F sp (nonceOf n)).1).map nonceOf
  | [] => rfl
  | n :: ns => by
    simp only [searchM, List.find?_cons]
    show (if powOk bits (nonceOf n) (powStep F sp (nonceOf n)).1 then _ else _) = _
    split <;> rename_i hp
    · simp only [hp, Option.map_some]; rfl
    · simp only [hp]; exact searchM_id bits sp ns

theorem findNonceM_id (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    findNonceM (m := Id) F bits sp fuel = findNonce F bits sp fuel := by
  unfold findNonceM findNonce
  split
  · rfl
  · exact searchM_id F bits sp _

theorem proveFromM_id (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : Prog α) (sp : Sponge) (h : List Ev),
      proveFromM (m := Id) H F S fuel p sp h = proveFrom H F S fuel p sp h
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, sp, h => by
    simp only [proveFromM, proveFrom]
    rw [← proveFromM_id S fuel]
    rfl
  | .sample k, sp, h => by
    simp only [proveFromM, proveFrom]
    rw [← proveFromM_id S fuel]
    rfl
  | .grind bits k, sp, h => by
    simp only [proveFromM, proveFrom]
    show (match findNonceM (m := Id) F bits sp fuel with
      | none => _ | some n => _) = _
    rw [findNonceM_id]
    cases findNonce F bits sp fuel
    · rfl
    · show Option.map _ (proveFromM (m := Id) H F S fuel k _ _) =
        Option.map _ (proveFrom H F S fuel k _ _)
      rw [proveFromM_id S fuel]
      rfl
  | .commit ht w k, sp, h => by
    simp only [proveFromM, proveFrom]
    show (proveFromM (m := Id) H F S fuel k _ _).map _ = _
    rw [treeRootM_id, proveFromM_id S fuel]
    rfl
  | .query i ps k, sp, h => by
    simp only [proveFromM, proveFrom]
    rcases (commits h)[i]? with _ | ⟨ht, w, word⟩
    · rfl
    · show (proveFromM (m := Id) H F S fuel _ sp _).map
        (fun t ↦ (t.1, Id.run (ps.mapM (openingAtM (m := Id) H ht word)) ++ t.2)) = _
      rw [List.idRun_mapM, proveFromM_id S fuel]
      simp only [Id.run, openingAtM_id]

/-- **The `Id` instance is the honest prover.** -/
theorem proveM_id (P : Prog Bool) (S : Strategy) (seed : KState) (fuel : ℕ) :
    proveM (m := Id) H F P S seed fuel = prove H F P S seed fuel := by
  show (proveFromM (m := Id) H F S fuel P ⟨seed, []⟩ []).map _ = _
  rw [proveFromM_id]
  rfl

end Pure

/-! ## Simulation commutes with the prover -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl HashSpec r)

theorem simulateQ_mapM {α β : Type} (f : α → OracleComp HashSpec β) :
    ∀ l : List α, simulateQ impl (l.mapM f) = l.mapM fun a ↦ simulateQ impl (f a)
  | [] => by simp
  | a :: l => by
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure]
    congr 1; funext b; rw [simulateQ_mapM f l]

theorem simulateQ_parentsM (level : List Digest) (n : ℕ) :
    simulateQ impl (parentsM queryH level n) = parentsM (implH impl) level n := by
  simp only [parentsM, simulateQ_mapM, simulateQ_queryH]

theorem simulateQ_rootOfLevelM :
    ∀ (k : ℕ) (level : List Digest),
      simulateQ impl (rootOfLevelM queryH k level) = rootOfLevelM (implH impl) k level
  | 0, _ => by simp [rootOfLevelM]
  | k + 1, level => by
    simp only [rootOfLevelM, simulateQ_bind, simulateQ_parentsM]
    congr 1; funext up; exact simulateQ_rootOfLevelM k up

theorem simulateQ_pathOfLevelM :
    ∀ (k : ℕ) (level : List Digest) (i : ℕ),
      simulateQ impl (pathOfLevelM queryH k level i) = pathOfLevelM (implH impl) k level i
  | 0, _, _ => by simp [pathOfLevelM]
  | k + 1, level, i => by
    simp only [pathOfLevelM, simulateQ_bind, simulateQ_parentsM, simulateQ_pure]
    congr 1; funext up; rw [simulateQ_pathOfLevelM k up]

theorem simulateQ_leafHashesM (height : ℕ) (word : Word) :
    simulateQ impl (leafHashesM queryH height word) = leafHashesM (implH impl) height word := by
  simp only [leafHashesM, simulateQ_mapM, simulateQ_queryH]

theorem simulateQ_treeRootM (height : ℕ) (word : Word) :
    simulateQ impl (treeRootM queryH height word) = treeRootM (implH impl) height word := by
  simp only [treeRootM, simulateQ_bind, simulateQ_leafHashesM, simulateQ_rootOfLevelM]

theorem simulateQ_openingAtM (height : ℕ) (word : Word) (q : ℕ) :
    simulateQ impl (openingAtM queryH height word q) =
      openingAtM (implH impl) height word q := by
  simp only [openingAtM, simulateQ_bind, simulateQ_leafHashesM, simulateQ_pathOfLevelM,
    simulateQ_pure]

theorem simulateQ_powStepM (sp : Sponge) (n : E) :
    simulateQ impl (powStepM queryF sp n) = powStepM (implF impl) sp n := by
  simp only [powStepM, simulateQ_bind, simulateQ_absorb, simulateQ_squeeze]

theorem simulateQ_searchM (bits : ℕ) (sp : Sponge) :
    ∀ ns : List ℕ, simulateQ impl (searchM queryF bits sp ns) =
      searchM (implF impl) bits sp ns
  | [] => by simp [searchM]
  | n :: ns => by
    simp only [searchM, simulateQ_bind, simulateQ_powStepM]
    congr 1; funext r
    split
    · simp
    · exact simulateQ_searchM bits sp ns

theorem simulateQ_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    simulateQ impl (findNonceM queryF bits sp fuel) = findNonceM (implF impl) bits sp fuel := by
  unfold findNonceM
  split
  · simp
  · exact simulateQ_searchM impl bits sp _

theorem simulateQ_proveFromM (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : Prog α) (sp : Sponge) (h : List Ev),
      simulateQ impl (proveFromM queryH queryF S fuel p sp h) =
        proveFromM (implH impl) (implF impl) S fuel p sp h
  | .ret _, _, _ => by simp [proveFromM]
  | .fail, _, _ => by simp [proveFromM]
  | .read k, sp, h => by
    simp only [proveFromM, simulateQ_bind, simulateQ_absorb, simulateQ_pure]
    congr 1; funext sp'; rw [simulateQ_proveFromM S fuel]
  | .sample k, sp, h => by
    simp only [proveFromM, simulateQ_bind, simulateQ_squeeze]
    congr 1; funext r; exact simulateQ_proveFromM S fuel _ _ _
  | .grind bits k, sp, h => by
    simp only [proveFromM, simulateQ_bind, simulateQ_findNonceM]
    congr 1; funext o
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_powStepM, simulateQ_pure]
      congr 1; funext r; rw [simulateQ_proveFromM S fuel]
  | .commit ht w k, sp, h => by
    simp only [proveFromM, simulateQ_bind, simulateQ_treeRootM, simulateQ_absorb,
      simulateQ_pure]
    congr 1; funext root; congr 1; funext sp0; congr 1; funext sp1
    rw [simulateQ_proveFromM S fuel]
  | .query i ps k, sp, h => by
    simp only [proveFromM]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_mapM, simulateQ_openingAtM, simulateQ_pure]
      congr 1; funext os; rw [simulateQ_proveFromM S fuel]

/-- **The prover commutes with simulation.** -/
theorem simulateQ_proveM (P : Prog Bool) (S : Strategy) (seed : KState) (fuel : ℕ) :
    simulateQ impl (proveM queryH queryF P S seed fuel) =
      proveM (implH impl) (implF impl) P S seed fuel := by
  simp only [proveM, simulateQ_bind, simulateQ_proveFromM, simulateQ_pure]

end Commute

/-! ## From a log's answers to a hash function and a permutation -/

/-- A hash function and a permutation, as an implementation of the oracles in `Id`. -/
def totalImpl (H : Bytes → Digest) (F : KState → KState) : QueryImpl HashSpec Id
  | .inl x => H x
  | .inr s => F s

theorem implH_totalImpl (H : Bytes → Digest) (F : KState → KState) :
    implH (totalImpl H F) = H := rfl

theorem implF_totalImpl (H : Bytes → Digest) (F : KState → KState) :
    implF (totalImpl H F) = F := rfl

/-- **From the log to a hash function and a permutation.** A computation that returns `r` when
every query is answered by the log `ℓ` returns `r` when every query is answered by a hash
function and a permutation that agree with the log. -/
theorem simulateQ_id_of_look {β : Type} (ℓ : Log) (H : Bytes → Digest) (F : KState → KState)
    (hH : ∀ x u, lookH ℓ x = some u → H x = u) (hF : ∀ s u, lookF ℓ s = some u → F s = u)
    (oa : OracleComp HashSpec β) :
    ∀ r : β, simulateQ (lookImpl ℓ) oa = some r → simulateQ (totalImpl H F) oa = r := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro r h
    simp only [simulateQ_pure] at h ⊢
    exact Option.some.inj h
  | query_bind t mx ih =>
    intro r h
    rw [simulateQ_query_bind] at h ⊢
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id] at h ⊢
    change (logLookup ℓ t).bind (fun u ↦ simulateQ (lookImpl ℓ) (mx u)) = some r at h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    change simulateQ (totalImpl H F) (mx (totalImpl H F t)) = r
    have ht : totalImpl H F t = u := by
      rcases t with x | s
      · exact hH x u hu
      · exact hF s u hu
    rw [ht]
    exact ih u r h

/-! ## The prover's queries -/

section Queries

theorem isTotalQueryBound_mapM {α β : Type} (f : α → OracleComp HashSpec β) (c : ℕ)
    (hf : ∀ a, IsTotalQueryBound (f a) c) :
    ∀ l : List α, IsTotalQueryBound (l.mapM f) (l.length * c)
  | [] => trivial
  | a :: l => by
    simp only [List.mapM_cons, List.length_cons]
    rw [show (l.length + 1) * c = c + (l.length * c + 0) by ring]
    exact isTotalQueryBound_bind (hf a) fun _ ↦ isTotalQueryBound_bind
      (isTotalQueryBound_mapM f c hf l) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem isTotalQueryBound_parentsM (level : List Digest) (n : ℕ) :
    IsTotalQueryBound (parentsM queryH level n) n := by
  have := isTotalQueryBound_mapM (β := Digest) (fun j : ℕ ↦ queryH (digestBytes
    (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))) 1
    (fun _ ↦ isTotalQueryBound_queryH_bind (f := pure) _ fun _ ↦ isTotalQueryBound_pure' _ 0
      |>.mono (by simp)) (List.range n)
  simpa [parentsM, queryH] using this

theorem isTotalQueryBound_rootOfLevelM :
    ∀ (k : ℕ) (level : List Digest), IsTotalQueryBound (rootOfLevelM queryH k level) (2 ^ k)
  | 0, _ => trivial
  | k + 1, level => by
    simp only [rootOfLevelM]
    rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by ring]
    exact isTotalQueryBound_bind (isTotalQueryBound_parentsM level _) fun up ↦
      isTotalQueryBound_rootOfLevelM k up

theorem isTotalQueryBound_pathOfLevelM :
    ∀ (k : ℕ) (level : List Digest) (i : ℕ),
      IsTotalQueryBound (pathOfLevelM queryH k level i) (2 ^ k)
  | 0, _, _ => trivial
  | k + 1, level, i => by
    simp only [pathOfLevelM]
    rw [show 2 ^ (k + 1) = 2 ^ k + (2 ^ k + 0) by ring]
    exact isTotalQueryBound_bind (isTotalQueryBound_parentsM level _) fun up ↦
      isTotalQueryBound_bind (isTotalQueryBound_pathOfLevelM k up _) fun _ ↦
        isTotalQueryBound_pure' _ 0

theorem isTotalQueryBound_leafHashesM (height : ℕ) (word : Word) :
    IsTotalQueryBound (leafHashesM queryH height word) (2 ^ height) := by
  have := isTotalQueryBound_mapM (β := Digest) (fun i : ℕ ↦ queryH ((word i).flatMap kBytes)) 1
    (fun _ ↦ isTotalQueryBound_queryH_bind (f := pure) _ fun _ ↦ isTotalQueryBound_pure' _ 0
      |>.mono (by simp)) (List.range (2 ^ height))
  simpa [leafHashesM, queryH] using this

theorem isTotalQueryBound_treeRootM (height : ℕ) (word : Word) :
    IsTotalQueryBound (treeRootM queryH height word) (2 ^ (height + 1)) := by
  unfold treeRootM
  rw [show 2 ^ (height + 1) = 2 ^ height + 2 ^ height by ring]
  exact isTotalQueryBound_bind (isTotalQueryBound_leafHashesM height word) fun l ↦
    isTotalQueryBound_rootOfLevelM height l

theorem isTotalQueryBound_openingAtM (height : ℕ) (word : Word) (q : ℕ) :
    IsTotalQueryBound (openingAtM queryH height word q) (2 ^ (height + 1)) := by
  unfold openingAtM
  rw [show 2 ^ (height + 1) = 2 ^ height + (2 ^ height + 0) by ring]
  exact isTotalQueryBound_bind (isTotalQueryBound_leafHashesM height word) fun l ↦
    isTotalQueryBound_bind (isTotalQueryBound_pathOfLevelM height l _) fun _ ↦
      isTotalQueryBound_pure' _ 0

/-- An absorption queries at most once. -/
theorem isTotalQueryBound_absorb_le {β : Type} (sp : Sponge) (x : E) (tag : ℕ)
    {g : Sponge → OracleComp HashSpec β} {n : ℕ} (hg : ∀ sp', IsTotalQueryBound (g sp') n) :
    IsTotalQueryBound (Compile.absorb queryF sp x tag >>= g) (n + 1) := by
  rw [absorb_bind]
  split
  · exact isTotalQueryBound_queryF_bind _ fun st ↦ hg _
  · exact (hg _).mono (Nat.le_succ n)

/-- A squeeze queries once. -/
theorem isTotalQueryBound_squeeze_le {β : Type} (sp : Sponge)
    {g : E × Sponge → OracleComp HashSpec β} {n : ℕ} (hg : ∀ r, IsTotalQueryBound (g r) n) :
    IsTotalQueryBound (squeeze queryF sp >>= g) (n + 1) := by
  rw [squeeze_bind]
  exact isTotalQueryBound_queryF_bind _ fun st ↦ hg _

/-- A proof-of-work step queries at most twice. -/
theorem isTotalQueryBound_powStepM_le {β : Type} (sp : Sponge) (n : E)
    {g : E × Sponge → OracleComp HashSpec β} {c : ℕ} (hg : ∀ r, IsTotalQueryBound (g r) c) :
    IsTotalQueryBound (powStepM queryF sp n >>= g) (c + 2) := by
  simp only [powStepM, bind_assoc]
  exact isTotalQueryBound_absorb_le _ _ _ fun sp' ↦ isTotalQueryBound_squeeze_le _ hg

theorem isTotalQueryBound_searchM (bits : ℕ) (sp : Sponge) :
    ∀ ns : List ℕ, IsTotalQueryBound (searchM queryF bits sp ns) (2 * ns.length)
  | [] => trivial
  | n :: ns => by
    simp only [searchM, List.length_cons]
    rw [show 2 * (ns.length + 1) = 2 * ns.length + 2 by ring]
    refine isTotalQueryBound_powStepM_le _ _ fun r ↦ ?_
    split
    · trivial
    · exact isTotalQueryBound_searchM bits sp ns

theorem isTotalQueryBound_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    IsTotalQueryBound (findNonceM queryF bits sp fuel) (2 * fuel) := by
  unfold findNonceM
  split
  · trivial
  · simpa using isTotalQueryBound_searchM bits sp (List.range fuel)

/-- The query cost of one quarter of a program's cost: an opening or a commitment rebuilds a
tree of height at most `height`, a proof of work searches `fuel` nonces at two queries each. -/
def proverFactor (height fuel : ℕ) : ℕ := 2 ^ (height + 1) + 2 * fuel + 2

theorem one_le_proverFactor (height fuel : ℕ) : 1 ≤ proverFactor height fuel := by
  unfold proverFactor; exact Nat.succ_le_of_lt (by positivity)

theorem fuel_le_proverFactor (height fuel : ℕ) :
    2 * fuel + 2 ≤ proverFactor height fuel := by
  unfold proverFactor; rw [Nat.add_assoc]; exact Nat.le_add_left _ _

theorem pow_le_proverFactor (height fuel : ℕ) :
    2 ^ (height + 1) + 2 ≤ proverFactor height fuel := by
  unfold proverFactor; exact Nat.add_le_add_right (Nat.le_add_right _ _) 2

/-- **The prover's queries.** From a history whose commitments have height at most `height`, the
prover runs a program of cost `n` (`Prog.Costs`, in quarters) with at most
`n · proverFactor height fuel` queries. -/
theorem isTotalQueryBound_proveFromM (S : Strategy) (fuel height : ℕ) {α : Type} :
    ∀ (p : Prog α) (sp : Sponge) (h : List Ev) (n : ℕ) (Q : α → Prop), p.Costs height n Q →
      (∀ c ∈ commits h, c.1 ≤ height) →
      IsTotalQueryBound (proveFromM queryH queryF S fuel p sp h) (n * proverFactor height fuel)
  | .ret _, _, _, _, _, _, _ => trivial
  | .fail, _, _, _, _, _, _ => trivial
  | .read k, sp, h, n, Q, hp, hs => by
    simp only [proveFromM]
    have hs' : ∀ c ∈ commits (h ++ [Ev.read (S.msg h)]), c.1 ≤ height := by
      simpa [commits_append, commits] using hs
    refine (isTotalQueryBound_absorb_le (n := (n - 1) * proverFactor height fuel + 0) _ _ _
      fun sp' ↦ isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height _ sp'
        (h ++ [Ev.read (S.msg h)]) (n - 1) Q (hp.2 _) hs') fun _ ↦
          isTotalQueryBound_pure' _ 0).mono ?_
    have h1 := hp.1
    have hF := one_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
    omega
  | .sample k, sp, h, n, Q, hp, hs => by
    simp only [proveFromM]
    refine (isTotalQueryBound_squeeze_le (n := (n - 4) * proverFactor height fuel) _
      fun r ↦ isTotalQueryBound_proveFromM S fuel height _ r.2
        (h ++ [Ev.sample r.1]) (n - 4) Q (hp.2 _)
          (by simpa [commits_append, commits] using hs)).mono ?_
    have h1 := hp.1
    have hF := one_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul]
    nlinarith
  | .grind bits k, sp, h, n, Q, hp, hs => by
    simp only [proveFromM]
    have hs' : ∀ c ∈ commits (h ++ [Ev.grind bits]), c.1 ≤ height := by
      simpa [commits_append, commits] using hs
    refine (isTotalQueryBound_bind (isTotalQueryBound_findNonceM bits sp fuel)
      (n₂ := (n - 5) * proverFactor height fuel + 0 + 2) fun o ↦ ?_).mono ?_
    · split
      · trivial
      · exact isTotalQueryBound_powStepM_le (c := (n - 5) * proverFactor height fuel + 0) _ _
          fun r ↦ isTotalQueryBound_bind
          (isTotalQueryBound_proveFromM S fuel height k r.2 (h ++ [Ev.grind bits]) (n - 5) Q
            hp.2 hs') fun _ ↦ isTotalQueryBound_pure' _ 0
    · have h1 := hp.1
      have hF := fuel_le_proverFactor height fuel
      generalize proverFactor height fuel = F at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 5 := ⟨n - 5, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul]
      nlinarith
  | .commit ht w k, sp, h, n, Q, hp, hs => by
    simp only [proveFromM]
    have hs' : ∀ c ∈ commits (h ++ [Ev.commit ht w (S.word h)]), c.1 ≤ height := by
      simp only [commits_append, commits, List.mem_append, List.mem_singleton]
      rintro c (hc | rfl)
      · exact hs c hc
      · exact hp.1
    refine (isTotalQueryBound_bind (isTotalQueryBound_treeRootM ht (S.word h))
      (n₂ := (n - 2) * proverFactor height fuel + 0 + 1 + 1) fun root ↦
        isTotalQueryBound_absorb_le _ _ _ fun sp0 ↦ isTotalQueryBound_absorb_le _ _ _ fun sp1 ↦
          isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height k sp1
            (h ++ [Ev.commit ht w (S.word h)]) (n - 2) Q hp.2.2 hs') fun _ ↦
              isTotalQueryBound_pure' _ 0).mono ?_
    have h1 := hp.2.1
    have h2 : 2 ^ (ht + 1) ≤ 2 ^ (height + 1) := Nat.pow_le_pow_right (by norm_num) (by
      have := hp.1; omega)
    have hF := pow_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    generalize 2 ^ (height + 1) = A at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul]
    omega
  | .query i ps k, sp, h, n, Q, hp, hs => by
    simp only [proveFromM]
    split
    · trivial
    · rename_i ht w word hc
      have hht : ht ≤ height := hs _ (List.mem_of_getElem? hc)
      have hs' : ∀ c ∈ commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]),
          c.1 ≤ height := by
        simpa [commits_append, commits] using hs
      refine (isTotalQueryBound_bind (isTotalQueryBound_mapM _ _
        (isTotalQueryBound_openingAtM ht word) ps)
        (n₂ := (n - Prog.openCost height ps.length) * proverFactor height fuel + 0) fun os ↦
          isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height _ sp _ _ Q (hp.2 _)
            hs') fun _ ↦ isTotalQueryBound_pure' _ 0).mono ?_
      have h1 := hp.1
      have h2 : 2 ^ (ht + 1) ≤ proverFactor height fuel :=
        (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
          ((Nat.le_add_right _ 2).trans (pow_le_proverFactor height fuel))
      have h3 : ps.length * 2 ^ (ht + 1) ≤
          Prog.openCost height ps.length * proverFactor height fuel :=
        calc ps.length * 2 ^ (ht + 1) ≤ ps.length * proverFactor height fuel :=
              Nat.mul_le_mul_left _ h2
          _ ≤ Prog.openCost height ps.length * proverFactor height fuel := by
              refine Nat.mul_le_mul_right _ ?_
              unfold Prog.openCost
              nlinarith
      generalize proverFactor height fuel = F at *
      generalize Prog.openCost height ps.length = O at *
      obtain ⟨d, hd⟩ : ∃ d, n = O + d := ⟨n - O, by omega⟩
      rw [hd, Nat.add_sub_cancel_left, Nat.add_mul]
      omega

/-- **The honest prover's queries**: at most `n · proverFactor height fuel` for a program of
cost `n` at `height`. -/
theorem isTotalQueryBound_proveM {P : Prog Bool} {height n : ℕ} (hP : P.CostLE height n)
    (S : Strategy) (seed : KState) (fuel : ℕ) :
    IsTotalQueryBound (proveM queryH queryF P S seed fuel) (n * proverFactor height fuel) := by
  unfold proveM
  rw [← Nat.add_zero (n * _)]
  exact isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height P ⟨seed, []⟩ [] n _ hP
    (by simp [commits])) fun _ ↦ isTotalQueryBound_pure' _ 0

end Queries

end
end LeanVM.Protocol.Compile
