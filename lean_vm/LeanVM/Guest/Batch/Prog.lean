/-
  LeanVM.Guest.Batch.Prog

  The batching as a program of the verifier language: the count, the children's claims and the
  sumcheck's messages are prover scalars, the lambdas and the sumcheck's challenges are samples.
-/

module

public import LeanVM.Guest.Batch.Sound

/-!
# The batching as a verifier program

`Node.batch` runs on the duplex sponge of the verifier language: `observe` is a read's
absorption (tag `1`) and `sample` a sample's squeeze. So the batching is a program
`batchAny M bytecode` (`LeanVM.Protocol.Compile.Prog`) whose prover sends the count `g^n` and
three zeros, each child's words and the zeros to a whole rate (`childCells`), the sumcheck's
messages and the final value, and whose challenges are the lambdas and the sumcheck's challenges.
It reads the count as the `n < M` with `g^n` the first scalar (`countOf`), checks the padding,
the final claim, and that the deferred claim holds of `bytecode`, then accepts.

`runProof_batchAny`: run with Keccak-256 and Keccak-f[1600] from the batching's seed
(`batchSeed`), on the stream of the count, children of the bytecode's shapes, the rounds of its
size and the final value (`batchStream`), it accepts exactly where `batch` defers a claim that
holds. So the random-oracle theorem of this program (`LeanVM.Guest.Batch.Rom`) is the batching's,
Keccak-256 and Keccak-f[1600] modelled as random oracles. The final value is read (absorbed)
after the last challenge, where `batch` takes it from the hints: the absorption changes no
challenge.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## Children -/

/-- The words of a child at `nB` bytecode coordinates: its public input's two, its proof's
claim, its statement's claim. -/
def childLen (nB : ℕ) : ℕ := 2 + (nB + 1) + (nB + 1)

/-- The zeros that pad `k` words to a whole rate. -/
def padLen (k : ℕ) : ℕ := (rateScalars - k % rateScalars) % rateScalars

/-- A child read off its words (`ChildClaims.words`), at `nB` bytecode coordinates; `none` where
the public input does not decode. -/
def parseChild (nB : ℕ) (xs : List E) : Option ChildClaims := do
  let pi ← digestOfScalars (xs.getD 0 0, xs.getD 1 0)
  let ys := xs.drop 2
  let zs := ys.drop (nB + 1)
  return ⟨pi, ⟨ys.take nB, ys.getD nB 0⟩, ⟨zs.take nB, zs.getD nB 0⟩⟩

/-- A child has the bytecode's shapes: its proof's claim and its statement's are at points of
`log₂` of the bytecode's length. -/
def ChildShaped (bytecode : List K) (c : ChildClaims) : Prop :=
  c.fresh.bytecodePoint.length = Nat.log2 bytecode.length ∧ c.carried.Shaped bytecode

/-- Read a child: its words, then the zeros to a whole rate. -/
def readChild (nB : ℕ) : Prog ChildClaims := do
  let xs ← Prog.readN (childLen nB + padLen (childLen nB))
  Prog.require (xs.drop (childLen nB) = List.replicate (padLen (childLen nB)) 0)
  liftOption (parseChild nB xs)

/-- Read `n` children. -/
def readChildren (nB : ℕ) : ℕ → Prog (List ChildClaims)
  | 0 => pure []
  | n + 1 => do
    let c ← readChild nB
    let cs ← readChildren nB n
    return c :: cs

open Classical in
/-- The count below `M` whose power of the generator is `x`, if any. -/
noncomputable def countOf (M : ℕ) (x : E) : Option ℕ :=
  if h : ∃ n, n < M ∧ Verifier.gpow n = x then some (Nat.find h) else none

/-- Read the count: `g^n`, then three zeros. -/
noncomputable def readCount (M : ℕ) : Prog ℕ := do
  let xs ← Prog.readN rateScalars
  Prog.require (xs.drop 1 = List.replicate (rateScalars - 1) 0)
  liftOption (countOf M (xs.getD 0 0))

/-! ## The lambdas and the rounds -/

/-- Sample a pair of lambdas per child. -/
def sampleL : ℕ → Prog (List (E × E))
  | 0 => pure []
  | n + 1 => do
    let a ← Prog.sampleE
    let b ← Prog.sampleE
    let l ← sampleL n
    return (a, b) :: l

/-- `k` rounds of the batching sumcheck from `claim`: read `g(1)` and `g(∞)`, sample the
challenge, fold. The challenges and the final claim. -/
def roundsProg : E → ℕ → Prog (List E × E)
  | claim, 0 => pure ([], claim)
  | claim, k + 1 => do
    let g1 ← Prog.readE
    let gInf ← Prog.readE
    let r ← Prog.sampleE
    let rest ← roundsProg (roundPoly claim (g1, gInf) r) k
    return (r :: rest.1, rest.2)

/-! ## The program -/

open Classical in
/-- **The batching after its children**: the lambdas and the sumcheck, the final value, the
final check, and the deferred claim true of `bytecode`. -/
noncomputable def batchRest (bytecode : List K) (cs : List ChildClaims) : Prog Bool := do
  let l ← sampleL cs.length
  let rb ← roundsProg (claimBOf cs l) (Nat.log2 bytecode.length)
  let bv ← Prog.readE
  Prog.require (rb.2 = bv * bytecodeWeight cs l rb.1 ∧
    DeferredClaim.Holds bytecode ⟨rb.1, bv⟩)
  return true

/-- **The batching of `n` children.** -/
noncomputable def batchProg (bytecode : List K) (n : ℕ) : Prog Bool := do
  let cs ← readChildren (Nat.log2 bytecode.length) n
  batchRest bytecode cs

/-- **The batching as a verifier program**, of fewer than `M` children: the count, then the
batching of that many. -/
noncomputable def batchAny (M : ℕ) (bytecode : List K) : Prog Bool := do
  let n ← readCount M
  batchProg bytecode n

/-- The prover's stream of a batching: the count's and the children's cells, the rounds'
messages, the final value. -/
def batchStream (cs : List ChildClaims) (h : BatchHints) : List E :=
  batchWords cs ++ h.bytecodeRounds.flatMap (fun g ↦ [g.1, g.2]) ++ [h.bytecodeValue]

/-! ## The cells -/

theorem padRate_eq (ws : List E) : padRate ws = ws ++ List.replicate (padLen ws.length) 0 := rfl

theorem length_words {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    c.words.length = childLen (Nat.log2 bytecode.length) := by
  obtain ⟨h1, h2⟩ := hc
  simp only [DeferredClaim.Shaped] at h2
  simp [ChildClaims.words, fixedCells, DeferredClaim.cells, childLen, h1, h2]
  omega

/-- A child of the bytecode's shapes has `childLen` words, then the padding. -/
theorem childCells_eq {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    childCells c = c.words ++
      List.replicate (padLen (childLen (Nat.log2 bytecode.length))) 0 := by
  rw [childCells, padRate_eq, length_words hc]

theorem length_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    (childCells c).length =
      childLen (Nat.log2 bytecode.length) + padLen (childLen (Nat.log2 bytecode.length)) := by
  rw [childCells_eq hc, List.length_append, length_words hc, List.length_replicate]

/-- A child of the bytecode's shapes is read back off its words. -/
theorem parseChild_words {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    parseChild (Nat.log2 bytecode.length) c.words = some c := by
  obtain ⟨pi, ⟨bp, bv⟩, ⟨bp', bv'⟩⟩ := c
  obtain ⟨h1, h2⟩ := hc
  simp only [DeferredClaim.Shaped] at h1 h2
  generalize Nat.log2 bytecode.length = nB at *
  subst h1
  simp [parseChild, ChildClaims.words, fixedCells, DeferredClaim.cells,
    digestOfScalars_digestScalars, List.getD_eq_getElem?_getD, List.drop_append, h2, List.drop_eq_nil_of_le]

/-- The padded words are read back off. -/
theorem parseChild_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    parseChild (Nat.log2 bytecode.length) (childCells c) = some c := by
  rw [← parseChild_words hc, childCells_eq hc]
  obtain ⟨pi, ⟨bp, bv⟩, ⟨bp', bv'⟩⟩ := c
  obtain ⟨h1, h2⟩ := hc
  simp only [DeferredClaim.Shaped] at h1 h2
  generalize Nat.log2 bytecode.length = nB at *
  subst h1
  simp [parseChild, ChildClaims.words, fixedCells, DeferredClaim.cells,
    List.getD_eq_getElem?_getD, List.drop_append, h2,
    List.drop_eq_nil_of_le]

theorem drop_childCells {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    (childCells c).drop (childLen (Nat.log2 bytecode.length)) =
      List.replicate (padLen (childLen (Nat.log2 bytecode.length))) 0 := by
  rw [childCells_eq hc, List.drop_left' (length_words hc)]

/-- The count's power is read back below `M ≤ 2^64 - 1`. -/
theorem countOf_gpow {M n : ℕ} (hM : M ≤ 2 ^ 64 - 1) (hn : n < M) :
    countOf M (Verifier.gpow n) = some n := by
  have hex : ∃ m, m < M ∧ Verifier.gpow m = Verifier.gpow n := ⟨n, hn, rfl⟩
  rw [countOf, dite_eq_left hex, Option.some.injEq]
  generalize hk : Nat.find hex = k at *
  obtain ⟨hlt, hs⟩ : k < M ∧ Verifier.gpow k = Verifier.gpow n := hk ▸ Nat.find_spec hex
  have hK : ∀ m, Verifier.gpow m = ofK (Parameters.gpow m) := fun m ↦ by
    show gen ^ m = algebraMap K E (g ^ m)
    rw [map_pow]
    rfl
  rw [hK k, hK n] at hs
  exact gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) (ofK_injective hs)

theorem headCells_eq (n : ℕ) : headCells n = [Verifier.gpow n, 0, 0, 0] := rfl

/-! ## The compiled run, piece by piece -/

/-- The deployed compiled run: Keccak-256 and Keccak-f[1600]. -/
abbrev runD {α : Type} (p : Prog α) (s : St) : Option (α × St) :=
  Id.run (run keccak256 keccakF p s)

/-- The compiled run of a sequence: the first program's, then the continuation's. -/
theorem runD_bind {α β : Type} (f : α → Prog β) :
    ∀ (p : Prog α) (s : St), runD (p.bind f) s =
      match runD p s with
      | some (a, s') => runD (f a) s'
      | none => none
  | .ret a, s => rfl
  | .fail, s => rfl
  | .read k, ⟨sp, [], os, roots⟩ => rfl
  | .read k, ⟨sp, x :: xs, os, roots⟩ => runD_bind f (k x) _
  | .sample k, s => runD_bind f (k _) _
  | .grind b k, ⟨sp, [], os, roots⟩ => rfl
  | .grind b k, ⟨sp, n :: xs, os, roots⟩ => by
    show (if _ then _ else _) = match (if _ then _ else _) with
      | some (a, s') => runD (f a) s'
      | none => none
    split
    · exact runD_bind f k _
    · rfl
  | .commit ht w k, ⟨sp, [], os, roots⟩ => rfl
  | .commit ht w k, ⟨sp, [x0], os, roots⟩ => rfl
  | .commit ht w k, ⟨sp, x0 :: x1 :: xs, os, roots⟩ => by
    show (match digestOfScalars (x0, x1) with | some root => _ | none => _) =
      match (match digestOfScalars (x0, x1) with | some root => _ | none => _) with
      | some (a, s') => runD (f a) s'
      | none => none
    split
    · exact runD_bind f k _
    · rfl
  | .query i ps k, s => by
    rcases h : s.roots[i]? with _ | ⟨root, height, width⟩
    · simp only [runD, Prog.bind, Compile.run, h]
      rfl
    · simp only [runD, Prog.bind, Compile.run, h]
      rcases ho : Id.run (openAll keccak256 root height width ps s.openings) with _ | ⟨rows, rest⟩
      · simp only [Id.run] at ho
        simp only [id_bind, ho]
        rfl
      · simp only [Id.run] at ho
        simp only [id_bind, ho]
        exact runD_bind f (k rows) _

/-- **`p` runs from the sponge `sp` on the scalars `xs`, returning `a` at the sponge `sp'`**,
whatever follows in the proof. -/
def RunsTo {α : Type} (p : Prog α) (sp : Sponge) (xs : List E) (a : α) (sp' : Sponge) : Prop :=
  ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
    runD p ⟨sp, xs ++ rest, os, roots⟩ = some (a, ⟨sp', rest, os, roots⟩)

theorem runsTo_ret {α : Type} (a : α) (sp : Sponge) : RunsTo (Prog.ret a) sp [] a sp :=
  fun _ _ _ ↦ rfl

theorem RunsTo.bind {α β : Type} {p : Prog α} {f : α → Prog β} {sp sp1 sp2 : Sponge}
    {xs ys : List E} {a : α} {b : β} (hp : RunsTo p sp xs a sp1)
    (hf : RunsTo (f a) sp1 ys b sp2) : RunsTo (p >>= f) sp (xs ++ ys) b sp2 := by
  intro rest os roots
  show runD (p.bind f) _ = _
  rw [runD_bind, List.append_assoc, hp]
  exact hf rest os roots

theorem RunsTo.of_eq {α : Type} {p : Prog α} {sp sp' : Sponge} {xs ys : List E} {a : α}
    (h : RunsTo p sp xs a sp') (hxy : xs = ys) : RunsTo p sp ys a sp' := hxy ▸ h

theorem runsTo_readE (sp : Sponge) (x : E) : RunsTo Prog.readE sp [x] x (obs sp x) :=
  fun _ _ _ ↦ rfl

theorem runsTo_sampleE (sp : Sponge) : RunsTo Prog.sampleE sp [] (sq sp).1 (sq sp).2 :=
  fun _ _ _ ↦ rfl

theorem runsTo_require {c : Prop} [Decidable c] (hc : c) (sp : Sponge) :
    RunsTo (Prog.require c) sp [] () sp := by
  intro rest os roots
  simp [Prog.require, hc]
  rfl

theorem runsTo_liftOption {α : Type} (a : α) (sp : Sponge) :
    RunsTo (liftOption (some a)) sp [] a sp := runsTo_ret a sp

theorem runsTo_readN (sp : Sponge) :
    ∀ xs : List E, RunsTo (Prog.readN xs.length) sp xs xs (obsAll sp xs)
  | [] => runsTo_ret _ _
  | x :: xs => by
    have h := (runsTo_readE sp x).bind (f := fun x ↦ do
        let xs ← Prog.readN xs.length
        return x :: xs)
      ((runsTo_readN (obs sp x) xs).bind (f := fun xs' ↦ (pure (x :: xs') : Prog (List E)))
        (runsTo_ret _ _))
    exact h.of_eq (by simp)

theorem runsTo_readN' (sp : Sponge) {n : ℕ} (xs : List E) (hn : xs.length = n) :
    RunsTo (Prog.readN n) sp xs xs (obsAll sp xs) := hn ▸ runsTo_readN sp xs

/-- A shaped child is read off its cells. -/
theorem runsTo_readChild {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c)
    (sp : Sponge) :
    RunsTo (readChild (Nat.log2 bytecode.length)) sp (childCells c) c
      (obsAll sp (childCells c)) := by
  have h := (runsTo_readN' sp (childCells c) (length_childCells hc)).bind
    (f := fun xs ↦ do
      Prog.require (xs.drop (childLen (Nat.log2 bytecode.length)) =
        List.replicate (padLen (childLen (Nat.log2 bytecode.length))) 0)
      liftOption (parseChild (Nat.log2 bytecode.length) xs))
    ((runsTo_require (drop_childCells hc) _).bind
      (f := fun _ ↦ liftOption (parseChild (Nat.log2 bytecode.length) (childCells c)))
      (by rw [parseChild_childCells hc]; exact runsTo_liftOption c _))
  exact h.of_eq (by simp)

/-- Shaped children are read off their cells. -/
theorem runsTo_readChildren {bytecode : List K} :
    ∀ {cs : List ChildClaims}, (∀ c ∈ cs, ChildShaped bytecode c) → ∀ sp : Sponge,
      RunsTo (readChildren (Nat.log2 bytecode.length) cs.length) sp (cs.flatMap childCells) cs
        (obsAll sp (cs.flatMap childCells))
  | [], _, sp => runsTo_ret _ sp
  | c :: cs, hs, sp => by
    have h := (runsTo_readChild (hs c List.mem_cons_self) sp).bind
      (f := fun c ↦ do
        let cs ← readChildren (Nat.log2 bytecode.length) cs.length
        return c :: cs)
      ((runsTo_readChildren (fun c' h' ↦ hs c' (List.mem_cons_of_mem c h')) _).bind
        (f := fun cs' ↦ (pure (c :: cs') : Prog (List ChildClaims))) (runsTo_ret _ _))
    rw [List.append_nil, ← obsAll_append, ← List.flatMap_cons] at h
    exact h

/-- The count is read off its cells. -/
theorem runsTo_readCount {M n : ℕ} (hM : M ≤ 2 ^ 64 - 1) (hn : n < M) (sp : Sponge) :
    RunsTo (readCount M) sp (headCells n) n (obsAll sp (headCells n)) := by
  have h := (runsTo_readN' sp (headCells n) rfl).bind
    (f := fun xs ↦ do
      Prog.require (xs.drop 1 = List.replicate (rateScalars - 1) 0)
      liftOption (countOf M (xs.getD 0 0)))
    ((runsTo_require (show (headCells n).drop 1 = List.replicate (rateScalars - 1) 0 from rfl)
      _).bind (f := fun _ ↦ liftOption (countOf M ((headCells n).getD 0 0)))
      (by rw [show (headCells n).getD 0 0 = Verifier.gpow n from rfl, countOf_gpow hM hn]
          exact runsTo_liftOption n _))
  exact h.of_eq (by simp)

/-- The lambdas are `sq2`'s. -/
theorem runsTo_sampleL :
    ∀ (n : ℕ) (sp : Sponge), RunsTo (sampleL n) sp [] (sq2 n sp).1 (sq2 n sp).2
  | 0, sp => runsTo_ret _ sp
  | n + 1, sp =>
    (runsTo_sampleE sp).bind
      (f := fun a ↦ do
        let b ← Prog.sampleE
        let l ← sampleL n
        return (a, b) :: l)
      ((runsTo_sampleE (sq sp).2).bind
        (f := fun b ↦ do
          let l ← sampleL n
          return ((sq sp).1, b) :: l)
        ((runsTo_sampleL n _).bind
          (f := fun l ↦ (pure (_ :: l) : Prog (List (E × E)))) (runsTo_ret _ _)))

/-- The rounds of the sumcheck are `rsRun`'s. -/
theorem runsTo_roundsProg : ∀ (rounds : List (E × E)) (claim : E) (sp : Sponge) {k : ℕ},
    rounds.length = k →
      RunsTo (roundsProg claim k) sp (rounds.flatMap fun g ↦ [g.1, g.2])
        (rsRun rounds claim sp).1 (rsRun rounds claim sp).2
  | [], claim, sp, _, hk => by subst hk; exact runsTo_ret _ sp
  | (g1, gInf) :: rounds, claim, sp, _, hk => by
    subst hk
    have h := (runsTo_readE sp g1).bind
      (f := fun g1 ↦ do
        let gInf ← Prog.readE
        let r ← Prog.sampleE
        let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
        return (r :: rest.1, rest.2))
      ((runsTo_readE (obs sp g1) gInf).bind
        (f := fun gInf ↦ do
          let r ← Prog.sampleE
          let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
          return (r :: rest.1, rest.2))
        ((runsTo_sampleE (obs (obs sp g1) gInf)).bind
          (f := fun r ↦ do
            let rest ← roundsProg (roundPoly claim (g1, gInf) r) rounds.length
            return (r :: rest.1, rest.2))
          ((runsTo_roundsProg rounds _ _ rfl).bind
            (f := fun rest ↦ (pure (_ :: rest.1, rest.2) : Prog (List E × E)))
            (runsTo_ret _ _))))
    exact h.of_eq (by simp)

/-- A check followed by acceptance. -/
theorem runD_require_true (c : Prop) [Decidable c] (s : St) :
    runD (Prog.require c >>= fun _ ↦ (pure true : Prog Bool)) s =
      if c then some (true, s) else none := by
  unfold Prog.require
  split_ifs <;> rfl

/-- A run continues where its first program's run ends. -/
theorem runD_bind_of_runsTo {α β : Type} {p : Prog α} {f : α → Prog β} {sp sp' : Sponge}
    {xs : List E} {a : α} (hp : RunsTo p sp xs a sp') (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    runD (p >>= f) ⟨sp, xs ++ rest, os, roots⟩ = runD (f a) ⟨sp', rest, os, roots⟩ := by
  show runD (p.bind f) _ = _
  rw [runD_bind, hp]

/-- **The program is the batching**: with Keccak-256 and Keccak-f[1600], from the batching's
seed, on the stream of fewer than `M` children of the bytecode's shapes and rounds of its size,
the program accepts exactly where `batch` defers a claim that holds of `bytecode`. -/
theorem runProof_batchAny {M : ℕ} (hM : M ≤ 2 ^ 64 - 1) {bytecode : List K}
    {cs : List ChildClaims} {h : BatchHints} (hn : cs.length < M)
    (hs : ∀ c ∈ cs, ChildShaped bytecode c)
    (hr : h.bytecodeRounds.length = Nat.log2 bytecode.length) :
    Id.run (runProof keccak256 keccakF (batchAny M bytecode) batchSeed
        ⟨batchStream cs h, []⟩) = true ↔
      ∃ d, batch cs h = some d ∧ d.Holds bytecode := by
  have hstream : batchStream cs h = headCells cs.length ++ (cs.flatMap childCells ++
      (h.bytecodeRounds.flatMap (fun g ↦ [g.1, g.2]) ++ [h.bytecodeValue])) := by
    simp only [batchStream, batchWords, List.append_assoc]
  show (match runD (batchAny M bytecode) ⟨⟨batchSeed, []⟩, batchStream cs h, [], []⟩ with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false) = true ↔ _
  have hsp : batchSponge cs = obsAll (obsAll ⟨batchSeed, []⟩ (headCells cs.length))
      (cs.flatMap childCells) := obsAll_append _ _ _
  rw [hstream, batchAny, runD_bind_of_runsTo (runsTo_readCount hM hn _), batchProg,
    runD_bind_of_runsTo (runsTo_readChildren hs _), ← hsp, batchRest,
    ← List.nil_append (List.flatMap _ _ ++ _),
    runD_bind_of_runsTo (runsTo_sampleL _ _),
    runD_bind_of_runsTo (runsTo_roundsProg h.bytecodeRounds _ _ hr),
    ← List.append_nil [h.bytecodeValue],
    runD_bind_of_runsTo (runsTo_readE _ _), runD_require_true, batch_eq']
  simp only [lambdasB, claimB, spB]
  split_ifs <;> simp_all

end
end LeanVM.Guest.Batch
