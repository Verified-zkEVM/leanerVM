/-
  LeanVM.Guest.Batch.Rom

  The batching in the random-oracle model: the batching program accepts children with a false
  claim with probability at most the number of queries times `2/|E|`, plus the hash's collision
  terms.
-/

module

public import LeanVM.Guest.Batch.RomSpec
public import LeanVM.Protocol.EndToEnd.Sound.Statements

/-!
# The batching in the random-oracle model

The statements are the child counts `n < M`, for `M ≤ 2^64 - 1` (so that the count's power of
the generator names it, `gpow_injOn`). A statement's seeding is the batching's: the label's
hash, then the count absorbed (`batchSeeds`); its root is one read naming it, never absorbed
(the indexing of `LeanVM.Protocol.EndToEnd.Sound.Statements`), at which the program of every
statement (`batchAny`) is the batching program `batchProg bytecode n`.

The certificate (`batchCert`): past a statement's root and the reads of children of the
bytecode's shapes with a nonzero gap, the doom of `restSpec` on the rest of the history; nothing
is doomed before. `batch_rom`: an adversary of `QA` queries outputs a child count and a proof;
the probability that the batching program, BLAKE2s a random oracle, accepts while the proof's
stream begins with the cells of children of the bytecode's shapes one of whose claims is false
(`FalseChildren`) is at most `(QA + QV) · (2/|E| + failBound (QA + QV))`, `QV` the program's
query bound (`batchQueryBound`).

With `runProof_batchProg`, the program is `Node.batch` with its final check that the deferred
claim holds; so the bound is that of the batching itself, BLAKE2s modelled as the oracle.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.Rom LeanVM.Node LeanVM.Guest.B1.Main OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-- **The batching program of every child count**: a read naming the count, then the batching
of that many children. -/
noncomputable def batchAny (bytecode : List K) : Prog Bool :=
  .read fun e ↦ batchProg bytecode (kNat (e.limb 0))

/-- The root of the child count `n`: its read. -/
def countRoot (n : ℕ) : List Ev := [Ev.read (wordE (K.ofBits n))]

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The children's cells -/

/-- Children of the bytecode's shapes have `childLen` cells each. -/
theorem length_flatMap_childCells {bytecode : List K} :
    ∀ {cs : List ChildClaims}, (∀ c ∈ cs, ChildShaped bytecode c) →
      (cs.flatMap childCells).length = cs.length * childLen (Nat.log2 bytecode.length)
  | [], _ => by simp
  | c :: cs, hs => by
    rw [List.flatMap_cons, List.length_append, length_childCells (hs c List.mem_cons_self),
      length_flatMap_childCells fun c' hc' ↦ hs c' (List.mem_cons_of_mem _ hc'),
      List.length_cons, Nat.succ_mul]
    omega

/-- **The cells name the children**, for children of the bytecode's shapes. -/
theorem eq_of_flatMap_childCells {bytecode : List K} :
    ∀ {cs cs' : List ChildClaims}, (∀ c ∈ cs, ChildShaped bytecode c) →
      (∀ c ∈ cs', ChildShaped bytecode c) → cs.flatMap childCells = cs'.flatMap childCells →
      cs = cs'
  | [], [], _, _, _ => rfl
  | [], c :: cs', _, _, h => by simp [childCells] at h
  | c :: cs, [], _, _, h => by simp [childCells] at h
  | c :: cs, c' :: cs', hs, hs', h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by
      rw [length_childCells (hs c List.mem_cons_self),
        length_childCells (hs' c' List.mem_cons_self)])
    have hc : some c = some c' := by
      rw [← parseChild_childCells (hs c List.mem_cons_self),
        ← parseChild_childCells (hs' c' List.mem_cons_self), h1]
    rw [Option.some.inj hc, eq_of_flatMap_childCells (fun x hx ↦ hs x (List.mem_cons_of_mem _ hx))
      (fun x hx ↦ hs' x (List.mem_cons_of_mem _ hx)) h2]

/-! ## The program along the children's reads -/

/-- `n` reads, along `n` scalars read, return them. -/
theorem after_readN : ∀ xs : List E,
    (Prog.readN xs.length).after (xs.map Ev.read) = some (.ret xs)
  | [] => rfl
  | x :: xs => by
    simp only [List.length_cons, Prog.readN, Prog.bind_eq, Prog.readE, Prog.bind, List.map_cons,
      Prog.after, Prog.pure_eq]
    rw [Prog.after_bind_of_after _ _ _ (after_readN xs)]
    rfl

/-- A child's read, along its cells, returns it. -/
theorem after_readChild {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    (readChild (Nat.log2 bytecode.length)).after ((childCells c).map Ev.read) = some (.ret c) := by
  have h := after_readN (childCells c)
  rw [length_childCells hc] at h
  simp only [readChild, Prog.bind_eq]
  rw [Prog.after_bind_of_after _ _ _ h, Prog.ret_bind, parseChild_childCells hc]
  rfl

/-- The children's reads, along their cells, return them. -/
theorem after_readChildren {bytecode : List K} :
    ∀ {cs : List ChildClaims}, (∀ c ∈ cs, ChildShaped bytecode c) →
      (readChildren (Nat.log2 bytecode.length) cs.length).after
        ((cs.flatMap childCells).map Ev.read) = some (.ret cs)
  | [], _ => rfl
  | c :: cs, hs => by
    simp only [List.length_cons, readChildren, Prog.bind_eq, Prog.pure_eq, List.flatMap_cons,
      List.map_append]
    rw [Prog.after_bind_append _ (after_readChild (hs c List.mem_cons_self)),
      Prog.after_bind_of_after _ _ _
        (after_readChildren fun x hx ↦ hs x (List.mem_cons_of_mem _ hx))]
    rfl

/-- **Past the children's cells, the batching is `batchRest`.** -/
theorem after_batchProg {bytecode : List K} {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (l : List Ev) :
    (batchProg bytecode cs.length).after ((cs.flatMap childCells).map Ev.read ++ l) =
      (batchRest bytecode cs).after l :=
  Prog.after_bind_append _ (after_readChildren hs) l

/-- After the child count's root, the program of every count is the batching of that count. -/
theorem after_countRoot (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) (l : List Ev) :
    (batchAny bytecode).after (countRoot n ++ l) = (batchProg bytecode n).after l := by
  simp only [countRoot, List.singleton_append, batchAny, Prog.after, limb_wordE, kNat_ofBits hn]

theorem nodeAt_countRoot (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) :
    nodeAt (batchAny bytecode) (countRoot n) = batchProg bytecode n := by
  rw [nodeAt, ← List.append_nil (countRoot n), after_countRoot bytecode hn]
  simp [Prog.after]

/-- A child count's root is a root of `batchAny`. -/
theorem rootOk_countRoot (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) :
    RootOk (batchAny bytecode) (countRoot n) := by
  have ha : (batchAny bytecode).after (countRoot n) = some (batchProg bytecode n) := by
    rw [← List.append_nil (countRoot n)]
    exact (after_countRoot bytecode hn []).trans (by simp [Prog.after])
  exact ⟨reachable_of_after_reads [wordE (K.ofBits n)] ha,
    boundary_map_read (l := [wordE (K.ofBits n)]) (by simp),
    grindBits_map_read [wordE (K.ofBits n)], commits_map_read [wordE (K.ofBits n)],
    by rw [ha]; rfl⟩

/-! ## The batching after its children: no proof of work -/

theorem movesOK_sampleLB : ∀ n, MovesOK (· ≤ 64) False (sampleLB n)
  | 0 => trivial
  | n + 1 => MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq MovesOK.sampleE fun _ ↦
      MovesOK.seq (movesOK_sampleLB n) fun _ ↦ trivial

theorem movesOK_sampleLM : ∀ n, MovesOK (· ≤ 64) False (sampleLM n)
  | 0 => trivial
  | n + 1 => MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq MovesOK.sampleE fun _ ↦
      MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_sampleLM n) fun _ ↦ trivial

theorem movesOK_roundsProg : ∀ (k : ℕ) (claim : E), MovesOK (· ≤ 64) False (roundsProg claim k)
  | 0, _ => trivial
  | k + 1, _ => MovesOK.seq MovesOK.readE fun _ ↦ MovesOK.seq MovesOK.readE fun _ ↦
      MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_roundsProg k _) fun _ ↦ trivial

theorem movesOK_require (q : Prop) (inst : Decidable q) :
    MovesOK (· ≤ 64) False (@Prog.require q inst) :=
  MovesOK.require q

theorem movesOK_batchRest (bytecode : List K) (cs : List ChildClaims) :
    MovesOK (· ≤ 64) False (batchRest bytecode cs) := by
  unfold batchRest
  generalize 2 * blake2sR1csLogSize = m
  refine MovesOK.seq (movesOK_sampleLB _) fun _ ↦ ?_
  refine MovesOK.seq (movesOK_roundsProg _ _) fun _ ↦ ?_
  refine MovesOK.seq (movesOK_sampleLM _) fun _ ↦ ?_
  refine MovesOK.seq (movesOK_roundsProg _ _) fun _ ↦ ?_
  refine MovesOK.seq MovesOK.readE fun _ ↦ ?_
  refine MovesOK.seq MovesOK.readE fun _ ↦ ?_
  refine MovesOK.seq MovesOK.readE fun _ ↦ ?_
  exact MovesOK.seq (movesOK_require _ _) fun _ ↦ trivial

/-! ## The seedings -/

theorem batchLabel_length : batchLabel.length = 31 := by
  rw [batchLabel, String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
  decide +kernel

/-- The last pending input of a batching seeding: the label's digest and the count's block. -/
theorem pend_batchSeed {H : Bytes → Option Digest} {b t : Bytes}
    (h : pend H ⟨batchLabel, [([], b)]⟩ = some (t, true)) : ∃ d, t = digestBytes d ++ b := by
  simp only [pend] at h
  split at h
  · simp at h
  · rename_i d hd
    simp only [goPend, Seed.input, List.nil_append] at h
    split at h
    · simp only [List.isEmpty_nil, Option.some.injEq, Prod.mk.injEq, and_true] at h
      exact ⟨d, h.symm⟩
    · simp at h

/-- **The batching's seedings**: for the child count `n`, the label's hash, then the count
absorbed. -/
def batchSeeds (M : ℕ) (hM : M ≤ 2 ^ 64 - 1) : Seeds (Fin M) where
  seed x := ⟨batchLabel, [([], blockOf (ofK (gpow x)) 1)]⟩
  root x := countRoot x
  steps := []
  steps_mem x a ha := by
    simp only [List.mem_singleton] at ha
    exact Or.inr (by rw [ha])
  last x := ⟨_, blockOf_length _ _, rfl⟩
  first_len _ := by
    show batchLabel.length ≠ 64
    rw [batchLabel_length]
    decide
  mid_len x a ha d := by simp at ha
  inj H hH x x' t hx hx' := by
    obtain ⟨d, rfl⟩ := pend_batchSeed hx
    obtain ⟨d', ht⟩ := pend_batchSeed hx'
    have hk := ofK_injective (chainInput_inj ht).2.1
    have := x.2
    have := x'.2
    exact Fin.ext (gpow_injOn (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr (by omega)) hk)

theorem batchSeeds_seed (M : ℕ) (hM : M ≤ 2 ^ 64 - 1) (x : Fin M) :
    (batchSeeds M hM).seed x = ⟨batchLabel, [([], blockOf (ofK (gpow x)) 1)]⟩ ∧
      (batchSeeds M hM).root x = countRoot x ∧ (batchSeeds M hM).steps = [] :=
  ⟨rfl, rfl, rfl⟩

/-! ## The certificate -/

/-- **A batching's doomed prefix**: fewer than `2^64` children of the bytecode's shapes, with a
nonzero gap. -/
structure BatchPre (bytecode : List K) where
  /-- The children. -/
  cs : List ChildClaims
  /-- Their count is a word. -/
  lt : cs.length < 2 ^ 64
  /-- They have the bytecode's shapes. -/
  shaped : ∀ c ∈ cs, ChildShaped bytecode c
  /-- Some claim leaves a nonzero gap. -/
  gap : SomeGap bytecode cs

namespace BatchPre

variable {bytecode : List K}

/-- The history of a prefix: the child count's root, then the children's cells read. -/
def hist (p : BatchPre bytecode) : List Ev :=
  countRoot p.cs.length ++ (p.cs.flatMap childCells).map Ev.read

/-- The certificate of the batching after a prefix's children: `restSpec`'s. -/
noncomputable def cert (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (p : BatchPre bytecode) : Cert (batchRest bytecode p.cs) :=
  (restSpec hb p.shaped p.gap).toCertOfLead

theorem hist_eq (p : BatchPre bytecode) :
    p.hist = (wordE (K.ofBits p.cs.length) :: p.cs.flatMap childCells).map Ev.read := rfl

theorem after_hist (p : BatchPre bytecode) :
    (batchAny bytecode).after p.hist = some (batchRest bytecode p.cs) := by
  rw [hist, after_countRoot bytecode p.lt, ← List.append_nil (List.map _ _),
    after_batchProg p.shaped]
  simp [Prog.after]

theorem commits_hist (p : BatchPre bytecode) : commits p.hist = [] := by
  rw [hist_eq]; exact commits_map_read _

theorem grindBits_hist (p : BatchPre bytecode) (h' : List Ev) :
    grindBits (p.hist ++ h') = grindBits h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · rw [List.append_nil, hist_eq]; exact grindBits_map_read _
  · rw [List.concat_eq_append, ← List.append_assoc]
    simp [grindBits]

/-- **Prefixes are prefix-free**: two prefixes on one history are one prefix. -/
theorem hist_inj {p q : BatchPre bytecode} {h' h'' : List Ev}
    (he : p.hist ++ h' = q.hist ++ h'') : p = q ∧ h' = h'' := by
  simp only [hist, countRoot, List.cons_append, List.nil_append, List.cons.injEq,
    Ev.read.injEq] at he
  obtain ⟨h0, he⟩ := he
  have hl : p.cs.length = q.cs.length := ofBits_injective p.lt q.lt (wordE_injective h0)
  obtain ⟨e1, e2⟩ := List.append_inj he (by
    simp only [List.length_map, length_flatMap_childCells p.shaped,
      length_flatMap_childCells q.shaped, hl])
  have hcs := eq_of_flatMap_childCells p.shaped q.shaped
    (List.map_injective_iff.mpr (fun a b h ↦ Ev.read.inj h) e1)
  refine ⟨?_, e2⟩
  cases p
  cases q
  subst hcs
  rfl

end BatchPre

/-- **Doom of the batching**: past a prefix, the doom of its certificate on the rest. -/
def batchD {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (h : List Ev) : Prop :=
  ∃ (p : BatchPre bytecode) (h' : List Ev), h = p.hist ++ h' ∧ (p.cert hb).D h'

open Classical in
/-- The batching's escape bound: its certificate's past a prefix, `0` elsewhere. -/
noncomputable def batchCertε {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (h : List Ev) : ℝ≥0∞ :=
  if hx : ∃ (p : BatchPre bytecode) (h' : List Ev), h = p.hist ++ h' then
    (hx.choose.cert hb).ε hx.choose_spec.choose
  else 0

section Cert

variable {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)

theorem batchD_iff (p : BatchPre bytecode) (h' : List Ev) :
    batchD hb (p.hist ++ h') ↔ (p.cert hb).D h' := by
  constructor
  · rintro ⟨q, h'', he, hD⟩
    obtain ⟨rfl, rfl⟩ := BatchPre.hist_inj he
    exact hD
  · intro hD
    exact ⟨p, h', rfl, hD⟩

theorem batchCertε_eq (p : BatchPre bytecode) (h' : List Ev) :
    batchCertε hb (p.hist ++ h') = (p.cert hb).ε h' := by
  have key : ∀ (q : BatchPre bytecode) (h'' : List Ev), p.hist ++ h' = q.hist ++ h'' →
      (q.cert hb).ε h'' = (p.cert hb).ε h' := by
    intro q h'' he
    obtain ⟨rfl, rfl⟩ := BatchPre.hist_inj he
    rfl
  unfold batchCertε
  split
  · rename_i hx
    exact key _ _ hx.choose_spec.choose_spec
  · rename_i hx
    exact absurd ⟨p, h', rfl⟩ hx

end Cert

/-- **The batching's certificate.** -/
noncomputable def batchCert {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) : Cert (batchAny bytecode) where
  D := batchD hb
  ε := batchCertε hb
  read := by
    intro h k e hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, batchD_iff]
    exact (p.cert hb).read e (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp
  grind := by
    intro h b k hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, batchD_iff]
    exact (p.cert hb).grind (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp
  commit := by
    intro h ht w k word hr ha hw hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, batchD_iff]
    exact (p.cert hb).commit word (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hw hDp
  group := by
    intro h q hr hbd ha hq hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [esc_drop (h₀ := p.hist) p.commits_hist (batchD_iff hb p), batchCertε_eq]
    exact (p.cert hb).group (reachable_drop hap p.commits_hist hr h' rfl)
      (boundary_drop hbd) (by rwa [after_drop hap] at ha) hq hDp
  final := by
    intro h hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    exact (p.cert hb).final (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group, is at most `2/|E|`. -/
theorem batchCert_bound {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (batchCert hb).ε h ≤ batchε := by
  by_cases hx : ∃ (p : BatchPre bytecode) (h' : List Ev), h = p.hist ++ h'
  · obtain ⟨p, h', rfl⟩ := hx
    show _ * batchCertε hb _ ≤ _
    rw [batchCertε_eq, p.grindBits_hist]
    by_cases hr : (batchRest bytecode p.cs).Reachable h'
    · rw [min_eq_left ((movesOK_batchRest bytecode p.cs).grindBits_le hr)]
      exact Spec.toCertOfLead_bound _ le_rfl h'
    · simp only [BatchPre.cert, Spec.toCertOfLead, Spec.toCert_ε, hr, false_and, ↓reduceIte,
        mul_zero, zero_le]
  · show _ * batchCertε hb _ ≤ _
    simp only [batchCertε, hx, ↓reduceDIte, mul_zero, zero_le]

/-! ## The query bound -/

section Costs

open Prog

theorem costs_liftOption {α : Type} (o : Option α) (n : ℕ) :
    Costs 0 (liftOption o) n fun _ ↦ True := by
  cases o <;> trivial

theorem costs_require (q : Prop) (inst : Decidable q) (n : ℕ) :
    Costs 0 (@Prog.require q inst) n fun _ ↦ q :=
  Costs.require q

theorem costs_readChild (nB : ℕ) : Costs 0 (readChild nB) (childLen nB) fun _ ↦ True :=
  Costs.seq (Costs.readN _) (fun _ _ ↦ costs_liftOption _ _) le_rfl

theorem costs_readChildren (nB : ℕ) :
    ∀ n, Costs 0 (readChildren nB n) (n * childLen nB) fun cs ↦ cs.length = n
  | 0 => rfl
  | n + 1 => by
    refine Costs.seq (costs_readChild nB) (fun c _ ↦ ?_) (by rw [Nat.succ_mul]; omega)
    refine Costs.seq (costs_readChildren nB n) (fun cs hcs ↦ ?_) (by rw [Nat.succ_mul]; omega)
    show (c :: cs).length = n + 1
    simp [hcs]

theorem costs_sampleLB : ∀ n, Costs 0 (sampleLB n) (2 * n) fun _ ↦ True
  | 0 => trivial
  | n + 1 => by
    refine Costs.seq Costs.sampleE (fun _ _ ↦ ?_) (by omega)
    refine Costs.seq Costs.sampleE (fun _ _ ↦ ?_) (by omega)
    exact Costs.seq (costs_sampleLB n) (fun _ _ ↦ trivial) (by omega)

theorem costs_sampleLM : ∀ n, Costs 0 (sampleLM n) (3 * n) fun _ ↦ True
  | 0 => trivial
  | n + 1 => by
    refine Costs.seq Costs.sampleE (fun _ _ ↦ ?_) (by omega)
    refine Costs.seq Costs.sampleE (fun _ _ ↦ ?_) (by omega)
    refine Costs.seq Costs.sampleE (fun _ _ ↦ ?_) (by omega)
    exact Costs.seq (costs_sampleLM n) (fun _ _ ↦ trivial) (by omega)

theorem costs_roundsProg : ∀ (k : ℕ) (claim : E), Costs 0 (roundsProg claim k) (3 * k) fun _ ↦ True
  | 0, _ => trivial
  | k + 1, _ => by
    refine Costs.seq Costs.readE (fun _ _ ↦ ?_) (by omega)
    refine Costs.seq Costs.readE (fun _ _ ↦ ?_) (by omega)
    refine Costs.seq Costs.sampleE (fun _ _ ↦ ?_) (by omega)
    exact Costs.seq (costs_roundsProg k _) (fun _ _ ↦ trivial) (by omega)

/-- The batching after `n` children costs `5n` lambdas, `3` per round, and the `3` final reads. -/
theorem costs_batchRest (bytecode : List K) {cs : List ChildClaims} {n : ℕ} (hn : cs.length = n) :
    CostLE 0 (batchRest bytecode cs)
      (5 * n + 3 * Nat.log2 bytecode.length + 3 * (2 * blake2sR1csLogSize) + 3) := by
  unfold batchRest
  generalize 2 * blake2sR1csLogSize = m
  refine Costs.seq (costs_sampleLB _) (fun _ _ ↦ ?_) (by omega)
  refine Costs.seq (costs_roundsProg _ _) (fun _ _ ↦ ?_) (by omega)
  refine Costs.seq (costs_sampleLM _) (fun _ _ ↦ ?_) (by omega)
  refine Costs.seq (costs_roundsProg _ _) (fun _ _ ↦ ?_) (by omega)
  refine Costs.seq Costs.readE (fun _ _ ↦ ?_) (by omega)
  refine Costs.seq Costs.readE (fun _ _ ↦ ?_) (by omega)
  refine Costs.seq Costs.readE (fun _ _ ↦ ?_) (by omega)
  exact Costs.seq (costs_require _ _ 0) (fun _ _ ↦ trivial) (by omega)

/-- **The batching of `n` children costs** their cells, then the rest. -/
theorem costs_batchProg (bytecode : List K) (n : ℕ) :
    CostLE 0 (batchProg bytecode n)
      (n * childLen (Nat.log2 bytecode.length) +
        (5 * n + 3 * Nat.log2 bytecode.length + 3 * (2 * blake2sR1csLogSize) + 3)) :=
  Costs.bind (costs_readChildren _ n) fun _ hcs ↦ costs_batchRest bytecode hcs

end Costs

/-- The batching program's query bound on child counts below `M`. -/
def batchQueryBound (bytecode : List K) (M : ℕ) : ℕ :=
  2 + M * (childLen (Nat.log2 bytecode.length) + 5) + 3 * Nat.log2 bytecode.length +
    3 * (2 * blake2sR1csLogSize) + 3

/-- The proof's stream begins with the cells of `n` children of the bytecode's shapes, one of
whose claims is false. -/
def FalseChildren (bytecode : List K) (z : ℕ × Proof) : Prop :=
  ∃ cs : List ChildClaims, cs.length = z.1 ∧ (∀ c ∈ cs, ChildShaped bytecode c) ∧
    cs.flatMap childCells <+: z.2.stream ∧
    ¬ ∀ c ∈ cs, c.fresh.Holds bytecode ∧ c.carried.Holds bytecode

/-- The verifier of a child count below `M` makes at most `batchQueryBound` queries. -/
theorem isTotalQueryBound_batchFam {bytecode : List K} {M : ℕ} (hM : M ≤ 2 ^ 64 - 1)
    (z : Fin M × Proof) :
    IsTotalQueryBound (verifierFam (batchSeeds M hM) (batchAny bytecode) z)
      (batchQueryBound bytecode M) := by
  have hx := z.1.2
  have hz : (z.1 : ℕ) < 2 ^ 64 := by omega
  show IsTotalQueryBound (verifierComp ((batchSeeds M hM).seed z.1)
    (nodeAt (batchAny bytecode) (countRoot z.1)) z.2) _
  rw [nodeAt_countRoot bytecode hz]
  refine (isTotalQueryBound_verifierComp (costs_batchProg bytecode z.1) _ z.2).mono ?_
  have h1 := Nat.mul_le_mul_right (childLen (Nat.log2 bytecode.length) + 5) hx.le
  show 1 + 1 + _ ≤ _
  unfold batchQueryBound
  nlinarith [h1]

/-! ## Doom on accepted runs -/

/-- **An accepted run records the reads of its stream's first scalars**: along scalars the
program reads, the extracted history extends the start by their reads. -/
theorem xrun_reads (H : Bytes → Option Digest) {α : Type} :
    ∀ (l : List E) (p : Prog α) {q : Prog α} (s : St) (h : List Ev) {r : α × St × List Ev},
      p.after (l.map Ev.read) = some q → l <+: s.stream → xrun H p s h = some r →
      h ++ l.map Ev.read <+: r.2.2
  | [], p, _, s, h, ⟨a, s', hist⟩, _, _, hx => by simpa using xrun_prefix H p s h hx
  | x :: l, p, _, s, h, r, ha, hl, hx => by
    cases p
    case read k =>
      obtain ⟨t, ht⟩ := hl
      simp only [xrun, ← ht, List.cons_append] at hx
      obtain ⟨cv, -, hx⟩ := Option.bind_eq_some_iff.mp hx
      have := xrun_reads H l (k x) _ _ (by simpa [Prog.after] using ha) (List.prefix_append l t) hx
      simpa using this
    all_goals simp [Prog.after] at ha

/-- **False children leave a nonzero gap**: children of the bytecode's shapes with no nonzero
gap have true claims, `bytecode` of length a power of two. -/
theorem someGap_of_false {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c)
    (hn : ¬ ∀ c ∈ cs, c.fresh.Holds bytecode ∧ c.carried.Holds bytecode) :
    SomeGap bytecode cs := by
  by_contra hz
  refine hn fun c hc ↦ ?_
  have hz' : ∀ g ∈ gapsB bytecode cs ++ gapsM cs, g = 0 := fun g hg ↦ by
    by_contra h
    exact hz ⟨g, hg, h⟩
  have gB := fun g hg ↦ hz' g (List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hc, hg⟩))
  have gM := fun g hg ↦ hz' g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, hg⟩))
  have e1 := sub_eq_zero.mp (gB _ (List.mem_cons_self ..))
  have e2 := sub_eq_zero.mp (gB _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have e3 := sub_eq_zero.mp (gM _ (List.mem_cons_self ..))
  have e4 := sub_eq_zero.mp (gM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have e5 := sub_eq_zero.mp
    (gM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  refine ⟨⟨e1.symm, e3.symm⟩, (hs c hc).2, ?_, e2.symm, Prod.ext e4.symm e5.symm⟩
  rw [(hs c hc).2.1]
  exact hb.symm

/-- **False children doom an accepted run**: past the count's root and the children's reads,
`restSpec` is doomed at its start. -/
theorem doomed_of_falseChildren {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {M : ℕ} (hM : M ≤ 2 ^ 64 - 1)
    {z : Fin M × Proof} {c : HashSpec.QueryCache}
    (hv : Rom.verify (fun x ↦ c x) ((batchSeeds M hM).seed z.1)
      (nodeAt (batchAny bytecode) ((batchSeeds M hM).root z.1)) z.2 = some true)
    (hf : FalseChildren bytecode (z.1, z.2)) : Doomed (batchCert hb) (batchSeeds M hM) z c := by
  obtain ⟨cs, hlen, hs, hpre, hn⟩ := hf
  simp only at hlen hpre
  have hx := z.1.2
  have hz : (z.1 : ℕ) < 2 ^ 64 := by omega
  have hlt : cs.length < 2 ^ 64 := by rw [hlen]; exact hz
  let p : BatchPre bytecode := ⟨cs, hlt, hs, someGap_of_false hb hs hn⟩
  have hroot : (batchSeeds M hM).root z.1 = countRoot z.1 := rfl
  rw [hroot, nodeAt_countRoot bytecode hz] at hv
  refine ⟨p.hist, ?_, ?_, ?_, ?_⟩
  · rw [hroot, nodeAt_countRoot bytecode hz, extractedFrom_eq _ _ _ _ _ hv]
    show countRoot cs.length ++ _ <+: _
    rw [hlen]
    refine (List.prefix_append_right_inj _).mpr ?_
    obtain ⟨seed, s, -, hxr⟩ := xrun_of_verify hv
    have ha : (batchProg bytecode z.1).after ((cs.flatMap childCells).map Ev.read) =
        some (batchRest bytecode cs) := by
      rw [← hlen, ← List.append_nil (List.map _ _), after_batchProg hs]
      simp [Prog.after]
    simpa using xrun_reads _ _ _ _ [] ha hpre hxr
  · rw [hroot]
    simp [BatchPre.hist, countRoot, p]
  · rw [p.hist_eq]
    exact boundary_map_read (by simp)
  · show batchD hb p.hist
    exact ⟨p, [], by rw [List.append_nil], (restSpec hb p.shaped p.gap).start_D [] rfl⟩

/-- **The batching in the random-oracle model.** An adversary of `QA` queries outputs a child
count below `M` and a proof; the probability that the batching program, BLAKE2s a random
oracle, accepts while the proof begins with children of the bytecode's shapes one of whose
claims is false is at most `(QA + QV) · (2/|E| + failBound (QA + QV))`. -/
theorem batch_rom {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    {M : ℕ} (hM : M ≤ 2 ^ 64 - 1) (A : OracleComp HashSpec (Fin M × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam (batchSeeds M hM) (batchAny bytecode))}[
      z.1.2 = true ∧ FalseChildren bytecode (z.1.1.1, z.1.1.2)] ≤
      ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) *
        (batchε + failBound (batchSeeds M hM) (QA + batchQueryBound bytecode M)) :=
  romSound_of_imp (batchAny bytecode) (batchCert hb) (batchSeeds M hM)
    (fun x ↦ rootOk_countRoot bytecode (by have := x.2; omega)) batchε (batchCert_bound hb) A QA
    hA (batchQueryBound bytecode M) (isTotalQueryBound_batchFam hM)
    (fun z _ ↦ FalseChildren bytecode (z.1, z.2))
    fun _ _ hv hf ↦ doomed_of_falseChildren hb hM hv hf

/-- The verifier of a child count and a proof is the batching program from the batching's
seeding. -/
theorem verifierFam_batch {bytecode : List K} {M : ℕ} (hM : M ≤ 2 ^ 64 - 1)
    (z : Fin M × Proof) :
    verifierFam (batchSeeds M hM) (batchAny bytecode) z =
      verifierComp ⟨batchLabel, [([], blockOf (ofK (gpow z.1)) 1)]⟩ (batchProg bytecode z.1)
        z.2 := by
  have hx := z.1.2
  show verifierComp _ (nodeAt (batchAny bytecode) (countRoot z.1)) z.2 = _
  rw [nodeAt_countRoot bytecode (by omega)]
  rfl

end
end LeanVM.Guest.Batch
