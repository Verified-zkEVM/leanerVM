/-
  LeanVM.Guest.Batch.Rom

  The batching in the random-oracle model: the batching program, with Keccak-256 and
  Keccak-f[1600] independent random oracles, accepts children with a false claim with probability
  at most the number of queries times `2/|E|` plus the oracles' collision terms.
-/

module

public import LeanVM.Guest.Batch.RomSpec
public import LeanVM.Protocol.EndToEnd.Sound.Statements

/-!
# The batching in the random-oracle model

The batching has no statement of its own: its sponge starts at `F(H(label) ‖ 0)`
(`FiatShamirState::from_label`, `batchSeed`), one seeding (`batchSeedOf`: a hash step, then the
permutation), and everything else, the child count included, is read from the proof
(`batchAny`). So the statements are a family of one (`batchSeeds : Seeds Unit`), its root the
empty history.

The certificate (`batchCert`): past the reads of the count and of fewer than `M` children of the
bytecode's shapes with a nonzero gap (`BatchPre`), the doom of `restSpec` on the rest of the
history; nothing is doomed before. `batch_rom`: an adversary of `QA` queries to the two oracles
together outputs a proof; the probability that the batching program, Keccak-256 and
Keccak-f[1600] random oracles, accepts while the proof's stream begins with the count and the
cells of fewer than `M` children of the bytecode's shapes one of whose claims is false
(`FalseChildren`) is at most `(QA + QV) · (2/|E| + 5 (QA + QV) / 2^256)`, `QV` the program's
query bound (`batchQueryBound`). `batch_rom_bits`: for `QA + QV ≤ 2^64` that is at most
`(QA + QV) · 2^-189`.

With `runProof_batchAny`, the program is `Node.batch` with its final check that the deferred
claim holds; so the bound is that of the batching itself, Keccak-256 and Keccak-f[1600] modelled
as random oracles.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Rom LeanVM.Node OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The seeding -/

/-- **The batching's seeding**: the label's hash, then the permutation of it beside a zero public
input (`FiatShamirState::from_label`). -/
def batchSeedOf : Seed where
  hs := [fun _ ↦ batchLabel]
  fin ds := seedInput (ds.getD 0 default) (Vector.replicate 4 0)

/-- The seeding, deployed, is the batching's seed. -/
theorem batchSeedOf_run : Id.run (batchSeedOf.run keccak256 keccakF) = batchSeed := rfl

/-- **The batching's statements**: one, its root the empty history. -/
def batchSeeds : Seeds Unit where
  seed _ := batchSeedOf
  root _ := []
  offs := []
  refs _ ds hds i hi := by
    left
    have hl : ds.length = 1 := hds
    have h0 : i = 0 := by omega
    subst h0
    show laneDigest (seedInput (ds.getD 0 default) _) = ds[0]
    rw [laneDigest_seedInput]
    simp [List.getD_eq_getElem?_getD, hi]
  cap0 _ _ := capOf_seedInput _ _
  inj _ _ _ _ _ _ _ _ _ := rfl

theorem rootOk_batch (M : ℕ) (bytecode : List K) : RootOk (batchAny M bytecode) [] :=
  ⟨Prog.Reachable.nil, trivial, rfl, rfl, rfl⟩

/-- The verifier of a proof is the batching program from the batching's seeding. -/
theorem verifierFam_batch (M : ℕ) (bytecode : List K) (z : Unit × Proof) :
    verifierFam batchSeeds (batchAny M bytecode) z =
      verifierComp batchSeedOf (batchAny M bytecode) z.2 := rfl

/-! ## The program along its reads -/

/-- `n` reads, along `n` scalars read, return them. -/
theorem after_readN : ∀ xs : List E,
    (Prog.readN xs.length).after (xs.map Ev.read) = some (.ret xs)
  | [] => rfl
  | x :: xs => by
    simp only [List.length_cons, Prog.readN, Prog.bind_eq, Prog.readE, Prog.bind, List.map_cons,
      Prog.after, Prog.pure_eq]
    rw [Prog.after_bind_of_after _ _ _ (after_readN xs)]
    rfl

theorem after_readN' {n : ℕ} (xs : List E) (hn : xs.length = n) :
    (Prog.readN n).after (xs.map Ev.read) = some (.ret xs) := hn ▸ after_readN xs

/-- A child's read, along its cells, returns it. -/
theorem after_readChild {bytecode : List K} {c : ChildClaims} (hc : ChildShaped bytecode c) :
    (readChild (Nat.log2 bytecode.length)).after ((childCells c).map Ev.read) =
      some (.ret c) := by
  simp only [readChild, Prog.bind_eq]
  rw [Prog.after_bind_of_after _ _ _ (after_readN' _ (length_childCells hc))]
  simp [Prog.require, drop_childCells hc, parseChild_childCells hc, Verifier.liftOption]

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

/-- The count's read, along its cells, returns it. -/
theorem after_readCount {M n : ℕ} (hM : M ≤ 2 ^ 64 - 1) (hn : n < M) :
    (readCount M).after ((headCells n).map Ev.read) = some (.ret n) := by
  simp only [readCount, Prog.bind_eq]
  rw [Prog.after_bind_of_after _ _ _ (after_readN' (n := rateScalars) (headCells n) rfl)]
  simp [Prog.require, headCells_eq, countOf_gpow hM hn, Verifier.liftOption, rateScalars]

/-- **Past the count's and the children's cells, the batching is `batchRest`.** -/
theorem after_batchAny {M : ℕ} (hM : M ≤ 2 ^ 64 - 1) {bytecode : List K} {cs : List ChildClaims}
    (hn : cs.length < M) (hs : ∀ c ∈ cs, ChildShaped bytecode c) (l : List Ev) :
    (batchAny M bytecode).after ((batchWords cs).map Ev.read ++ l) =
      (batchRest (DeferredClaim.Holds bytecode) bytecode cs).after l := by
  rw [batchWords, List.map_append, List.append_assoc]
  exact (Prog.after_bind_append _ (after_readCount hM hn) _).trans
    (Prog.after_bind_append _ (after_readChildren hs) l)

/-! ## The children's cells -/

/-- Children of the bytecode's shapes have `childLen` words and the padding each. -/
theorem length_flatMap_childCells {bytecode : List K} :
    ∀ {cs : List ChildClaims}, (∀ c ∈ cs, ChildShaped bytecode c) →
      (cs.flatMap childCells).length = cs.length *
        (childLen (Nat.log2 bytecode.length) + padLen (childLen (Nat.log2 bytecode.length)))
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
  | [], c :: cs', _, _, h => by
    have := congrArg List.length h
    simp [childCells, padRate_eq, ChildClaims.words] at this
  | c :: cs, [], _, _, h => by
    have := congrArg List.length h
    simp [childCells, padRate_eq, ChildClaims.words] at this
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

/-! ## The batching after its children: no proof of work -/

theorem movesOK_roundsProg : ∀ (k : ℕ) (claim : E), MovesOK (· ≤ 64) False (roundsProg claim k)
  | 0, _ => trivial
  | k + 1, _ => MovesOK.seq MovesOK.readE fun _ ↦ MovesOK.seq MovesOK.readE fun _ ↦
      MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_roundsProg k _) fun _ ↦ trivial

theorem movesOK_require (q : Prop) (inst : Decidable q) :
    MovesOK (· ≤ 64) False (@Prog.require q inst) :=
  MovesOK.require q

theorem movesOK_batchRest (bytecode : List K) (cs : List ChildClaims) :
    MovesOK (· ≤ 64) False (batchRest (DeferredClaim.Holds bytecode) bytecode cs) := by
  unfold batchRest
  refine MovesOK.seq MovesOK.sampleE fun _ ↦ ?_
  refine MovesOK.seq (movesOK_roundsProg _ _) fun _ ↦ ?_
  refine MovesOK.seq MovesOK.readE fun _ ↦ ?_
  exact MovesOK.seq (movesOK_require _ _) fun _ ↦ trivial

/-! ## The certificate -/

/-- **A batching's doomed prefix**: fewer than `M` children of the bytecode's shapes, with a
nonzero gap. -/
structure BatchPre (M : ℕ) (bytecode : List K) where
  /-- The children. -/
  cs : List ChildClaims
  /-- Fewer than `M`. -/
  lt : cs.length < M
  /-- They have the bytecode's shapes. -/
  shaped : ∀ c ∈ cs, ChildShaped bytecode c
  /-- Some claim leaves a nonzero gap. -/
  gap : SomeGap bytecode cs

namespace BatchPre

variable {M : ℕ} {bytecode : List K}

/-- The history of a prefix: the count's and the children's cells read. -/
def hist (p : BatchPre M bytecode) : List Ev := (batchWords p.cs).map Ev.read

/-- The certificate of the batching after a prefix's children: `restSpec`'s. -/
noncomputable def cert (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (p : BatchPre M bytecode) : Cert (batchRest (DeferredClaim.Holds bytecode) bytecode p.cs) :=
  (restSpec hb p.lt p.shaped p.gap).toCertOfLead

theorem after_hist (hM : M ≤ 2 ^ 64 - 1) (p : BatchPre M bytecode) :
    (batchAny M bytecode).after p.hist = some (batchRest (DeferredClaim.Holds bytecode) bytecode p.cs) := by
  rw [hist, ← List.append_nil (List.map _ _), after_batchAny hM p.lt p.shaped]
  simp [Prog.after]

theorem commits_hist (p : BatchPre M bytecode) : commits p.hist = [] := commits_map_read _

theorem grindBits_hist (p : BatchPre M bytecode) (h' : List Ev) :
    grindBits (p.hist ++ h') = grindBits h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · rw [List.append_nil]; exact grindBits_map_read _
  · rw [List.concat_eq_append, ← List.append_assoc]
    simp [grindBits]

/-- **Prefixes are prefix-free**: two prefixes on one history are one prefix. -/
theorem hist_inj (hM : M ≤ 2 ^ 64 - 1) {p q : BatchPre M bytecode} {h' h'' : List Ev}
    (he : p.hist ++ h' = q.hist ++ h'') : p = q ∧ h' = h'' := by
  simp only [hist, batchWords, headCells_eq, List.map_cons, List.cons_append, List.nil_append,
    List.cons.injEq, Ev.read.injEq] at he
  obtain ⟨h0, -, -, -, he⟩ := he
  have hl : p.cs.length = q.cs.length := by
    have := congrArg (countOf M) h0
    rwa [countOf_gpow hM p.lt, countOf_gpow hM q.lt, Option.some.injEq] at this
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

variable {M : ℕ} {bytecode : List K}

/-- **Doom of the batching**: past a prefix, the doom of its certificate on the rest. -/
def batchD (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (h : List Ev) : Prop :=
  ∃ (p : BatchPre M bytecode) (h' : List Ev), h = p.hist ++ h' ∧ (p.cert hb).D h'

open Classical in
/-- The batching's escape bound: its certificate's past a prefix, `0` elsewhere. -/
noncomputable def batchCertε (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (h : List Ev) : ℝ≥0∞ :=
  if hx : ∃ (p : BatchPre M bytecode) (h' : List Ev), h = p.hist ++ h' then
    (hx.choose.cert hb).ε hx.choose_spec.choose
  else 0

section Cert

variable (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)

theorem batchD_iff (hM : M ≤ 2 ^ 64 - 1) (p : BatchPre M bytecode) (h' : List Ev) :
    batchD (M := M) hb (p.hist ++ h') ↔ (p.cert hb).D h' := by
  constructor
  · rintro ⟨q, h'', he, hD⟩
    obtain ⟨rfl, rfl⟩ := BatchPre.hist_inj hM he
    exact hD
  · intro hD
    exact ⟨p, h', rfl, hD⟩

theorem batchCertε_eq (hM : M ≤ 2 ^ 64 - 1) (p : BatchPre M bytecode) (h' : List Ev) :
    batchCertε (M := M) hb (p.hist ++ h') = (p.cert hb).ε h' := by
  have key : ∀ (q : BatchPre M bytecode) (h'' : List Ev), p.hist ++ h' = q.hist ++ h'' →
      (q.cert hb).ε h'' = (p.cert hb).ε h' := by
    intro q h'' he
    obtain ⟨rfl, rfl⟩ := BatchPre.hist_inj hM he
    rfl
  unfold batchCertε
  split
  · rename_i hx
    exact key _ _ hx.choose_spec.choose_spec
  · rename_i hx
    exact absurd ⟨p, h', rfl⟩ hx

/-- **The batching's certificate.** -/
noncomputable def batchCert (hM : M ≤ 2 ^ 64 - 1) : Cert (batchAny M bytecode) where
  D := batchD (M := M) hb
  ε := batchCertε (M := M) hb
  read := by
    intro h k e hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist hM
    rw [List.append_assoc, batchD_iff hb hM]
    exact (p.cert hb).read e (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp
  grind := by
    intro h b k hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist hM
    rw [List.append_assoc, batchD_iff hb hM]
    exact (p.cert hb).grind (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp
  commit := by
    intro h ht w k word hr ha hw hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist hM
    rw [List.append_assoc, batchD_iff hb hM]
    exact (p.cert hb).commit word (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hw hDp
  group := by
    intro h q hr hbd ha hq hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist hM
    rw [esc_drop (h₀ := p.hist) p.commits_hist (batchD_iff hb hM p), batchCertε_eq hb hM]
    exact (p.cert hb).group (reachable_drop hap p.commits_hist hr h' rfl)
      (boundary_drop hbd) (by rwa [after_drop hap] at ha) hq hDp
  final := by
    intro h hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist hM
    exact (p.cert hb).final (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
challenge, is at most `batchε M`. -/
theorem batchCert_bound (hM : M ≤ 2 ^ 64 - 1) (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (batchCert hb hM).ε h ≤ batchε M := by
  by_cases hx : ∃ (p : BatchPre M bytecode) (h' : List Ev), h = p.hist ++ h'
  · obtain ⟨p, h', rfl⟩ := hx
    show _ * batchCertε hb _ ≤ _
    rw [batchCertε_eq hb hM, p.grindBits_hist]
    by_cases hr : (batchRest (DeferredClaim.Holds bytecode) bytecode p.cs).Reachable h'
    · rw [min_eq_left ((movesOK_batchRest bytecode p.cs).grindBits_le hr)]
      exact Spec.toCertOfLead_bound _ le_rfl h'
    · simp only [BatchPre.cert, Spec.toCertOfLead, Spec.toCert_ε, hr, false_and, ↓reduceIte,
        mul_zero, zero_le]
  · show _ * batchCertε hb _ ≤ _
    simp only [batchCertε, hx, ↓reduceDIte, mul_zero, zero_le]

end Cert

/-! ## The query bound -/

section Costs

open Prog

theorem costs_require (q : Prop) (inst : Decidable q) {n : ℕ} :
    Costs 0 (@Prog.require q inst) n fun _ ↦ q :=
  Costs.require q

theorem countOf_lt {M n : ℕ} {x : E} (h : countOf M x = some n) : n < M := by
  unfold countOf at h
  split at h
  · rename_i hx
    rw [Option.some.injEq] at h
    rw [← h]
    exact (Nat.find_spec hx).1
  · simp at h

theorem costs_readCount (M : ℕ) : Costs 0 (readCount M) rateScalars fun n ↦ n < M := by
  refine Costs.seq (Costs.readN _) (fun xs _ ↦ ?_) le_rfl
  refine Costs.seq (Costs.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  rcases h : countOf M (xs.getD 0 0) with _ | n
  · trivial
  · exact countOf_lt h

theorem costs_readChild (nB : ℕ) :
    Costs 0 (readChild nB) (childLen nB + padLen (childLen nB)) fun _ ↦ True := by
  refine Costs.seq (Costs.readN _) (fun xs _ ↦ ?_) le_rfl
  refine Costs.seq (Costs.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  cases parseChild nB xs <;> trivial

theorem costs_readChildren (nB : ℕ) :
    ∀ n, Costs 0 (readChildren nB n) (n * (childLen nB + padLen (childLen nB)))
      fun cs ↦ cs.length = n
  | 0 => rfl
  | n + 1 => by
    refine Costs.seq (costs_readChild nB) (fun c _ ↦ ?_) (by rw [Nat.succ_mul]; omega)
    refine Costs.seq (costs_readChildren nB n) (fun cs hcs ↦ ?_) (by rw [Nat.succ_mul]; omega)
    show (c :: cs).length = n + 1
    simp [hcs]

theorem costs_roundsProg : ∀ (k : ℕ) (claim : E), Costs 0 (roundsProg claim k) (6 * k) fun _ ↦ True
  | 0, _ => trivial
  | k + 1, _ => by
    refine Costs.seq Costs.readE (fun _ _ ↦ ?_) (by omega)
    refine Costs.seq Costs.readE (fun _ _ ↦ ?_) (by omega)
    refine Costs.seq Costs.sampleE (fun _ _ ↦ ?_) (by omega)
    exact Costs.seq (costs_roundsProg k _) (fun _ _ ↦ trivial) (by omega)

/-- The batching after its children costs `4` for the challenge, `6` per round, and the final
read. -/
theorem costs_batchRest (bytecode : List K) (cs : List ChildClaims) :
    CostLE 0 (batchRest (DeferredClaim.Holds bytecode) bytecode cs)
      (4 + 6 * Nat.log2 bytecode.length + 1) := by
  unfold batchRest
  refine Costs.seq Costs.sampleE (fun _ _ ↦ ?_) (by omega)
  refine Costs.seq (costs_roundsProg _ _) (fun _ _ ↦ ?_) (by omega)
  refine Costs.seq Costs.readE (fun _ _ ↦ ?_) (by omega)
  exact Costs.seq (costs_require _ _ (n := 0)) (fun _ _ ↦ trivial) (by omega)

/-- **The batching of fewer than `M` children costs** the count, at most `M` children's cells,
and the rest. -/
theorem costs_batchAny (M : ℕ) (bytecode : List K) :
    CostLE 0 (batchAny M bytecode)
      (rateScalars + (M * (childLen (Nat.log2 bytecode.length) +
        padLen (childLen (Nat.log2 bytecode.length))) + 4 + 6 * Nat.log2 bytecode.length + 1)) :=
  Costs.bind (costs_readCount M) fun n hn ↦
    (Costs.bind (costs_readChildren _ n) fun cs _ ↦ costs_batchRest bytecode cs).mono
      (by nlinarith) fun _ h ↦ h

end Costs

/-- The verifier makes at most `batchQueryBound` queries. -/
theorem isTotalQueryBound_batchFam (M : ℕ) (bytecode : List K) (z : Unit × Proof) :
    IsTotalQueryBound (verifierFam batchSeeds (batchAny M bytecode) z)
      (batchQueryBound bytecode M) :=
  isTotalQueryBound_verifierComp (costs_batchAny M bytecode) batchSeedOf z.2

/-! ## Doom on accepted runs -/

/-- **An accepted run records the reads of its stream's first scalars**: along scalars the
program reads, the extracted history extends the start by their reads. -/
theorem xrun_reads (H : Bytes → Option Digest) (F : KState → Option KState) {α : Type} :
    ∀ (l : List E) (p : Prog α) {q : Prog α} (s : St) (h : List Ev) {r : α × St × List Ev},
      p.after (l.map Ev.read) = some q → l <+: s.stream → xrun H F p s h = some r →
      h ++ l.map Ev.read <+: r.2.2
  | [], p, _, s, h, ⟨a, s', hist⟩, _, _, hx => by simpa using xrun_prefix H F p s h hx
  | x :: l, p, _, s, h, r, ha, hl, hx => by
    cases p
    case read k =>
      obtain ⟨t, ht⟩ := hl
      simp only [xrun, ← ht, List.cons_append] at hx
      obtain ⟨sp, -, hx⟩ := Option.bind_eq_some_iff.mp hx
      have := xrun_reads H F l (k x) _ _ (by simpa [Prog.after] using ha)
        (List.prefix_append l t) hx
      simpa using this
    all_goals simp [Prog.after] at ha

/-- **False children leave a nonzero gap**, `bytecode` of length a power of two. -/
theorem someGap_of_false (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    {cs : List ChildClaims} (hs : ∀ c ∈ cs, ChildShaped bytecode c)
    (hn : ¬ ∀ c ∈ cs, c.fresh.Holds bytecode ∧ c.carried.Holds bytecode) :
    SomeGap bytecode cs := by
  by_contra hz
  refine hn (holds_of_gaps (fun g hg ↦ ?_) hb.symm fun c hc ↦ (hs c hc).2)
  by_contra h
  exact hz ⟨g, hg, h⟩

/-- **False children doom an accepted run**: past their reads, `restSpec` is doomed at its
start. -/
theorem doomed_of_falseChildren (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hM : M ≤ 2 ^ 64 - 1) {z : Unit × Proof} {c : HashSpec.QueryCache}
    (hv : Rom.verify (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) (batchSeeds.seed z.1)
      (nodeAt (batchAny M bytecode) (batchSeeds.root z.1)) z.2 = some true)
    (hf : FalseChildren bytecode M z.2) : Doomed (batchCert hb hM) batchSeeds z c := by
  obtain ⟨cs, hlt, hs, hpre, hn⟩ := hf
  let p : BatchPre M bytecode := ⟨cs, hlt, hs, someGap_of_false hb hs hn⟩
  refine ⟨p.hist, ?_, Nat.zero_le _, ?_, ?_⟩
  · obtain ⟨seed, s, -, hxr⟩ := xrun_of_verify_from [] hv
    have ha : (batchAny M bytecode).after ((batchWords cs).map Ev.read) =
        some (batchRest (DeferredClaim.Holds bytecode) bytecode cs) := p.after_hist hM
    have h := xrun_reads _ _ _ _ _ [] ha hpre hxr
    rw [List.nil_append] at h
    exact h
  · exact boundary_map_read (by simp [batchWords, headCells_eq])
  · exact ⟨p, [], by rw [List.append_nil], (restSpec hb p.lt p.shaped p.gap).start_D [] rfl⟩

/-- **The batching in the random-oracle model.** An adversary of `QA` queries to Keccak-256 and
Keccak-f[1600], independent random oracles, outputs a proof; the probability that the batching
program accepts it while it begins with fewer than `M` children of the bytecode's shapes one of
whose claims is false is at most `(QA + QV) · (batchε M + failBound (QA + QV))`, `QV` the
program's query bound. -/
theorem batch_rom (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (hM : M ≤ 2 ^ 64 - 1)
    (A : OracleComp HashSpec (Unit × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam batchSeeds (batchAny M bytecode))}[
      z.1.2 = true ∧ FalseChildren bytecode M z.1.1.2] ≤
      ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) *
        (batchε M + failBound batchSeeds (QA + batchQueryBound bytecode M)) :=
  romSound_of_imp (batchAny M bytecode) (batchCert hb hM) batchSeeds
    (fun _ ↦ rootOk_batch M bytecode) (batchε M) (batchCert_bound hb hM) A QA hA
    (batchQueryBound bytecode M) (isTotalQueryBound_batchFam M bytecode)
    (fun z _ ↦ FalseChildren bytecode M z.2)
    fun _ _ hv hf ↦ doomed_of_falseChildren hb hM hv hf

/-! ## The bound in bits -/

/-- `2 max(M, 1)/|E| = max(M, 1) · 2^-191`. -/
theorem batchε_eq_pow (M : ℕ) : batchε M = (max M 1 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 191 := by
  have hc : ∀ inst : Fintype E, @Fintype.card E inst = 2 ^ 192 := fun inst ↦ by
    convert card_E
  rw [batchε, hc, inv_pow_eq_div 191 192 (by norm_num), show 192 - 191 = 1 from rfl, pow_one,
    mul_div_assoc']
  push_cast
  ring

/-- The failure term of the batching's one seeding: `5N/2^256`. -/
theorem failBound_batchSeeds (N : ℕ) :
    failBound batchSeeds N = ((5 * N : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  simp [failBound, batchSeeds]

/-- **The batching's error**, explicit: `Q · (max(M, 1) · 2^-191 + 5Q/2^256)` for `Q = QA + QV`
queries. -/
theorem batch_rom_explicit (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hM : M ≤ 2 ^ 64 - 1) (A : OracleComp HashSpec (Unit × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierFam batchSeeds (batchAny M bytecode))}[
      z.1.2 = true ∧ FalseChildren bytecode M z.1.1.2] ≤
      ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) * ((max M 1 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 191 +
        ((5 * (QA + batchQueryBound bytecode M) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  rw [← batchε_eq_pow, ← failBound_batchSeeds]
  exact batch_rom hb hM A QA hA

/-- `m · 2^-191 + 5N/2^256 ≤ m · 2^-189` for `m ≥ 1` and `N ≤ 2^64`. -/
theorem bits_189 {m N : ℕ} (hm : 1 ≤ m) (hN : N ≤ 2 ^ 64) :
    (m : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 191 + ((5 * N : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      (m : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 189 := by
  have h2 : (2 : ℝ≥0∞) ^ 256 = ((2 ^ 256 : ℕ) : ℝ≥0∞) := by rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [h2, inv_pow_eq_div 191 256 (by norm_num), inv_pow_eq_div 189 256 (by norm_num),
    ← mul_div_assoc, ← mul_div_assoc, ← Nat.cast_mul, ← Nat.cast_mul,
    ENNReal.div_add_div_same, ← Nat.cast_add]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [show 256 - 191 = 65 from rfl, show 256 - 189 = 67 from rfl]
  have : 5 * N ≤ 3 * m * 2 ^ 65 := by
    calc 5 * N ≤ 5 * 2 ^ 64 := by omega
      _ ≤ 3 * 1 * 2 ^ 65 := by norm_num
      _ ≤ 3 * m * 2 ^ 65 := by gcongr
  calc m * 2 ^ 65 + 5 * N ≤ m * 2 ^ 65 + 3 * m * 2 ^ 65 := by omega
    _ = m * 2 ^ 67 := by ring

/-- **The batching in the random-oracle model, in bits**: for `Q = QA + QV ≤ 2^64` queries to
Keccak-256 and Keccak-f[1600] together, the adversary and the batching program's, the program
accepts fewer than `M` children with a false claim with probability at most
`Q · max(M, 1) · 2^-189`. -/
theorem batch_rom_bits (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hM : M ≤ 2 ^ 64 - 1) (A : OracleComp HashSpec (Unit × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) (hQ : QA + batchQueryBound bytecode M ≤ 2 ^ 64) :
    Pr{let z ← romExperiment A (verifierFam batchSeeds (batchAny M bytecode))}[
      z.1.2 = true ∧ FalseChildren bytecode M z.1.1.2] ≤
      ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) * ((max M 1 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ 189) := by
  refine (batch_rom_explicit hb hM A QA hA).trans ?_
  gcongr
  exact bits_189 (by omega) hQ

end
end LeanVM.Guest.Batch
