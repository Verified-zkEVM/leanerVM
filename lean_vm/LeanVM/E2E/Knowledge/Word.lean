/-
  LeanVM.E2E.Knowledge.Word

  The word V_I checks at a node is the word V°'s extractor reads: the sizes and the stack's root
  of a proof are the ones its accepted run announces and commits, and a word whose Merkle tree
  the log answers is the word the log's answers extract under its root.
-/

module

public import LeanVM.E2E.Statement
public import LeanVM.Protocol.EndToEnd.Blind.Execution
public import LeanVM.Protocol.EndToEnd.Sound.Runs

/-!
# V_I's word is the extracted word

T1 (`blind_knowledge_cache'`) gives, for a proof V° accepts with every hash answered by a log
without failure, a stack satisfying the leanISA relation without Flock among the candidates of
the word the extractor reads off the log under the stack's root (`ExtractedBlind`). V_I
(`nodeStep`) enumerates the candidates of the word the idealized proof gives the node, checked to
have that root. This module shows the two are the same candidates.

* **Runs, split** (`xrun_bind`): the extracted run of a sequence is the run of its first program,
  then of the continuation.
* **Reading programs** (`ReadsN`): a program that only reads `n` scalars (and checks them) consumes
  the first `n` scalars of the stream, records them, and returns what its run returns under every
  hash (`xrun_of_readsN`); `readSizes` is one (`readsN_readSizes`), so V°'s announced sizes are
  `Verifier.announced`'s (`announced_eq_of_xrun`).
* **The stack's root** (`xrun_commitStack`): the commitment after the sizes reads the two scalars
  `stackRoot` names, and records the word extracted under the root they encode.
* **Merkle trees** (`openOne_of_rootOfLevelM`): every leaf of a tree whose root the log answers
  has an opening the log accepts, so the word extracted under that root is the word, at every
  position of the tree (`extract_eq_of_treeRootM`).
* `candidates_congr`: the candidates of a word read only its columns.
* **The node** (`mem_blindCandidates_of_extractedBlind`): at a node V_I accepts, T1's extracted
  stack is one of the candidates V_I enumerates.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.EndToEnd.Blind LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom

@[expose] public section

/-! ## Extracted runs of sequences -/

section XRun

variable (H : Bytes → Option Digest)

/-- **The extracted run of a sequence** is the run of the first program, then of the
continuation from where it ended. -/
theorem xrun_bind {α β : Type} (f : α → Prog β) :
    ∀ (p : Prog α) (s : St) (h : List Ev),
      xrun H (p.bind f) s h = (xrun H p s h).bind fun r ↦ xrun H (f r.1) r.2.1 r.2.2
  | .ret a, s, h => rfl
  | .fail, s, h => rfl
  | .read k, s, h => by
    simp only [Prog.bind, xrun]
    split
    · rfl
    · rw [Option.bind_assoc]
      congr 1
      funext cv
      exact xrun_bind f (k _) _ _
  | .sample k, s, h => by
    simp only [Prog.bind, xrun]
    rw [Option.bind_assoc]
    congr 1
    funext cv
    exact xrun_bind f (k _) _ _
  | .grind bits k, s, h => by
    simp only [Prog.bind, xrun]
    split
    · rfl
    · simp only [Option.bind_assoc]
      congr 1; funext base; congr 1; funext d; congr 1; funext cv
      split
      · exact xrun_bind f k _ _
      · rfl
  | .commit height width k, s, h => by
    simp only [Prog.bind, xrun]
    split
    · simp only [Option.bind_assoc]
      congr 1; funext cv0; congr 1; funext cv1
      split
      · exact xrun_bind f k _ _
      · rfl
    · rfl
  | .query i ps k, s, h => by
    simp only [Prog.bind, xrun]
    split
    · rfl
    · split
      · exact xrun_bind f (k _) _ _
      · rfl

/-- `xrun_bind` with the monad's bind. -/
theorem xrun_bind' {α β : Type} (p : Prog α) (f : α → Prog β) (s : St) (h : List Ev) :
    xrun H (p >>= f) s h = (xrun H p s h).bind fun r ↦ xrun H (f r.1) r.2.1 r.2.2 :=
  xrun_bind H f p s h

end XRun

/-! ## Programs that only read -/

/-- **`p` reads `n` scalars and does nothing else**: no challenge, proof of work, commitment or
opening; it may reject. -/
inductive ReadsN {α : Type} : ℕ → Prog α → Prop
  /-- A return reads nothing. -/
  | ret (a : α) : ReadsN 0 (.ret a)
  /-- A rejection reads as much as asked. -/
  | fail (n : ℕ) : ReadsN n .fail
  /-- A read, then `n` more. -/
  | read {n : ℕ} {k : E → Prog α} : (∀ x, ReadsN n (k x)) → ReadsN (n + 1) (.read k)

/-- Reading programs in sequence read the sum. -/
theorem ReadsN.bind {α β : Type} {n m k : ℕ} {p : Prog α} {f : α → Prog β} (hp : ReadsN n p)
    (hf : ∀ a, ReadsN m (f a)) (hk : k = n + m) : ReadsN k (p >>= f) := by
  induction hp generalizing k with
  | ret a => rw [Nat.zero_add] at hk; subst hk; exact hf a
  | fail n => exact ReadsN.fail k
  | @read n k' _ ih =>
    obtain rfl : k = (n + m) + 1 := by omega
    exact ReadsN.read fun x ↦ ih x rfl

/-- A check reads nothing. -/
theorem readsN_require (c : Prop) [Decidable c] : ReadsN 0 (Prog.require c) := by
  unfold Prog.require
  split
  · exact ReadsN.ret ()
  · exact ReadsN.fail 0

/-- An optional value reads nothing. -/
theorem readsN_liftOption {α : Type} (o : Option α) : ReadsN 0 (liftOption o) := by
  cases o
  · exact ReadsN.fail 0
  · exact ReadsN.ret _

/-- `readN n` reads `n` scalars. -/
theorem readsN_readN : ∀ n, ReadsN n (Prog.readN n)
  | 0 => ReadsN.ret []
  | n + 1 => ReadsN.bind (n := 1) (m := n) (ReadsN.read fun x ↦ ReadsN.ret x)
      (fun x ↦ ReadsN.bind (n := n) (m := 0) (readsN_readN n) (fun xs ↦ ReadsN.ret (x :: xs))
        rfl) (by omega)

/-- **The announced sizes are read**: `readSizes` reads the `2 + |tables|` scalars. -/
theorem readsN_readSizes (bytecode : List K) : ReadsN (2 + tables.length) (readSizes bytecode) := by
  unfold readSizes
  refine ReadsN.bind (m := 0) (readsN_readN _) (fun xs ↦ ?_) rfl
  refine ReadsN.bind (m := 0) (readsN_require _) (fun _ ↦ ?_) rfl
  refine ReadsN.bind (m := 0) (readsN_require _) (fun _ ↦ ?_) rfl
  refine ReadsN.bind (m := 0) (readsN_liftOption _) (fun _ ↦ ?_) rfl
  exact ReadsN.bind (m := 0) (readsN_require _) (fun _ ↦ ReadsN.ret _) rfl

section XRun

variable (H : Bytes → Option Digest)

/-- **The extracted run of a reading program** consumes the first `n` scalars of the stream,
records them, keeps the roots, and returns what the program's run returns under every hash. -/
theorem xrun_of_readsN {α : Type} {n : ℕ} {p : Prog α} (hp : ReadsN n p) :
    ∀ {s : St} {h : List Ev} {a : α} {s' : St} {h' : List Ev},
      xrun H p s h = some (a, s', h') →
        ∃ xs : List E, xs.length = n ∧ s.stream = xs ++ s'.stream ∧ s'.roots = s.roots ∧
          h' = h ++ xs.map Ev.read ∧
          ∀ (H' : Bytes → Id Digest) (cv : Digest) (os : List Opening)
            (roots : List (Digest × ℕ × ℕ)),
            (Id.run (run H' p ⟨cv, s.stream, os, roots⟩)).map (·.1) = some a := by
  induction hp with
  | ret a =>
    intro s h a' s' h' hx
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨[], rfl, by simp, rfl, by simp, fun _ _ _ _ ↦ rfl⟩
  | fail n =>
    intro s h a' s' h' hx
    simp [xrun] at hx
  | @read n k _ ih =>
    intro s h a s' h' hx
    obtain ⟨cv, stream, os, roots⟩ := s
    simp only [xrun] at hx
    cases stream with
    | nil => simp at hx
    | cons x xs =>
      simp only [Option.bind_eq_some_iff] at hx
      obtain ⟨cv', -, hx⟩ := hx
      obtain ⟨ys, hl, hs, hr, hh, hrun⟩ := ih x hx
      refine ⟨x :: ys, by simp [hl], by simpa using hs, hr, by simp [hh], ?_⟩
      intro H' cv'' os' roots'
      exact hrun H' _ os' roots'

end XRun

/-! ## Merkle trees answered by a log -/

section Merkle

/-- An `Option` traversal that succeeds relates every input to its output. -/
theorem forall₂_of_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b ↦ f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (forall₂_of_mapM_some hbs)

/-- An `Option` traversal of `0, …, n - 1` that succeeds has `n` outputs, the `j`-th `f j`'s. -/
theorem mapM_range_some {β : Type} {f : ℕ → Option β} {n : ℕ} {l : List β}
    (h : (List.range n).mapM f = some l) :
    ∃ hl : l.length = n, ∀ (j : ℕ) (hj : j < n), f j = some (l[j]'(hl ▸ hj)) := by
  have h2 := forall₂_of_mapM_some h
  have hl : l.length = n := by rw [← h2.length_eq, List.length_range]
  refine ⟨hl, fun j hj ↦ ?_⟩
  have := List.forall₂_iff_get.mp h2
  have h3 := this.2 j (by simpa using hj) (by omega)
  simpa using h3

variable {H : Bytes → Option Digest}

/-- **Every node of a level whose root is answered climbs to the root**, through answered
parents. -/
theorem climb_of_rootOfLevelM :
    ∀ (k : ℕ) (level : List Digest) (root : Digest), level.length = 2 ^ k →
      rootOfLevelM H k level = some root → ∀ i < 2 ^ k,
        ∃ path : List Digest, path.length = k ∧
          climb (m := Option) H (level.getD i default) i path = some root
  | 0, level, root, _, h, i, hi => by
    obtain rfl : i = 0 := by omega
    simp only [rootOfLevelM, pure, Option.some.injEq] at h
    exact ⟨[], rfl, by rw [h]; rfl⟩
  | k + 1, level, root, hlen, h, i, hi => by
    simp only [rootOfLevelM, bind, Option.bind_eq_some_iff] at h
    obtain ⟨up, hup, h⟩ := h
    obtain ⟨hul, hu⟩ := mapM_range_some hup
    have hi2 : i / 2 < 2 ^ k := by rw [Nat.pow_succ] at hi; omega
    obtain ⟨path, hpl, hpath⟩ := climb_of_rootOfLevelM k up root hul h (i / 2) hi2
    have hpar := hu (i / 2) hi2
    rw [← List.getD_eq_getElem (d := default)] at hpar
    refine ⟨level.getD (if i % 2 = 0 then i + 1 else i - 1) default :: path, by simp [hpl], ?_⟩
    rw [climb_cons, Option.bind_eq_some_iff]
    refine ⟨up.getD (i / 2) default, ?_, hpath⟩
    rw [← hpar]
    unfold nodeInput
    split
    · rename_i he
      rw [show 2 * (i / 2) = i by omega]
    · rename_i he
      rw [show 2 * (i / 2) = i - 1 by omega, show i - 1 + 1 = i by omega]

/-- **Every leaf of a tree whose root the log answers has an opening the log accepts.** -/
theorem openOne_of_treeRootM {ht w : ℕ} {W : Word} {root : Digest} (hws : WellShaped w W)
    (h : treeRootM H ht W = some root) {p : ℕ} (hp : p < 2 ^ ht) :
    ∃ path : List Digest, openOne (m := Option) H root ht w p ⟨W p, path⟩ = some true := by
  simp only [treeRootM, bind, Option.bind_eq_some_iff] at h
  obtain ⟨leaves, hleaves, h⟩ := h
  obtain ⟨hll, hl⟩ := mapM_range_some hleaves
  obtain ⟨path, hpl, hpath⟩ := climb_of_rootOfLevelM ht leaves root hll h p hp
  refine ⟨path, (openOne_eq_some_true_iff _ _ _ _ _ _).mpr ⟨hws p, hpl, _, ?_, hpath⟩⟩
  rw [hl p hp, List.getD_eq_getElem]

/-- **The word a log extracts under a tree's root is the tree's word**, at every position of
the tree, when the log's answers have no collision. -/
theorem extract_eq_of_treeRootM (hH : AnswersInj H) {ht w : ℕ} {W : Word} {root : Digest}
    (hws : WellShaped w W) (h : treeRootM H ht W = some root) {p : ℕ} (hp : p < 2 ^ ht) :
    Rom.extract H root ht w p = W p := by
  obtain ⟨path, ho⟩ := openOne_of_treeRootM hws h hp
  have := extract_eq_of_openOne hH ho
  rwa [Nat.mod_eq_of_lt hp] at this

end Merkle

/-! ## The stack's commitment -/

section Commit

variable (H : Bytes → Option Digest)

/-- **The stack's commitment, extracted**: it reads the next two scalars, which encode a root,
and records the word extracted under it, of level 0's shape. -/
theorem xrun_commitStack {logN ρ : ℕ} {level : Whir.Level} {rest : List Whir.Level}
    (hc : deriveConfig logN ρ = some (level :: rest)) {s : St} {h : List Ev} {u : Unit}
    {s' : St} {h' : List Ev} (hx : xrun H (commitStack logN ρ) s h = some (u, s', h')) :
    ∃ (x0 x1 : E) (xs : List E) (root : Digest), s.stream = x0 :: x1 :: xs ∧
      digestOfScalars (x0, x1) = some root ∧
      h' = h ++ [Ev.commit (levelShape logN level (2 ^ level.fold)).1
        (levelShape logN level (2 ^ level.fold)).2
        (Rom.extract H root (levelShape logN level (2 ^ level.fold)).1
          (levelShape logN level (2 ^ level.fold)).2)] := by
  have e : commitStack logN ρ = Prog.commitP (levelShape logN level (2 ^ level.fold)).1
      (levelShape logN level (2 ^ level.fold)).2 := by
    simp only [commitStack, hc, Verifier.liftOption]
    rfl
  rw [e] at hx
  obtain ⟨cv, stream, os, roots⟩ := s
  match stream, hx with
  | [], hx => simp [Prog.commitP, xrun] at hx
  | [_], hx => simp [Prog.commitP, xrun] at hx
  | x0 :: x1 :: xs, hx =>
    simp only [Prog.commitP, xrun, Option.bind_eq_some_iff] at hx
    obtain ⟨cv0, -, cv1, -, hx⟩ := hx
    split at hx
    · rename_i root hroot
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      exact ⟨x0, x1, xs, root, rfl, hroot, hx.2.2.symm⟩
    · simp at hx

end Commit

/-! ## The public input of a digest -/

/-- The field element of two words. -/
theorem ofBits_words (lo hi : UInt32) :
    K.ofBits (lo.toNat + 2 ^ 32 * hi.toNat) = ofWords lo hi := by
  have h := toNat_lowWord_add_highWord (ofWords lo hi)
  rw [lowWord_ofWords, highWord_ofWords] at h
  rw [h, K.ofBits, BitVec.ofNat_toNat, BitVec.setWidth_eq, BF64.ofBitVec_toBitVec]

/-- **The public input of a digest has that digest** (`publicDigest`'s inverse). -/
theorem publicDigest_inputOf (d : Digest) : publicDigest (inputOf d) = d := by
  have e : inputOf d = Guest.End.publicInputOf d := by
    simp only [inputOf, Guest.End.publicInputOf, publicInputOfDigest]
    congr 1
    funext i
    fin_cases i <;> simpa using ofBits_words _ _
  rw [e, Guest.End.publicDigest_publicInputOf]

/-! ## Candidates read only the columns -/

/-- **The candidates of a word read only its columns**: two words equal on the columns of a
level-0 commitment have the same candidates. -/
theorem candidates_congr {μ R A : ℕ} {W W' : Word}
    (h : ∀ v < 2 ^ (μ - laneBits + R), W v = W' v) {q : Column μ}
    (hq : q ∈ Candidates μ R A W) : q ∈ Candidates μ R A W' := by
  obtain ⟨S, hS, hag⟩ := hq
  refine ⟨S, hS, fun v hv u ↦ ?_⟩
  rw [← hag v hv u]
  simp only [laneOf, h v v.isLt]

/-! ## The node -/

/-- The cache of a log reads as the log. -/
theorem cacheOf_eq_look (ℓ : Log) : (fun x ↦ cacheOf ℓ x) = look ℓ :=
  funext fun x ↦ cacheOf_apply ℓ x

/-- **At a node V_I accepts, T1's extracted stack is among V_I's candidates.** On a log without
failure, for a proof V° accepts with every hash answered by the log, at the sizes `s`, rate `ρ`
and stack root `r` V_I reads off the proof, and a word `W` of the stack's shape whose tree the
log answers with the root `r` encodes: the sizes are admissible, and if the extractor reading
the log succeeds (`ExtractedBlind`, T1's conclusion), some candidate of `W` satisfies the
leanISA relation without Flock (`blindCandidates`). -/
theorem mem_blindCandidates_of_extractedBlind {ℓ : Log} (hf : ¬ Fail leanVmSeeds ℓ)
    {prog : Program} {pi : Digest} {π : Proof}
    (hv : verifyBlindWith (look ℓ) (bytecodeWords prog) pi π = some true)
    {layout : Verifier.Layout} {ρ : ℕ} {s : Sizes} {r : E × E} {ht w : ℕ} {W : Word}
    {root : Digest}
    (hann : Verifier.announced (bytecodeWords prog) π.stream = some (layout, ρ))
    (hs : sizesOf prog layout = some s) (hr : stackRoot π = some r)
    (hsh : stackShape layout ρ = some (ht, w)) (hws : WellShaped w W)
    (hroot : treeRootM (look ℓ) ht W = some root) (hrr : digestScalars root = r)
    (hx : ExtractedBlind prog (inputOf pi) (cacheOf ℓ) π) :
    s.Admissible prog ∧ ∃ q, q ∈ blindCandidates prog s ρ pi W := by
  -- The sizes V_I chose.
  have hsz : verifierLayout prog s = layout ∧ s.Admissible prog := by
    unfold sizesOf at hs
    split at hs
    · rename_i hex
      obtain rfl := Option.some.inj hs
      exact hex.choose_spec
    · simp at hs
  -- V°'s run, extracted.
  have hv' : Rom.verify (look ℓ) (leanVmSeed (bytecodeWords prog) pi)
      (blindProgram (bytecodeWords prog) pi) π = some true := by
    rw [← hv]
    simp only [Rom.verify, verifyBlindWith, seedRun_leanVmSeed]
  obtain ⟨seed, st, -, hxr⟩ := xrun_of_verify hv'
  generalize hH : extractedHistory (look ℓ) (leanVmSeed (bytecodeWords prog) pi)
    (blindProgram (bytecodeWords prog) pi) π = hist
    at hxr
  rw [show blindProgram (bytecodeWords prog) pi =
      verifyExecutionBlind (bytecodeWords prog) pi >>= fun _ ↦ pure true from rfl,
    xrun_bind', Option.bind_eq_some_iff] at hxr
  obtain ⟨⟨u, s₂, h₂⟩, hve, hret⟩ := hxr
  simp only [pure, xrun, Option.some.injEq, Prod.mk.injEq] at hret
  obtain ⟨-, -, hhist⟩ := hret
  rw [verifyExecutionBlind_eq, ← show ∀ (p : Prog (Verifier.Layout × ℕ)) (f : _ → Prog Unit),
    p >>= f = p.bind f from fun _ _ ↦ rfl, xrun_bind', Option.bind_eq_some_iff] at hve
  obtain ⟨⟨a, s₁, h₁⟩, hrs, hbody⟩ := hve
  rw [show veBodyBlind pi a.1 a.2 = commitStack a.1.stackLog a.2 >>= fun _ ↦ _ from rfl,
    xrun_bind', Option.bind_eq_some_iff] at hbody
  obtain ⟨⟨u', s₃, h₃⟩, hcs, hrest⟩ := hbody
  -- The sizes, read.
  obtain ⟨xs, hxl, hstream, -, hh₁, hrun⟩ :=
    xrun_of_readsN (look ℓ) (readsN_readSizes (bytecodeWords prog)) hrs
  have ha : a = (layout, ρ) := by
    have h1 : Verifier.announced (bytecodeWords prog) π.stream = some a :=
      hrun (fun _ ↦ pure default) default [] []
    rw [hann] at h1
    exact (Option.some.inj h1).symm
  subst ha
  simp only [List.nil_append] at hh₁
  -- The stack's root, committed.
  unfold stackShape at hsh
  split at hsh
  · rename_i level rest hc
    obtain ⟨rfl⟩ := hsh
    obtain ⟨x0, x1, xs', root', hs₁, hroot', hh₃⟩ := xrun_commitStack (look ℓ) hc hcs
    simp only at hstream
    rw [hs₁] at hstream
    have hr' : r = (x0, x1) := by
      have h2 : (xs ++ x0 :: x1 :: xs')[2 + tables.length]? = some x0 := by
        rw [List.getElem?_append_right (by omega)]; simp [hxl]
      have h3 : (xs ++ x0 :: x1 :: xs')[3 + tables.length]? = some x1 := by
        rw [List.getElem?_append_right (by omega)]
        rw [show 3 + tables.length - xs.length = 1 by omega]; rfl
      unfold stackRoot at hr
      rw [hstream, h2, h3] at hr
      simpa [bind, pure] using hr.symm
    subst hr'
    rw [← hrr, digestOfScalars_digestScalars, Option.some.injEq] at hroot'
    subst hroot'
    -- The history.
    have hpre₃ : h₃ <+: h₂ := xrun_prefix (look ℓ) _ _ _ hrest
    obtain ⟨l₁, hl₁e, hl₁, -⟩ := xrun_after (look ℓ) _ _ _ hrs
    simp only [List.nil_append] at hl₁e
    subst hl₁e
    have hann' : announced prog hist = some (s, ρ) := by
      rw [← hhist]
      exact announced_eq prog ((List.prefix_append _ _).trans (hh₃ ▸ hpre₃)) hl₁ hsz.1.symm
    have hfw : firstWord hist =
        some (Rom.extract (look ℓ) root (levelShape layout.stackLog level (2 ^ level.fold)).1
          (levelShape layout.stackLog level (2 ^ level.fold)).2) := by
      rw [← hhist]
      obtain ⟨l₂, rfl⟩ := hpre₃
      rw [hh₃, hh₁]
      refine firstWord_append ?_ l₂
      rw [firstWord, commits_reads_commit]
      rfl
    -- The extractor's candidate.
    obtain ⟨s', q, hex, -, -⟩ := hx
    unfold extractStackBlind at hex
    rw [publicDigest_inputOf, cacheOf_eq_look, hH] at hex
    dsimp only at hex
    rw [hann', hfw] at hex
    dsimp only at hex
    split at hex
    · rename_i hq
      refine ⟨hsz.2, hq.choose, ?_, hq.choose_spec.2⟩
      -- The shape of level 0.
      obtain ⟨g, -, -, hwa, -⟩ := good_of_readSizes prog hl₁
      obtain ⟨q₀, rest', hc', -⟩ := Whir.Complete.exists_ladder hwa
      rw [hc] at hc'
      simp only [Option.some.injEq, List.cons.injEq] at hc'
      obtain ⟨rfl, rfl⟩ := hc'
      refine candidates_congr (fun v hv ↦ ?_) hq.choose_spec.1
      refine extract_eq_of_treeRootM (answersInj_look hf) hws hroot ?_
      simpa [levelShape, ← hsz.1, stackLog_verifierLayout] using hv
    · simp at hex
  · simp at hsh

end
end LeanVM.E2E
