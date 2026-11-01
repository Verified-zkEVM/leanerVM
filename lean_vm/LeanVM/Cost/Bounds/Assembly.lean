module

public import LeanVM.Cost.Bounds.Layout
public import LeanVM.Cost.Bounds.TranscriptReplay
public import LeanVM.Cost.Bounds.Sizes.Pruning
import all Statement.LeanIsa
import all Statement.LeanVmVerifier
import all LeanVM.Protocol.Extraction.Fast.AfterRoot
import all LeanVM.Protocol.Extraction.Fast.Extract

/-!
# Bounds: the extractor's price, assembled

`extractorTop prog input qs π` (`Fast/Compiled.lean`) is a chain of two `Option.bind`s:

```
let ((layout, R), state) ← afterRootLite (bytecodeWords prog) π      -- the replay
let (root, height, width) ← state.roots.head?                          -- the stack's root
let idx := transcriptIndex qs (max 64 (8 * width))                      -- the transcript's index
let leaves := subtreeLeavesWith (preimageIn idx) width height root     -- the committed leaves
let word := leafAt leaves height width                                  -- the word's reader
let tabs := runnerTables prog layout                                    -- the runner's tables
let execution := runWithTables tabs prog input layout                  -- a stack's run
(fastStacksFast layout.stackLog R word).findSome? execution <|>
  (decodeStacksDistinct layout.stackLog R word).findSome? execution
```

Its compiled price (`cost_compile extractorC := extractorTop`, withdrawn for now) is, as for
`afterRootLiteC`, three equations: the top's (the bytecode's words, the replay, then
`Option.bind.c323` on the replay's result and a closure `lam0`), `lam0`'s (the roots' head, then
`Option.bind.c323` on it and a closure `lam1 r`), and `lam1`'s (the body). **`extractor_cost`**
takes them as hypotheses (`hTop`, `hLam0`, `hLam1`, as inequalities up to constants `c0`, `c1`,
`c2`), with the closures' runs and prices (the word's reader `wordVal`, `17·w + cW`; a stack's
run `execVal`, `runWithTablesC`'s price and `cE`), the committed leaves' price (`hLeaves`: the
sample's `committedLeaves_cost`, `Bounds/Samples/CommittedLeaves.lean`, re-proved on the chain)
and the decoder's total (`hDec`, a parameter `decoder μ R` until it lands), and bounds the price
on every input by **`extractorBudget`** at the run's shape:

* the replay (`afterRootLite_cost`): `9·|bytecode| + 1004514000`;
* the transcript's index (`transcriptIndex_cost`): `transcriptBound D L N`, `N` queries,
  `N + 2 ≤ 2^D`, `L = max 64 (8·w)`;
* the committed leaves: `leavesBound D h w = 2^h·(2·(40 + D·(18 + 192·(D + 2))) + 617·w + 12060 +
  8·h) + 7` (a lookup's `D` levels of binary searches);
* the runner's tables (`runnerTables_cost`): `tablesBound κ ℓ`;
* the fast path (`fastStacksFast_cost`, the word read by `leafAt`): `fastBound μ R w cW`;
* the runs: at most one fast stack (`fastStacksFast_length_le`) and `2^18` decoded ones
  (`decodeStacksDistinct_length_le_johnson`), each `runBound κ ℓ + cE` (`runWithTables_cost`, the
  step cap `≤ 2^35`) and `9` (`findSome_cost`), on the layouts `afterRootLite` returns
  (`afterRootLite_facts`);
* the decoder: `decoder μ R`.

The tree's shape is the ladder's first level's: height `μ - 6 + R`, width `64`
(`afterRootLite_roots`). At `(μ, R) = (28, 4)`, `κ = ℓ = 32`, at most `2^40` queries
(**`extractorBudget_28_4`**): at most `4085503073093210518239 ≈ 2^71.79` plus the glue and the
decoder (`2^71.77` of it the `2^18 + 1` runs; the transcript's index `≈ 2^65.44`, the fast path
`≈ 2^47.04`, the committed leaves `≈ 2^45.48`, the runner's tables `≈ 2^44.35`, the replay
`≈ 2^39.17`).

The glue `c0`, `c1`, `c2`, the bytecode's words' price `wordsPrice` and the closures' constants
`cE`, `cW` come from the compiled top's equations; the on-demand
names `Option.bind.c323`, `List.findSome?.c125` are this chain's (a re-chain renames them).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

public section

/-! ## Facts of the run -/

theorem bytecodeWords_length (prog : Semantics.Program) :
    (LeanVM.bytecodeWords prog).length = 16 * 2 ^ prog.logSize := by
  simp [LeanVM.bytecodeWords, List.length_flatMap]
  omega

theorem commitPure_roots {height width : ℕ} {s : ProgState} {t : Unit × ProgState}
    (h : commitPure height width s = some t) :
    ∃ root, t.2.roots = s.roots ++ [(root, height, width)] := by
  unfold commitPure at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h.symm
      exact ⟨_, rfl⟩
    · simp at h
  · simp at h

/-- **The stack's root**: `afterRootLite`'s one root, at the ladder's first level: height
`μ - 6 + R`, width `2^6`. -/
theorem afterRootLite_roots {bytecode : List K} {π : Proof} {L : LayoutLite} {R : ℕ}
    {st : ProgState} (h : afterRootLite bytecode π = some ((L, R), st)) :
    ∃ root, st.roots = [(root, L.stackLog - 6 + R, 64)] := by
  unfold afterRootLite at h
  cases hr : readSizesLite bytecode (initialState π) with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr, Option.bind_some] at h
    obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨⟨L', R'⟩, s'⟩ := r
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    obtain ⟨-, -, hroots, -⟩ := readSizesLite_some hr
    unfold commitStackPure at ht
    split at ht
    · rename_i level rest hla
      obtain ⟨hf, hR⟩ := ladder_head hla
      obtain ⟨root, hrt⟩ := commitPure_roots ht
      refine ⟨root, ?_⟩
      rw [hrt, hroots, hf, hR]
      rfl
    · simp at ht

/-- **At most one fast stack**: every lane's pruning step keeps at most as many survivors. -/
theorem fastStacksFast_length_le (μ R : ℕ) (W : ℕ → List K) : (fastStacksFast μ R W).length ≤ 1 := by
  have key : ∀ (f : List (List (Array K) × List ℕ) → ℕ → List (List (Array K) × List ℕ)),
      (∀ st u, (f st u).length ≤ st.length) →
      ∀ (l : List ℕ) (st : List (List (Array K) × List ℕ)), st.length ≤ 1 →
        (l.foldl f st).length ≤ 1 := by
    intro f hf l
    induction l with
    | nil => intro st h; exact h
    | cons u l ih => intro st h; exact ih _ ((hf st u).trans h)
  unfold fastStacksFast
  rw [List.length_map]
  exact key _ (fun st u ↦ pruneStep_single.1) _ _ (by simp)

/-! ## The budget -/

/-- The transcript's index (`transcriptIndex_cost`): `N` queries, `N + 2 ≤ 2^D`, strings of at
most `L` bytes. -/
@[expose] def transcriptBound (D L N : ℕ) : ℕ :=
  (23 * 8 + 31) * D + (replayStepBound (L + 136) D + 13) * N +
    (114 * (L + 136) + 12313) * (N + 1) + 470 +
    (N + 1) * ((23 * L * (D * D) + 60 * (D * D) + 69 * (L * D) + 208 * D + 94) +
      (25 * L + 192 * (D * D) + 595 * D + 161) + D * (17 + (60 + 23 * L) * (D + 2)) + 60) + 50

theorem transcriptBound_mono {D L N N' : ℕ} (h : N ≤ N') :
    transcriptBound D L N ≤ transcriptBound D L N' := by
  unfold transcriptBound
  gcongr

/-- The committed leaves of a tree of height `h`, leaves of `w` words, a lookup's `D` levels of
binary searches (the sample's `committedLeaves_cost`). -/
@[expose] def leavesBound (D h w : ℕ) : ℕ :=
  2 ^ h * (2 * (40 + D * (18 + 192 * (D + 2))) + 617 * w + 12060 + 8 * h) + 7

/-- The runner's tables (`runnerTables_cost`). -/
@[expose] def tablesBound (κ ℓ : ℕ) : ℕ :=
  (70 * κ + 374) * 2 ^ κ + (70 * ℓ + 374) * 2 ^ ℓ + 535 * ℓ + 830

/-- A stack's run (`runWithTables_cost`, the step cap at most `2^35`). -/
@[expose] def runBound (κ ℓ : ℕ) : ℕ := (stepPrice κ ℓ + 45) * 2 ^ 35 + 44 * 2 ^ κ + 1796

/-- The fast path (`fastStacksFast_cost`), a column read at `17·w + cW`, of `w` words. -/
@[expose] def fastBound (μ R w cW : ℕ) : ℕ :=
  64 * ((μ - 6) * (1520 * 2 ^ (μ - 6 + R) + 39583) + 102 * 2 ^ (μ - 6 + R) + 17509) +
    (17 * w + cW + 10 * w + 46) * 2 ^ (μ - 6 + R) + 1016 * 2 ^ μ + 1300

/-- A shape of the extractor's run. -/
structure Shape where
  /-- The stack's log-size. -/
  μ : ℕ
  /-- The rate's log. -/
  R : ℕ
  /-- The memory's log-size `κ`. -/
  logMemory : ℕ
  /-- The program's log-size `ℓ`. -/
  logBytecode : ℕ
  /-- The bytecode's words. -/
  bytecodeLength : ℕ
  /-- The transcript's permutation queries `N`. -/
  queries : ℕ
  /-- `N + 2 ≤ 2^D`. -/
  D : ℕ
  /-- The tree's height. -/
  height : ℕ
  /-- The tree's width (words per leaf). -/
  width : ℕ

/-- **The per-shape budget**: the glue, the replay, the transcript's index, the committed leaves,
the runner's tables, the fast path, at most one fast run, the decoder, at most `2^18` decoded
runs. -/
@[expose] def extractorBudget (glue cE cW decoder : ℕ) (s : Shape) : ℕ :=
  glue + (9 * s.bytecodeLength + 1004514000) + transcriptBound s.D (max 64 (8 * s.width)) s.queries +
    leavesBound s.D s.height s.width + tablesBound s.logMemory s.logBytecode +
    fastBound s.μ s.R s.width cW + ((runBound s.logMemory s.logBytecode + cE + 9) * 1 + 3) +
    decoder + ((runBound s.logMemory s.logBytecode + cE + 9) * 2 ^ 18 + 3)

theorem extractorBudget_def (glue cE cW decoder μ R κ ℓ n N D h w : ℕ) :
    extractorBudget glue cE cW decoder ⟨μ, R, κ, ℓ, n, N, D, h, w⟩ =
      glue + (9 * n + 1004514000) + transcriptBound D (max 64 (8 * w)) N + leavesBound D h w +
        tablesBound κ ℓ + fastBound μ R w cW + ((runBound κ ℓ + cE + 9) * 1 + 3) + decoder +
        ((runBound κ ℓ + cE + 9) * 2 ^ 18 + 3) :=
  rfl

/-- The word the extractor reads, at the root `t = (root, height, width)`. -/
@[expose] def wordOf (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (t : LeanVM.Protocol.Digest × ℕ × ℕ) : ℕ → List K :=
  leafAt (subtreeLeavesWith (preimageIn (transcriptIndex qs (max 64 (8 * t.2.2)))) t.2.2 t.2.1 t.1)
    t.2.1 t.2.2

theorem wordOf_length (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (t : LeanVM.Protocol.Digest × ℕ × ℕ) (v : ℕ) : (wordOf qs t v).length ≤ t.2.2 :=
  leafAt_length_le _ _ _ v fun l hl ↦ (subtreeLeavesWith_mem_length _ _ _ _ l hl).le

/-! ## The assembly -/

/-- **The extractor's price, assembled**, from the compiled top's three price equations
(`hTop`, `hLam0`, `hLam1`: the shape `cost_compile` emits for a chain of two `Option.bind`s, as
for `afterRootLiteC`), the closures' prices, the committed leaves' and the decoder's: at most
`extractorBudget` at the run's shape (the replay alone when it fails). -/
theorem extractor_cost (P : LeanVM.Cost.Program) (prog : Semantics.Program) (input : PublicInput)
    (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (π : Proof)
    (D : ℕ) (hD : D ≤ 61) (hN : qs.length + 2 ≤ 2 ^ D)
    (top : ℕ) {β : Type} [Enc β] (c0 c1 c2 cE cW wordsPrice : ℕ)
    (lam0 : Val) (k0 : (LayoutLite × ℕ) × ProgState → Option β)
    (lam1 : (LayoutLite × ℕ) × ProgState → Val)
    (k1 : (LayoutLite × ℕ) × ProgState → LeanVM.Protocol.Digest × ℕ × ℕ → Option β)
    (wordVal : (LayoutLite × ℕ) × ProgState → LeanVM.Protocol.Digest × ℕ × ℕ → Val)
    (execVal : (LayoutLite × ℕ) × ProgState → Val)
    (leavesCost : (LayoutLite × ℕ) × ProgState → LeanVM.Protocol.Digest × ℕ × ℕ → ℕ)
    (decoder : ℕ → ℕ → ℕ)
    (hA : Includes P afterRootLiteC.costDeps) (hB : Includes P Auto.Option.bind.c323.costDeps)
    (hFS : Includes P Auto.List.findSome?.c125.costDeps) (hT : Includes P transcriptIndexC.costDeps)
    (hRT : Includes P runnerTablesC.costDeps) (hRW : Includes P runWithTablesC.costDeps)
    (hFF : Includes P fastStacksFastC.costDeps)
    -- the top: the bytecode's words, the replay, the first bind
    (hTop : machineCost P top [enc prog, enc input, enc qs, enc π] ≤
      c0 + wordsPrice + machineCost P afterRootLiteC.costIdx [enc (LeanVM.bytecodeWords prog), enc π] +
        machineCost P Auto.Option.bind.c323.costIdx
          [enc (afterRootLite (LeanVM.bytecodeWords prog) π), lam0])
    (hk0 : ∀ r, RunsApp P lam0 [enc r] (enc (k0 r)))
    -- `lam0`: the roots' head, the second bind
    (hLam0 : ∀ r, afterRootLite (LeanVM.bytecodeWords prog) π = some r →
      appCost P lam0 [enc r] ≤ c1 + machineCost P Auto.Option.bind.c323.costIdx
        [enc r.2.roots.head?, lam1 r])
    (hk1 : ∀ r t, RunsApp P (lam1 r) [enc t] (enc (k1 r t)))
    -- `lam1`: the body
    (hLam1 : ∀ r t, afterRootLite (LeanVM.bytecodeWords prog) π = some r → r.2.roots.head? = some t →
      appCost P (lam1 r) [enc t] ≤ c2 +
        machineCost P transcriptIndexC.costIdx [enc qs, enc (max 64 (8 * t.2.2))] +
        leavesCost r t + machineCost P runnerTablesC.costIdx [enc prog, enc r.1.1] +
        machineCost P fastStacksFastC.costIdx [enc r.1.1.stackLog, enc r.1.2, wordVal r t] +
        machineCost P Auto.List.findSome?.c125.costIdx
          [execVal r, enc (fastStacksFast r.1.1.stackLog r.1.2 (wordOf qs t))] +
        machineCost P decodeStacksDistinctC.costIdx [enc r.1.1.stackLog, enc r.1.2, wordVal r t] +
        machineCost P Auto.List.findSome?.c125.costIdx
          [execVal r, enc (decodeStacksDistinct r.1.1.stackLog r.1.2 (wordOf qs t))])
    -- the committed leaves
    (hLeaves : ∀ r t, afterRootLite (LeanVM.bytecodeWords prog) π = some r →
      r.2.roots.head? = some t → leavesCost r t ≤ leavesBound D t.2.1 t.2.2)
    -- the word's reader
    (hW : ∀ r t v, RunsApp P (wordVal r t) [enc v] (enc (wordOf qs t v)))
    (hWc : ∀ r t v, v < 2 ^ 64 → appCost P (wordVal r t) [enc v] ≤ 17 * t.2.2 + cW)
    -- a stack's run
    (hE : ∀ r (q : Vector K (2 ^ r.1.1.stackLog)), RunsApp P (execVal r) [enc q]
      (enc (runWithTables (runnerTables prog r.1.1) prog input r.1.1 q)))
    (hEc : ∀ r (q : Vector K (2 ^ r.1.1.stackLog)), appCost P (execVal r) [enc q] ≤
      machineCost P runWithTablesC.costIdx
        [enc (runnerTables prog r.1.1), enc prog, enc input, enc r.1.1, enc q] + cE)
    -- the decoder, on a word of `64`-word columns read at `17·64 + cW`
    (hDec : ∀ μ R, Whir.Admissible μ R → ∀ (W : ℕ → List K) (WVal : Val),
      (∀ v, RunsApp P WVal [enc v] (enc (W v))) →
      (∀ v, v < 2 ^ 64 → appCost P WVal [enc v] ≤ 17 * 64 + cW) → (∀ v, (W v).length ≤ 64) →
      machineCost P decodeStacksDistinctC.costIdx [enc μ, enc R, WVal] ≤ decoder μ R) :
    machineCost P top [enc prog, enc input, enc qs, enc π] ≤
      match afterRootLite (LeanVM.bytecodeWords prog) π with
      | none => c0 + wordsPrice + (9 * (LeanVM.bytecodeWords prog).length + 1004514000) + 3
      | some ((L, R), _) =>
        extractorBudget (c0 + wordsPrice + c1 + c2 + 10) cE cW (decoder L.stackLog R)
          ⟨L.stackLog, R, L.logMemory, prog.logSize, (LeanVM.bytecodeWords prog).length,
            qs.length, D, L.stackLog - 6 + R, 64⟩ := by
  have hbc := bytecodeWords_length prog
  have hls : prog.logSize ≤ 32 := prog.logSize_le
  have hA' := afterRootLite_cost P hA (LeanVM.bytecodeWords prog) π (by
    rw [hbc]
    have : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hls
    omega)
  rw [Auto.Option.bind.c323.costEq P hB _ k0 lam0 hk0] at hTop
  cases har : afterRootLite (LeanVM.bytecodeWords prog) π with
  | none =>
    rw [har] at hTop
    dsimp only at hTop
    show _ ≤ c0 + wordsPrice + (9 * (LeanVM.bytecodeWords prog).length + 1004514000) + 3
    omega
  | some r =>
    obtain ⟨⟨L, R⟩, st⟩ := r
    rw [har] at hTop
    dsimp only at hTop ⊢
    have h0 := hLam0 _ har
    rw [Auto.Option.bind.c323.costEq P hB _ (k1 _) (lam1 _) (hk1 _)] at h0
    obtain ⟨hf, hμ1, hμ2, hR1, hR2, -⟩ := afterRootLite_facts har
    have hadm := admissible_of_afterRootLite har
    obtain ⟨root, hroots⟩ := afterRootLite_roots har
    have hhead : st.roots.head? = some (root, L.stackLog - 6 + R, 64) := by rw [hroots]; rfl
    dsimp only at h0
    rw [hhead] at h0
    dsimp only at h0
    have h1 := hLam1 _ _ har hhead
    have hl := hLeaves _ _ har hhead
    dsimp only at h1 hl
    rw [show max 64 (8 * 64) = 512 by norm_num] at h1
    -- the transcript's index
    have hTI : machineCost P transcriptIndexC.costIdx [enc qs, enc 512] ≤
        transcriptBound D 512 qs.length := by
      have := transcriptIndex_cost P hT D 512 hD (by norm_num) qs hN
      unfold transcriptBound; omega
    -- the runner's tables
    have hRT' : machineCost P runnerTablesC.costIdx [enc prog, enc L] ≤
        tablesBound L.logMemory prog.logSize :=
      runnerTables_cost P hRT prog L hf.logMemory_le hf.logBytecode_le hf.heights_le
        hf.heights_length
    -- the word
    have hWt := hW ((L, R), st) (root, L.stackLog - 6 + R, 64)
    have hWct := hWc ((L, R), st) (root, L.stackLog - 6 + R, 64)
    have hWl := wordOf_length qs (root, L.stackLog - 6 + R, 64)
    dsimp only at hWct hWl
    -- the fast path
    have hFF' : machineCost P fastStacksFastC.costIdx [enc L.stackLog, enc R,
        wordVal ((L, R), st) (root, L.stackLog - 6 + R, 64)] ≤ fastBound L.stackLog R 64 cW := by
      have := fastStacksFast_cost P hFF L.stackLog R (by omega) (by omega)
        (wordOf qs (root, L.stackLog - 6 + R, 64)) (wordVal ((L, R), st) (root, L.stackLog - 6 + R, 64))
        hWt (17 * 64 + cW) 64 hWct hWl
      unfold fastBound
      simpa only [show Whir.initialFold = 6 from rfl] using this
    -- a stack's run
    have hrun : ∀ q : Vector K (2 ^ L.stackLog), appCost P (execVal ((L, R), st)) [enc q] ≤
        runBound L.logMemory prog.logSize + cE := by
      intro q
      have h1 := hEc ((L, R), st) q
      have h2 := runWithTables_cost P hRW prog input L hf.logMemory_le hf.logBytecode_le
        hf.heights_le hf.heights_length hf.index_lt_word q
      have h3 := stepCapLite_le L hf.logMemory_le hf.logBytecode_le hf.heights_le hf.heights_length
      have h4 := Nat.mul_le_mul_left (stepPrice L.logMemory prog.logSize + 45) h3
      unfold runBound
      dsimp only at h1
      omega
    have hfind : ∀ (qs' : List (Vector K (2 ^ L.stackLog))) (n : ℕ), qs'.length ≤ n →
        machineCost P Auto.List.findSome?.c125.costIdx [execVal ((L, R), st), enc qs'] ≤
          (runBound L.logMemory prog.logSize + cE + 9) * n + 3 := by
      intro qs' n hn
      have := findSome_cost P hFS _ (execVal ((L, R), st)) (hE ((L, R), st))
        (runBound L.logMemory prog.logSize + cE) qs' (fun q _ ↦ hrun q)
      have := Nat.mul_le_mul_left (runBound L.logMemory prog.logSize + cE + 9) hn
      omega
    have hF1 := hfind _ 1 (fastStacksFast_length_le L.stackLog R
      (wordOf qs (root, L.stackLog - 6 + R, 64)))
    have hF2 := hfind _ (2 ^ 18) (decodeStacksDistinct_length_le_johnson hadm
      (wordOf qs (root, L.stackLog - 6 + R, 64)))
    -- the decoder
    have hdec := hDec L.stackLog R hadm _ _ hWt hWct hWl
    refine le_of_le_of_eq ?_ (extractorBudget_def _ _ _ _ _ _ _ _ _ _ _ _ _).symm
    rw [show max 64 (8 * 64) = 512 by norm_num]
    omega

/-! ## The budget at `(28, 4)` -/

/-- **The budget at `(μ, R) = (28, 4)`**, `κ = ℓ = 32` (the bytecode's `2^36` words), at most
`2^40` queries (`D = 41`), the closures' constants at most `100`: at most
`4085503073093210518239 ≈ 2^71.79`, the glue and the decoder aside. -/
theorem extractorBudget_28_4 (glue cE cW decoder N : ℕ) (hN : N ≤ 2 ^ 40) (hE : cE ≤ 100)
    (hW : cW ≤ 100) :
    extractorBudget glue cE cW decoder ⟨28, 4, 32, 32, 16 * 2 ^ 32, N, 41, 26, 64⟩ ≤
      glue + decoder + 4085503073093210518239 := by
  have h1 := transcriptBound_mono (D := 41) (L := 512) hN
  have h2 : transcriptBound 41 512 (2 ^ 40) = 49942440468860842399 := by
    unfold transcriptBound replayStepBound; norm_num
  unfold extractorBudget leavesBound tablesBound fastBound runBound stepPrice
  dsimp only
  rw [show max 64 (8 * 64) = 512 by norm_num]
  norm_num
  omega

theorem extractorBudget_28_4_lt (glue cE cW decoder N : ℕ) (hN : N ≤ 2 ^ 40) (hE : cE ≤ 100)
    (hW : cW ≤ 100) :
    extractorBudget glue cE cW decoder ⟨28, 4, 32, 32, 16 * 2 ^ 32, N, 41, 26, 64⟩ <
      glue + decoder + 2 ^ 72 :=
  lt_of_le_of_lt (extractorBudget_28_4 glue cE cW decoder N hN hE hW) (by norm_num)

end

end LeanVM.Cost.Bounds
