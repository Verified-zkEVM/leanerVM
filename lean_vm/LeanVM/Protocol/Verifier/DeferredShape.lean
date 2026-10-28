/-
  LeanVM.Protocol.Verifier.DeferredShape

  The claim a deferring verifier accepts is of the verifier's shape: the bytecode's point has the
  bytecode's log-length.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.Verifier.Deferred

/-!
# The shapes of the accepted claims

The claimed evaluator (`claimedValue c`) answers only at the point of `c`, so a run of
the deferring verifier that returns passes through its call at `c`'s point, which is the
verifier's own: the bus's `bytecodeLow ++ alphas`. Its length is fixed by the program
(`verifyDeferred_shaped`).

The run is read through `Prog.Returns` (`returns_of_runProof`: an accepted proof's program may
return `true`), and every phase on the way is walked with `Prog.returns_bind`:

* `readSizes_logBytecode`: the layout's bytecode log-size is `Nat.log2 bytecode.length` less
  `busBits`;
* `busLayout_depth_ge`: the push side's GKR depth is at least the bytecode's log-size, so the
  bus point's `take` keeps all of it.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

@[expose] public section

namespace Prog

variable {α : Type}

/-- A program's successful run returns what the program may return. -/
theorem returns_of_run (H : Bytes → Id Digest) (F : KState → Id KState) {p : Prog α} :
    ∀ {s : St} {a : α} {s' : St}, run H F p s = some (a, s') → Returns p a := by
  induction p with
  | ret b =>
    intro s a s' h
    simp only [run] at h
    cases h
    exact .ret b
  | fail => intro s a s' h; simp [run] at h
  | read k ih =>
    intro s a s' h
    simp only [run] at h
    split at h
    · simp at h
    · next x xs hs => exact .read x (ih x h)
  | sample k ih => intro s a s' h; simp only [run] at h; exact .sample _ (ih _ h)
  | grind bits k ih =>
    intro s a s' h
    simp only [run] at h
    split at h
    · simp at h
    · next n xs hs =>
      change (if _ then _ else _) = _ at h
      split at h
      · exact .grind bits (ih h)
      · simp at h
  | commit height width k ih =>
    intro s a s' h
    simp only [run] at h
    split at h
    · next x0 x1 xs hs =>
      change (match digestOfScalars (x0, x1) with | some root => _ | none => _) = _ at h
      split at h
      · next root hroot => exact .commit height width (ih h)
      · simp at h
    · simp at h
  | query i ps k ih =>
    intro s a s' h
    simp only [run] at h
    split at h
    · simp at h
    · next root height width hr =>
      change (match openAll H root height width ps s.openings with
        | some (rows, rest) => _ | none => _) = _ at h
      split at h
      · next rows rest ho => exact .query i ps rows (ih rows h)
      · simp at h

/-- An accepted proof's program may return `true`. -/
theorem returns_of_runProof (H : Bytes → Id Digest) (F : KState → Id KState) {P : Prog Bool}
    {seed : KState} {π : Proof} (h : runProof H F P seed π = true) : Returns P true := by
  unfold runProof at h
  revert h
  match hr : run H F P ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ with
  | some (true, s) => exact fun _ ↦ returns_of_run H F hr
  | some (false, _) => intro h; simp at h
  | none => intro h; simp at h

/-- `readN n` returns `n` scalars. -/
theorem returns_readN : ∀ {n : ℕ} {xs : List E}, Returns (readN n) xs → xs.length = n
  | 0, xs, h => by rw [returns_ret h]; rfl
  | n + 1, xs, h => by
    unfold readN at h
    obtain ⟨_, -, h⟩ := returns_bind h
    obtain ⟨ys, hys, h⟩ := returns_bind h
    rw [returns_ret h, List.length_cons, returns_readN hys]

/-- `sampleN n` returns `n` challenges. -/
theorem returns_sampleN : ∀ {n : ℕ} {xs : List E}, Returns (sampleN n) xs → xs.length = n
  | 0, xs, h => by rw [returns_ret h]; rfl
  | n + 1, xs, h => by
    unfold sampleN at h
    obtain ⟨_, -, h⟩ := returns_bind h
    obtain ⟨ys, hys, h⟩ := returns_bind h
    rw [returns_ret h, List.length_cons, returns_sampleN hys]

/-- A requirement that may return holds. -/
theorem returns_require {c : Prop} [Decidable c] {u : Unit} (h : Returns (require c) u) : c := by
  unfold require at h
  split at h
  · assumption
  · cases h

end Prog

end
end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A lifted option that may return `a` is `some a`. -/
theorem returns_liftOption {α : Type} {o : Option α} {a : α} (h : Prog.Returns (liftOption o) a) :
    o = some a := by
  unfold liftOption at h
  split at h
  · cases h
  · rw [Prog.returns_ret h]

/-- A sumcheck's point has one challenge per round. -/
theorem returns_sumcheck {count : ℕ} :
    ∀ {eqs : List (Option E)} {claim : E} {x : List E × E},
      Prog.Returns (sumcheck claim count eqs) x → x.1.length = eqs.length
  | [], claim, x, h => by unfold sumcheck at h; rw [Prog.returns_ret h]; rfl
  | e :: es, claim, x, h => by
    unfold sumcheck at h
    obtain ⟨_, -, h⟩ := Prog.returns_bind h
    obtain ⟨_, -, h⟩ := Prog.returns_bind h
    obtain ⟨⟨pt, fin⟩, hp, h⟩ := Prog.returns_bind h
    rw [Prog.returns_ret h, List.length_cons, List.length_cons, ← returns_sumcheck hp]

/-- A GKR step of `step` levels adds `step` coordinates to the point. -/
theorem returns_gkrStep {step : ℕ} {s t : GkrState} (h : Prog.Returns (gkrStep step s) t) :
    t.point.length = step + s.point.length := by
  unfold gkrStep at h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨⟨x, cl⟩, hx, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨y, hy, h⟩ := Prog.returns_bind h
  rw [Prog.returns_ret h, List.length_append, Prog.returns_sampleN hy, returns_sumcheck hx,
    List.length_map]

/-- The GKR walk over `n` levels adds `n` coordinates to the point. -/
theorem returns_gkrLayers :
    ∀ (n : ℕ) {s t : GkrState}, Prog.Returns (gkrLayers n s) t →
      t.point.length = n + s.point.length
  | 0, s, t, h => by unfold gkrLayers at h; rw [Prog.returns_ret h, zero_add]
  | 1, s, t, h => by
    unfold gkrLayers at h
    obtain ⟨s1, h1, h⟩ := Prog.returns_bind h
    rw [returns_gkrLayers 0 h, returns_gkrStep h1]
    omega
  | n + 2, s, t, h => by
    unfold gkrLayers at h
    split at h
    · obtain ⟨s1, h1, h⟩ := Prog.returns_bind h
      rw [returns_gkrLayers (n + 1) h, returns_gkrStep h1]
      omega
    · obtain ⟨s1, h1, h⟩ := Prog.returns_bind h
      rw [returns_gkrLayers n h, returns_gkrStep h1]
      omega

/-- The GKR point has the depth's length. -/
theorem returns_verifyGkrGrandProducts {depth : ℕ} {x : E × List E × List E}
    (h : Prog.Returns (verifyGkrGrandProducts depth) x) : x.2.1.length = depth := by
  unfold verifyGkrGrandProducts at h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨t, ht, h⟩ := Prog.returns_bind h
  rw [Prog.returns_ret h]
  exact (returns_gkrLayers depth ht).trans (add_zero _)

/-- The claimed bytecode value is given only at the claimed point. -/
theorem returns_claimed_bytecode {c : FixedClaims} {words : List K} {point : List E} {v : E}
    (h : Prog.Returns (claimedValue c words point) v) :
    point = c.bytecodePoint := by
  obtain ⟨_, h, -⟩ := Prog.returns_bind h
  exact Prog.returns_require h

/-- `log2Strict` gives `Nat.log2`. -/
theorem log2Strict_eq {n k : ℕ} (h : log2Strict n = some k) : k = Nat.log2 n := by
  unfold log2Strict at h
  split at h
  · next hn =>
    simp only [Option.some.injEq] at h
    rw [← h]
    unfold bitLength
    split <;> omega
  · cases h

/-- `log2Ceil N` is at least `k` once `2 ^ k ≤ N`. -/
theorem le_log2Ceil_of_two_pow_le {k N : ℕ} (h : 2 ^ k ≤ N) : k ≤ log2Ceil N := by
  rcases k with _ | k
  · exact Nat.zero_le _
  · have hk : 2 ^ k ≤ N - 1 := by rw [pow_succ] at h; have := Nat.one_le_two_pow (n := k); omega
    have hN : N - 1 ≠ 0 := by have := Nat.one_le_two_pow (n := k); omega
    unfold log2Ceil bitLength
    simp only [hN, ↓reduceIte]
    exact Nat.succ_le_succ ((Nat.le_log2 hN).mpr hk)

/-- The second component of `stack_offsets`' placing fold sums the block sizes. -/
theorem foldl_place_snd (w : ℕ → ℕ) :
    ∀ (l : List ℕ) (acc : List ℕ × ℕ),
      (l.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + w i)) acc).2 =
        acc.2 + (l.map w).sum
  | [], acc => by simp
  | i :: l, acc => by
    rw [List.foldl_cons, foldl_place_snd w l, List.map_cons, List.sum_cons]
    simp only
    omega

/-- The push side's GKR depth is at least the bytecode's log-size. -/
theorem busLayout_depth_ge (logMemory logBytecode : ℕ) (blocks : List BusBlock) :
    logBytecode ≤ (busLayout [0, logMemory, logBytecode] blocks).depth := by
  show logBytecode ≤ (stackOffsets ([0, logMemory, logBytecode] ++ blocks.map (·.logRows))).2
  unfold stackOffsets
  simp only
  rw [foldl_place_snd, zero_add]
  apply le_log2Ceil_of_two_pow_le
  refine List.le_sum_of_mem (List.mem_map.mpr ⟨2, ?_, rfl⟩)
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_range]
  simp

/-- The layout `readSizes` returns has the bytecode's log-size, in tuples of `2 ^ busBits`. -/
theorem readSizes_logBytecode {bytecode : List K} {x : Layout × ℕ}
    (h : Prog.Returns (readSizes bytecode) x) :
    x.1.logBytecode + busBits = Nat.log2 bytecode.length := by
  unfold readSizes at h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨layout, hl, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  rw [Prog.returns_ret h]
  have ho := returns_liftOption hl
  unfold buildLayout at ho
  split at ho
  · simp at ho
  · next logLength hlog =>
    split at ho
    · next hc =>
      simp only [Option.some.injEq] at ho
      rw [← ho, ← log2Strict_eq hlog]
      show logLength - busBits + busBits = logLength
      omega
    · simp at ho

/-- The bus asks for the bytecode at a point of length `logBytecode + busBits`. -/
theorem verifyBusBalance_bytecodePoint {c : FixedClaims} {layout : Layout} {b : BusResult}
    (h : Prog.Returns (verifyBusBalance (claimedValue c) layout) b) :
    c.bytecodePoint.length = layout.logBytecode + busBits := by
  unfold verifyBusBalance at h
  obtain ⟨alphas, ha, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨⟨cr, point, tv⟩, hg, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, hv, -⟩ := Prog.returns_bind h
  have hd := busLayout_depth_ge layout.logMemory layout.logBytecode layout.push
  have hp : point.length = _ := returns_verifyGkrGrandProducts hg
  rw [← returns_claimed_bytecode hv, List.length_append, List.length_take, Prog.returns_sampleN ha,
    hp]
  omega

/-- **The verifier's claims, of the verifier's shapes**: a run of the verifier on the claimed
evaluator that may return makes claims of the lengths the program fixes. -/
theorem verifyExecution_shaped {c : FixedClaims} {bytecode : List K} {publicInput : Digest}
    {u : Unit} (h : Prog.Returns (verifyExecutionClaims (claimedValue c) bytecode publicInput) u) :
    c.bytecodePoint.length = Nat.log2 bytecode.length := by
  unfold verifyExecutionClaims at h
  obtain ⟨⟨layout, r⟩, hl, h⟩ := Prog.returns_bind h
  obtain ⟨_, -, h⟩ := Prog.returns_bind h
  obtain ⟨_, hb, -⟩ := Prog.returns_bind h
  rw [verifyBusBalance_bytecodePoint hb]
  exact readSizes_logBytecode hl

/-- **An accepted proof's claims are of the verifier's shapes**: a proof the deferring verifier
accepts claims the bytecode at a point of the bytecode's log-length. -/
theorem verifyDeferred_shaped {bytecode : List K} {iv publicInput : Digest} {c : FixedClaims}
    {π : Proof} (h : verifyDeferred bytecode iv publicInput c π = true) :
    c.bytecodePoint.length = Nat.log2 bytecode.length := by
  have hP := Prog.returns_of_runProof keccak256 keccakF h
  rw [deferredProgram_eq] at hP
  obtain ⟨_, hu, -⟩ := Prog.returns_bind hP
  exact verifyExecution_shaped hu

end
end LeanVM.Protocol.Verifier
