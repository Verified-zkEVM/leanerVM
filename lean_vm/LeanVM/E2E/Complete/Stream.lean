/-
  LeanVM.E2E.Complete.Stream

  What V_I reads of an honest proof: its announced sizes and its stack's root, the first ten
  scalars of the honest stream.
-/

module

public import LeanVM.E2E.Statement
public import LeanVM.Protocol.EndToEnd.Blind.Complete

/-!
# The head of the honest stream

V_I's node step (`nodeStep`) reads only the head of a node's proof: the announced sizes
(`Verifier.announced`, `readSizes` run on the stream) and the stack's root (`stackRoot`, scalars
`8` and `9`). For V°'s honest proof (`Blind.honestStrategyBlind`, compiled by `prove`):

* `readSizes_honest`: `readSizes` is eight reads, then checks that pass on the honest
  announcement `announce s ρ` and return the verifier's layout and the rate;
* `announced_announce`: on a stream starting with `announce s ρ`, `announced` returns
  `(verifierLayout prog s, ρ)`;
* `prove_stream_head`: the honest proof's stream is `announce s ρ`, then the two scalars of the
  root of the committed word `stackWord` at the height `commitStack` announces, then the rest;
* `stackRoot_prove`, `announced_prove`: what V_I reads of it.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.Blake2sHash

@[expose] public section

/-! ## The announcement -/

/-- The honest announcement has `2 + |tables|` scalars. -/
theorem length_announce (s : Sizes) (ρ : ℕ) : (announce s ρ).length = 2 + tables.length := by
  simp [announce, tables]

/-- **`readSizes` on the honest announcement**: eight reads, then checks that pass and return the
verifier's layout and the rate. -/
theorem readSizes_honest (prog : Program) {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) :
    ∃ f, readSizes (bytecodeWords prog) = (Prog.readN (2 + tables.length)).bind f ∧
      f (announce s ρ) = Prog.ret (verifierLayout prog s, ρ) := by
  refine ⟨_, rfl, ?_⟩
  obtain ⟨h1, h2, h3, h5⟩ := hs
  have hlimbs : ((announce s ρ).all fun value ↦ decide (value.limb 1 = 0 ∧ value.limb 2 = 0)) =
      true := by
    simp [announce, eOfNat_limb_one, eOfNat_limb_two]
  have hmem : s.logMem < 2 ^ 64 := by
    have : s.logMem ≤ 32 := h2
    omega
  have hhead : kToNat (((announce s ρ).headD 0).limb 0) = s.logMem := by
    simp only [announce, List.cons_append, List.map_cons, List.headD_cons]
    exact kToNat_eOfNat hmem
  have hlast : kToNat (((announce s ρ).getLastD 0).limb 0) = ρ := by
    simp only [announce, List.map_cons, List.map_append, List.map_nil, List.cons_append]
    rw [List.getLastD_eq_getLast?, List.getLast?_cons, List.getLast?_append]
    simp only [List.getLast?_singleton, Option.some_or, Option.getD_some]
    exact kToNat_eOfNat (by have := hρ.2; omega)
  have htab : (((announce s ρ).drop 1).take tables.length).map (fun value ↦ kToNat (value.limb 0))
      = tableRows s := by
    have ht : tables.length = 6 := rfl
    simp only [announce, ht, List.cons_append, List.map_cons, List.drop_succ_cons, List.drop_zero,
      List.map_append, List.map_nil, tableRows, List.ofFn_succ, List.ofFn_zero]
    simp only [List.nil_append, List.take_succ_cons, List.take_zero,
      List.map_cons, List.map_nil, List.cons.injEq, and_true]
    have hτ : ∀ j, kToNat ((eOfNat (s.rows j)).limb 0) = s.rows j := fun j ↦
      kToNat_eOfNat (lt_of_le_of_lt (h3 j) (by decide))
    exact ⟨hτ 0, hτ 1, hτ 2, hτ 3, hτ 4, hτ 5⟩
  have hok : LayoutOk s := ⟨h1, h2, h3⟩
  have hb := buildLayout_eq prog s
  simp only [hok, ↓reduceIte] at hb
  have hwin : minStackedLog ≤ (verifierLayout prog s).stackLog ∧
      (verifierLayout prog s).stackLog ≤ maxStackedLog := by
    rw [stackLog_verifierLayout]
    exact ⟨le_max_right _ _, h5⟩
  simp only [Prog.require, hlimbs, ↓reduceIte, Prog.ret_bind, hlast, hhead, htab, hb,
    Verifier.liftOption, hwin, and_self, Prog.pure_eq, Prog.bind_eq]
  simp only [show 1 ≤ ρ ∧ ρ ≤ 4 from hρ, and_self, ↓reduceIte, Prog.ret_bind]

/-- Reading `|xs|` scalars of a stream starting with `xs` reads `xs`. -/
theorem run_readN_bind {α : Type} (H : Bytes → Id Digest) :
    ∀ (xs rest : List E) (f : List E → Prog α) (st : St), st.stream = xs ++ rest →
      ∃ cv, Id.run (Compile.run H ((Prog.readN xs.length).bind f) st) =
        Id.run (Compile.run H (f xs) { st with cv := cv, stream := rest })
  | [], rest, f, st, h => ⟨st.cv, by
      simp only [List.nil_append] at h
      simp only [List.length_nil, Prog.readN, Prog.ret_bind]
      rw [← h]⟩
  | x :: xs, rest, f, st, h => by
    have e : (Prog.readN (x :: xs).length).bind f =
        Prog.read fun y ↦ (Prog.readN xs.length).bind fun l ↦ f (y :: l) := by
      simp only [List.length_cons, Prog.readN, Prog.readE, Prog.bind_eq, Prog.bind_assoc]
      rfl
    rw [e]
    simp only [List.cons_append] at h
    obtain ⟨cv, hcv⟩ := run_readN_bind H xs rest (fun l ↦ f (x :: l))
      { st with cv := Id.run (absorbBlock H st.cv (blockOf x 1)), stream := xs ++ rest } rfl
    refine ⟨cv, ?_⟩
    simp only [Compile.run, h]
    exact hcv

/-- **The announced sizes of an honest stream**: on a stream starting with `announce s ρ`,
`announced` returns the verifier's layout at `s` and the rate. -/
theorem announced_announce (prog : Program) {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) (rest : List E) :
    Verifier.announced (bytecodeWords prog) (announce s ρ ++ rest) =
      some (verifierLayout prog s, ρ) := by
  obtain ⟨f, hf, hfa⟩ := readSizes_honest prog hs hρ
  unfold Verifier.announced
  rw [hf, ← length_announce s ρ]
  obtain ⟨cv, hcv⟩ := run_readN_bind (fun _ ↦ pure default) (announce s ρ) rest f
    ⟨default, announce s ρ ++ rest, [], []⟩ rfl
  rw [hcv, hfa]
  rfl

/-! ## The honest proof's head -/

/-- Scripts sequence associatively. -/
theorem script_bind_assoc {α β γ : Type} (p : Script α) (f : α → Script β) (g : β → Script γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [Script.bind, ih]
  | sample k ih => simp only [Script.bind, ih]
  | grind k ih => simp only [Script.bind, ih]
  | commit w k ih => simp only [Script.bind, ih]
  | query k ih => simp only [Script.bind, ih]

/-- Walking the reads of the first `i` scalars of a sent list. -/
theorem walk_sendList_bind {α : Type} (k : Unit → Script α) :
    ∀ (xs : List E) (i : ℕ), i ≤ xs.length →
      ((Script.sendList xs).bind k).walk ((xs.take i).map Ev.read) =
        some ((Script.sendList (xs.drop i)).bind k)
  | _, 0, _ => rfl
  | [], _ + 1, h => absurd h (by simp)
  | x :: xs, i + 1, h => by
    simp only [List.take_succ_cons, List.map_cons, Script.walk, Script.sendList, Script.bind,
      Script.step, Option.bind_some, List.drop_succ_cons]
    exact walk_sendList_bind k xs i (by simpa using h)

/-- The scalar a sent list's script sends after the reads of its first `i` scalars. -/
theorem msgAt_sendList_bind {α : Type} (k : Unit → Script α) (xs : List E) (i : ℕ)
    (hi : i < xs.length) :
    ((Script.sendList xs).bind k).msgAt ((xs.take i).map Ev.read) = xs[i] := by
  rw [Script.msgAt, walk_sendList_bind k xs i hi.le, List.drop_eq_getElem_cons hi]
  rfl

/-- **The honest prover reads out what it sends**: along reads of the scalars it sends, the proof
starts with them. -/
theorem proveFrom_readN_bind (H : Bytes → Digest) (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (xs : List E) (f : List E → Prog α) (cv : Digest) (h : List Ev),
      (∀ i (hi : i < xs.length), S.msg (h ++ (xs.take i).map Ev.read) = xs[i]) →
      ∃ cv', proveFrom H S fuel ((Prog.readN xs.length).bind f) cv h =
        (proveFrom H S fuel (f xs) cv' (h ++ xs.map Ev.read)).map fun t ↦ (xs ++ t.1, t.2)
  | [], f, cv, h, _ => ⟨cv, by
      simp only [List.length_nil, Prog.readN, Prog.ret_bind, List.map_nil, List.append_nil,
        List.nil_append]
      cases proveFrom H S fuel (f []) cv h <;> rfl⟩
  | x :: xs, f, cv, h, hm => by
    have e : (Prog.readN (x :: xs).length).bind f =
        Prog.read fun y ↦ (Prog.readN xs.length).bind fun l ↦ f (y :: l) := by
      simp only [List.length_cons, Prog.readN, Prog.readE, Prog.bind_eq, Prog.bind_assoc]
      rfl
    have h0 : S.msg h = x := by have := hm 0 (by simp); simpa using this
    obtain ⟨cv', hcv⟩ := proveFrom_readN_bind H S fuel xs (fun l ↦ f (x :: l))
      (H (digestBytes cv ++ blockOf x 1)) (h ++ [Ev.read x]) fun i hi ↦ by
        have := hm (i + 1) (by simpa using hi)
        simpa [List.append_assoc] using this
    refine ⟨cv', ?_⟩
    rw [e, proveFrom, h0, hcv, Option.map_map]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
    rfl

/-- The height of the honest stack's commitment: `commitStack`'s at level 0 of the ladder. -/
def stackHeight (μ : ℕ) (level : Whir.Level) : ℕ := (levelShape μ level (2 ^ level.fold)).1

/-- **The head of V°'s honest proof**: the honest announcement, then the two scalars of the root
of the stack's word at the height `commitStack` announces, then the rest. -/
theorem prove_stream_head (H : Bytes → Digest) {prog : Program} {s : Sizes} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} {input : PublicInput} (hs : s.Admissible prog)
    (hρ : validRate ρ) {seed : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (blindProgram (bytecodeWords prog) (publicDigest input))
      (Blind.honestStrategyBlind prog s ρ q) seed fuel = some π) :
    ∃ level rest tail, deriveConfig (leanIsaμ prog s) ρ = some (level :: rest) ∧
      π.stream = announce s ρ ++
        ((digestScalars (treeRoot H (stackHeight (leanIsaμ prog s) level)
            (stackWord (leanIsaμ prog s) q))).1 ::
          (digestScalars (treeRoot H (stackHeight (leanIsaμ prog s) level)
            (stackWord (leanIsaμ prog s) q))).2 :: tail) := by
  obtain ⟨q₀, rest, hc, -⟩ := exists_ladder (whirAdmissible prog hs hρ)
  obtain ⟨f, hf, hfa⟩ := readSizes_honest prog hs hρ
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hπ
  set S := Blind.honestStrategyBlind prog s ρ q
  set W := stackWord (leanIsaμ prog s) q
  -- The script, from its first move.
  obtain ⟨K, hscript⟩ : ∃ K : Unit → Script Unit,
      (Blind.honestRunBlind prog s ρ q >>= fun _ ↦ Script.ret ()) =
        (Script.sendList (announce s ρ)).bind fun _ ↦ (Script.commitS W).bind K := by
    exact ⟨_, by simp only [Blind.honestRunBlind, Script.bind_eq, script_bind_assoc]; rfl⟩
  have hmsg : ∀ i (hi : i < (announce s ρ).length),
      S.msg ([] ++ ((announce s ρ).take i).map Ev.read) = (announce s ρ)[i] := by
    intro i hi
    show (Blind.honestRunBlind prog s ρ q >>= fun _ ↦ Script.ret ()).msgAt
      ((((announce s ρ).take i).map Ev.read).drop 0) = _
    rw [List.drop_zero, hscript]
    exact msgAt_sendList_bind _ _ i hi
  have hword : S.word ([] ++ (announce s ρ).map Ev.read) = W := by
    show (Blind.honestRunBlind prog s ρ q >>= fun _ ↦ Script.ret ()).wordAt
      ((((announce s ρ).map Ev.read)).drop 0) = _
    have hw := walk_sendList_bind (fun _ ↦ (Script.commitS W).bind K) (announce s ρ)
      (announce s ρ).length le_rfl
    rw [List.take_length, List.drop_length] at hw
    rw [List.drop_zero, hscript, Script.wordAt, hw]
    rfl
  -- The program, from its first read.
  obtain ⟨g, k, hP, hk⟩ : ∃ (g : Verifier.Layout × ℕ → Prog Bool) (k : Prog Bool),
      blindProgram (bytecodeWords prog) (publicDigest input) =
        (Prog.readN (announce s ρ).length).bind (fun a ↦ (f a).bind g) ∧
      g (verifierLayout prog s, ρ) =
        Prog.commit (stackHeight (leanIsaμ prog s) ⟨laneBits, ρ, q₀⟩) (2 ^ laneBits) k :=
    ⟨_, _, by
      rw [length_announce]
      simp only [blindProgram, verifyExecutionBlind, Prog.bind_eq, hf, Prog.bind_assoc]
      rfl, by
      simp only [commitStack, stackLog_verifierLayout, hc, Verifier.liftOption, Prog.ret_bind,
        Prog.commitP, Prog.bind_eq]
      rfl⟩
  rw [hP] at ht
  obtain ⟨cv, hcv⟩ := proveFrom_readN_bind H S fuel (announce s ρ) _ seed [] hmsg
  rw [hcv, hfa, Prog.ret_bind, hk] at ht
  simp only [proveFrom, hword] at ht
  rw [Option.map_map] at ht
  obtain ⟨t', -, rfl⟩ := Option.map_eq_some_iff.mp ht
  exact ⟨_, rest, t'.1, hc, rfl⟩

/-- **What V_I reads of V°'s honest proof**: the announced layout and rate are the verifier's at
the honest sizes, the stack's root is the root of the honest stack's word, and the stack's shape
is `commitStack`'s. -/
theorem nodeHead_prove (H : Bytes → Digest) {prog : Program} {s : Sizes} {ρ : ℕ}
    {q : Column (leanIsaμ prog s)} {input : PublicInput} (hs : s.Admissible prog)
    (hρ : validRate ρ) {seed : Digest} {fuel : ℕ} {π : Proof}
    (hπ : prove H (blindProgram (bytecodeWords prog) (publicDigest input))
      (Blind.honestStrategyBlind prog s ρ q) seed fuel = some π) :
    ∃ level rest, deriveConfig (leanIsaμ prog s) ρ = some (level :: rest) ∧
      Verifier.announced (bytecodeWords prog) π.stream = some (verifierLayout prog s, ρ) ∧
      stackRoot π = some (digestScalars (treeRoot H (stackHeight (leanIsaμ prog s) level)
        (stackWord (leanIsaμ prog s) q))) ∧
      stackShape (verifierLayout prog s) ρ = some (levelShape (leanIsaμ prog s) level
        (2 ^ level.fold)) := by
  obtain ⟨level, rest, tail, hc, hst⟩ := prove_stream_head H hs hρ hπ
  refine ⟨level, rest, hc, by rw [hst]; exact announced_announce prog hs hρ _, ?_, ?_⟩
  · have hl := length_announce s ρ
    simp only [stackRoot, hst]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      hl, Nat.sub_self, show 3 + tables.length - (2 + tables.length) = 1 by omega]
    rfl
  · simp only [stackShape, stackLog_verifierLayout, hc]

end
end LeanVM.E2E.Complete
