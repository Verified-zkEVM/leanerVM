/-
  LeanVM.E2E.Batch.Prog

  The bytecode part of the batching as a verifier program, for every child count: its doom
  specification after children whose claims on the bytecode leave a nonzero gap, and its
  certificate.
-/

module

public import LeanVM.Guest.Batch.Rom
public import LeanVM.E2E.Statement
public import LeanVM.Protocol.EndToEnd.Blind.Deferred

/-!
# The bytecode part of the batching, as a program

`Node.batch` batches the children's claims on the two fixed polynomials with separate lambdas
and separate sumchecks: the bytecode's (`lambdasB`, the first sumcheck) and the matrices' (the
later lambdas, the second sumcheck). The bytecode's side is sound on its own: its doom
(`Guest.Batch.restSpecB`) tracks only the bytecode's gaps, the lambdas `lB` and the first
sumcheck, and only the bytecode's final check contradicts it. So the bytecode part of the
deferred claim (`DeferredClaim.BytecodeHolds`, what the root's outer check V_I verifies) is enough
to make the children's bytecode claims true; the matrix part plays no part.

`bytecodeRest bytecode cs` is the batching after the children `cs` cut to that side: the lambdas
`lB`, the bytecode's sumcheck, and its final check with the bytecode's own value at the
sumcheck's point, `f(r) = mle(bytecode)(r) · weight(r)` (`bytecodePoly`). It reads no final value:
every hash it makes is one `Node.batchWith` makes (`LeanVM.E2E.Batch.With`), which matters once
the hashes are a log's answers. `bytecodeAny bytecode` is it for every child count, the count's
read naming it (as `Guest.Batch.batchAny`), from the batching's seedings `Guest.Batch.batchSeeds`.

* `bytecodeRestSpec`: after children of the bytecode's shapes with a nonzero gap on the bytecode
  (`∃ g ∈ gapsB bytecode cs, g ≠ 0`), a doom specification from the empty history with doom at
  the start and rejection at the end, each group of challenges escaping at most `batchε = 2/|E|`;
* `bytecodeCert`: the certificate of `bytecodeAny`, doom past a count's root and the reads of
  such children (`BytecodePre`); `bytecodeCert_bound`: its escape bounds are at most `batchε`;
* `doomed_of_falseBytecode`: an accepted run whose stream begins with children of the
  bytecode's shapes one of whose bytecode claims is false (`FalseBytecode`) passes a doomed
  boundary, for any answers `H`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.Rom LeanVM.Node LeanVM.Guest.Batch LeanVM.Guest.B1.Main
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The program -/

/-- **The bytecode part of the batching after its children**: the bytecode's lambdas, its
sumcheck, and the final check against the bytecode's value at the sumcheck's point. -/
noncomputable def bytecodeRest (bytecode : List K) (cs : List ChildClaims) : Prog Bool := do
  let lB ← sampleLB cs.length
  let rb ← roundsProg (claimBOf cs lB) (Nat.log2 bytecode.length)
  Prog.require (rb.2 = bytecodePoly bytecode cs lB rb.1)
  return true

/-- **The bytecode part of the batching of `n` children**: their cells, then the rest. -/
noncomputable def bytecodeProg (bytecode : List K) (n : ℕ) : Prog Bool := do
  let cs ← readChildren (Nat.log2 bytecode.length) n
  bytecodeRest bytecode cs

/-- **The bytecode part of the batching of every child count**: a read naming the count, then
the batching of that many children. -/
noncomputable def bytecodeAny (bytecode : List K) : Prog Bool :=
  .read fun e ↦ bytecodeProg bytecode (kNat (e.limb 0))

/-- The prover's stream of the bytecode part of a batching: the children's cells, then the
bytecode sumcheck's messages. -/
def bytecodeStream (cs : List ChildClaims) (h : BatchHints) : List E :=
  cs.flatMap childCells ++ h.bytecodeRounds.flatMap fun g ↦ [g.1, g.2]

/-! ## The program along the children's reads -/

/-- **Past the children's cells, the program is `bytecodeRest`.** -/
theorem after_bytecodeProg {bytecode : List K} {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (l : List Ev) :
    (bytecodeProg bytecode cs.length).after ((cs.flatMap childCells).map Ev.read ++ l) =
      (bytecodeRest bytecode cs).after l :=
  Prog.after_bind_append _ (after_readChildren hs) l

/-- After the child count's root, the program of every count is the program of that count. -/
theorem after_countRoot_bytecode (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) (l : List Ev) :
    (bytecodeAny bytecode).after (countRoot n ++ l) = (bytecodeProg bytecode n).after l := by
  simp only [countRoot, List.singleton_append, bytecodeAny, Prog.after, limb_wordE,
    kNat_ofBits hn]

/-- The node of `bytecodeAny` at a child count's root is the program of that count. -/
theorem nodeAt_countRoot_bytecode (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) :
    nodeAt (bytecodeAny bytecode) (countRoot n) = bytecodeProg bytecode n := by
  rw [nodeAt, ← List.append_nil (countRoot n), after_countRoot_bytecode bytecode hn]
  simp [Prog.after]

/-- A child count's root is a root of `bytecodeAny`. -/
theorem rootOk_countRoot_bytecode (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) :
    RootOk (bytecodeAny bytecode) (countRoot n) := by
  have ha : (bytecodeAny bytecode).after (countRoot n) = some (bytecodeProg bytecode n) := by
    rw [← List.append_nil (countRoot n)]
    exact (after_countRoot_bytecode bytecode hn []).trans (by simp [Prog.after])
  exact ⟨reachable_of_after_reads [wordE (K.ofBits n)] ha,
    boundary_map_read (l := [wordE (K.ofBits n)]) (by simp),
    grindBits_map_read [wordE (K.ofBits n)], commits_map_read [wordE (K.ofBits n)],
    by rw [ha]; rfl⟩

/-- The program after the children makes no proof of work. -/
theorem movesOK_bytecodeRest (bytecode : List K) (cs : List ChildClaims) :
    MovesOK (· ≤ 64) False (bytecodeRest bytecode cs) := by
  unfold bytecodeRest
  refine MovesOK.seq (movesOK_sampleLB _) fun _ ↦ ?_
  refine MovesOK.seq (movesOK_roundsProg _ _) fun _ ↦ ?_
  exact MovesOK.seq (movesOK_require _ _) fun _ ↦ trivial

/-! ## The doom specification -/

-- Two enumerations of `K` are in scope here (`LeanVM.Parameters`' and `LeanDa`'s); the
-- calculus (`Spec.sampleE`, `Spec.sample`) counts `E` with the first.
attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-- **Doom of the bytecode part**: the bytecode's lambdas and rounds tracked, after children of
the bytecode's shapes with a nonzero gap on the bytecode; the final check contradicts it. -/
noncomputable def bytecodeRestSpec {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (hB : ∃ g ∈ gapsB bytecode cs, g ≠ 0) :
    Spec (bytecodeRest bytecode cs) (fun h ↦ h = []) (fun b _ ↦ b = false) batchε batchε 0 :=
  ((lamSpecB (gapsB bytecode cs) cs.length 0 [] rfl).bind' fun lB ↦
    ((roundsSpec (bytecode_quadraticIn hb (bytecodePoints hs) lB) _ (claimBOf cs lB) []
        (by simp)).mono (fun _ h ↦ claimB_ne hb hs h.1 h.2) (fun _ _ h ↦ h) le_rfl le_rfl
        le_rfl).bind' fun rb ↦
      (Spec.require (Post := fun _ _ ↦ False) fun _ hφ hc ↦ hφ (by
          rw [List.nil_append]; exact hc)).bind' fun _ ↦
        Spec.dead).mono
    (fun _ _ ↦ lDoom_nil hB) (fun _ _ h ↦ h) le_rfl (lamLead_le _ _) le_rfl

/-! ## The certificate -/

/-- **A doomed prefix of the bytecode part**: fewer than `2^64` children of the bytecode's
shapes, with a nonzero gap on the bytecode. -/
structure BytecodePre (bytecode : List K) where
  /-- The children. -/
  cs : List ChildClaims
  /-- Their count is a word. -/
  lt : cs.length < 2 ^ 64
  /-- They have the bytecode's shapes. -/
  shaped : ∀ c ∈ cs, ChildShaped bytecode c
  /-- Some claim on the bytecode leaves a nonzero gap. -/
  gap : ∃ g ∈ gapsB bytecode cs, g ≠ 0

namespace BytecodePre

variable {bytecode : List K}

/-- The history of a prefix: the child count's root, then the children's cells read. -/
def hist (p : BytecodePre bytecode) : List Ev :=
  countRoot p.cs.length ++ (p.cs.flatMap childCells).map Ev.read

/-- The certificate after a prefix's children: `bytecodeRestSpec`'s. -/
noncomputable def cert (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (p : BytecodePre bytecode) : Cert (bytecodeRest bytecode p.cs) :=
  (bytecodeRestSpec hb p.shaped p.gap).toCertOfLead

/-- A prefix's history is the reads of the count's word and the children's cells. -/
theorem hist_eq (p : BytecodePre bytecode) :
    p.hist = (wordE (K.ofBits p.cs.length) :: p.cs.flatMap childCells).map Ev.read := rfl

/-- Past a prefix's history, the program is `bytecodeRest` of its children. -/
theorem after_hist (p : BytecodePre bytecode) :
    (bytecodeAny bytecode).after p.hist = some (bytecodeRest bytecode p.cs) := by
  rw [hist, after_countRoot_bytecode bytecode p.lt, ← List.append_nil (List.map _ _),
    after_bytecodeProg p.shaped]
  simp [Prog.after]

/-- A prefix's history commits nothing. -/
theorem commits_hist (p : BytecodePre bytecode) : commits p.hist = [] := by
  rw [hist_eq]; exact commits_map_read _

/-- A prefix's history adds no proof of work. -/
theorem grindBits_hist (p : BytecodePre bytecode) (h' : List Ev) :
    grindBits (p.hist ++ h') = grindBits h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · rw [List.append_nil, hist_eq]; exact grindBits_map_read _
  · rw [List.concat_eq_append, ← List.append_assoc]
    simp [grindBits]

/-- **Prefixes are prefix-free**: two prefixes on one history are one prefix. -/
theorem hist_inj {p q : BytecodePre bytecode} {h' h'' : List Ev}
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

end BytecodePre

/-- **Doom of the bytecode part**: past a prefix, the doom of its certificate on the rest. -/
def bytecodeD {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (h : List Ev) : Prop :=
  ∃ (p : BytecodePre bytecode) (h' : List Ev), h = p.hist ++ h' ∧ (p.cert hb).D h'

open Classical in
/-- The escape bound of the bytecode part: its certificate's past a prefix, `0` elsewhere. -/
noncomputable def bytecodeCertε {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (h : List Ev) : ℝ≥0∞ :=
  if hx : ∃ (p : BytecodePre bytecode) (h' : List Ev), h = p.hist ++ h' then
    (hx.choose.cert hb).ε hx.choose_spec.choose
  else 0

section Cert

variable {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)

/-- Past a prefix, doom is the prefix certificate's. -/
theorem bytecodeD_iff (p : BytecodePre bytecode) (h' : List Ev) :
    bytecodeD hb (p.hist ++ h') ↔ (p.cert hb).D h' := by
  constructor
  · rintro ⟨q, h'', he, hD⟩
    obtain ⟨rfl, rfl⟩ := BytecodePre.hist_inj he
    exact hD
  · intro hD
    exact ⟨p, h', rfl, hD⟩

/-- Past a prefix, the escape bound is the prefix certificate's. -/
theorem bytecodeCertε_eq (p : BytecodePre bytecode) (h' : List Ev) :
    bytecodeCertε hb (p.hist ++ h') = (p.cert hb).ε h' := by
  have key : ∀ (q : BytecodePre bytecode) (h'' : List Ev), p.hist ++ h' = q.hist ++ h'' →
      (q.cert hb).ε h'' = (p.cert hb).ε h' := by
    intro q h'' he
    obtain ⟨rfl, rfl⟩ := BytecodePre.hist_inj he
    rfl
  unfold bytecodeCertε
  split
  · rename_i hx
    exact key _ _ hx.choose_spec.choose_spec
  · rename_i hx
    exact absurd ⟨p, h', rfl⟩ hx

end Cert

/-- **The certificate of the bytecode part**, for every child count. -/
noncomputable def bytecodeCert {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) : Cert (bytecodeAny bytecode) where
  D := bytecodeD hb
  ε := bytecodeCertε hb
  read := by
    intro h k e hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, bytecodeD_iff]
    exact (p.cert hb).read e (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp
  grind := by
    intro h b k hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, bytecodeD_iff]
    exact (p.cert hb).grind (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp
  commit := by
    intro h ht w k word hr ha hw hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, bytecodeD_iff]
    exact (p.cert hb).commit word (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hw hDp
  group := by
    intro h q hr hbd ha hq hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [esc_drop (h₀ := p.hist) p.commits_hist (bytecodeD_iff hb p), bytecodeCertε_eq]
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
theorem bytecodeCert_bound {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (bytecodeCert hb).ε h ≤ batchε := by
  by_cases hx : ∃ (p : BytecodePre bytecode) (h' : List Ev), h = p.hist ++ h'
  · obtain ⟨p, h', rfl⟩ := hx
    show _ * bytecodeCertε hb _ ≤ _
    rw [bytecodeCertε_eq, p.grindBits_hist]
    by_cases hr : (bytecodeRest bytecode p.cs).Reachable h'
    · rw [min_eq_left ((movesOK_bytecodeRest bytecode p.cs).grindBits_le hr)]
      exact Spec.toCertOfLead_bound _ le_rfl h'
    · simp only [BytecodePre.cert, Spec.toCertOfLead, Spec.toCert_ε, hr, false_and,
        ↓reduceIte, mul_zero, zero_le]
  · show _ * bytecodeCertε hb _ ≤ _
    simp only [bytecodeCertε, hx, ↓reduceDIte, mul_zero, zero_le]

/-! ## Doom on accepted runs -/

/-- The proof's stream begins with the cells of `n` children of the bytecode's shapes, one of
whose bytecode claims is false: its proof's (`FixedClaims.BytecodeHolds`) or its statement's
(`DeferredClaim.BytecodeHolds`). -/
def FalseBytecode (bytecode : List K) (n : ℕ) (π : Proof) : Prop :=
  ∃ cs : List ChildClaims, cs.length = n ∧ (∀ c ∈ cs, ChildShaped bytecode c) ∧
    cs.flatMap childCells <+: π.stream ∧
    ¬ ∀ c ∈ cs, c.fresh.BytecodeHolds bytecode ∧ c.carried.BytecodeHolds bytecode

/-- **False bytecode claims leave a nonzero gap on the bytecode**: children of the bytecode's
shapes with no nonzero gap on it have true bytecode claims, `bytecode` of length a power of two. -/
theorem gapB_of_false {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c)
    (hn : ¬ ∀ c ∈ cs, c.fresh.BytecodeHolds bytecode ∧ c.carried.BytecodeHolds bytecode) :
    ∃ g ∈ gapsB bytecode cs, g ≠ 0 := by
  by_contra hz
  refine hn fun c hc ↦ ?_
  have hz' : ∀ g ∈ gapsB bytecode cs, g = 0 := fun g hg ↦ by
    by_contra h
    exact hz ⟨g, hg, h⟩
  have gB := fun g hg ↦ hz' g (List.mem_flatMap.mpr ⟨c, hc, hg⟩)
  have e1 := sub_eq_zero.mp (gB _ (List.mem_cons_self ..))
  have e2 := sub_eq_zero.mp (gB _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨e1.symm, (hs c hc).2, ?_, e2.symm⟩
  rw [(hs c hc).2.1]
  exact hb.symm

/-- **False bytecode claims doom an accepted run**, for any answers `H`: past the count's root and
the children's reads, `bytecodeRestSpec` is doomed at its start. -/
theorem doomed_of_falseBytecode {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {M : ℕ} (hM : M ≤ 2 ^ 64 - 1)
    {H : Bytes → Option Digest} {x : Fin M} {π : Proof}
    (hv : Rom.verify H ((batchSeeds M hM).seed x)
      (nodeAt (bytecodeAny bytecode) ((batchSeeds M hM).root x)) π = some true)
    (hf : FalseBytecode bytecode x π) :
    ∃ h₀, h₀ <+: extractedFrom H ((batchSeeds M hM).seed x)
        (nodeAt (bytecodeAny bytecode) ((batchSeeds M hM).root x)) ((batchSeeds M hM).root x) π ∧
      ((batchSeeds M hM).root x).length ≤ h₀.length ∧ Boundary h₀ ∧ (bytecodeCert hb).D h₀ := by
  obtain ⟨cs, hlen, hs, hpre, hn⟩ := hf
  have hx := x.2
  have hz : (x : ℕ) < 2 ^ 64 := by omega
  have hlt : cs.length < 2 ^ 64 := by rw [hlen]; exact hz
  let p : BytecodePre bytecode := ⟨cs, hlt, hs, gapB_of_false hb hs hn⟩
  have hroot : (batchSeeds M hM).root x = countRoot x := rfl
  rw [hroot, nodeAt_countRoot_bytecode bytecode hz] at hv
  refine ⟨p.hist, ?_, ?_, ?_, ?_⟩
  · rw [hroot, nodeAt_countRoot_bytecode bytecode hz, extractedFrom_eq _ _ _ _ _ hv]
    show countRoot cs.length ++ _ <+: _
    rw [hlen]
    refine (List.prefix_append_right_inj _).mpr ?_
    obtain ⟨seed, s, -, hxr⟩ := xrun_of_verify hv
    have ha : (bytecodeProg bytecode x).after ((cs.flatMap childCells).map Ev.read) =
        some (bytecodeRest bytecode cs) := by
      rw [← hlen, ← List.append_nil (List.map _ _), after_bytecodeProg hs]
      simp [Prog.after]
    simpa using xrun_reads _ _ _ _ [] ha hpre hxr
  · rw [hroot]
    simp [BytecodePre.hist, countRoot, p]
  · rw [p.hist_eq]
    exact boundary_map_read (by simp)
  · exact ⟨p, [], by rw [List.append_nil], (bytecodeRestSpec hb p.shaped p.gap).start_D [] rfl⟩

/-! ## The bytecode part, challenge by challenge -/

/-- **The batching's bytecode part is sound, challenge by challenge** (`Guest.Batch.batch_sound`
for the bytecode part alone): an accepted batching whose deferred claim's bytecode part holds,
of children whose claims have the bytecode's shapes, makes every child's bytecode claims true, or
a challenge of the bytecode's side is bad (its lambdas, or a round of its sumcheck). The matrices'
side and the matrix part of the deferred claim play no part. -/
theorem batch_sound_bytecode {bytecode : List K} {cs : List ChildClaims} {h : BatchHints}
    {d : DeferredClaim} (hb : batch cs h = some d) (hd : d.BytecodeHolds bytecode)
    (hf : ∀ c ∈ cs, FreshShapedFor bytecode c.fresh) (hc : ∀ c ∈ cs, c.carried.Shaped bytecode) :
    (∀ c ∈ cs, c.fresh.BytecodeHolds bytecode ∧ c.carried.BytecodeHolds bytecode) ∨
      SideBad (gapsB bytecode cs) ((lambdasB cs).flatMap fun l ↦ [l.1, l.2])
        (bytecodePoly bytecode cs (lambdasB cs)) h.bytecodeRounds (claimB cs) (cvB cs) := by
  rw [batch_eq] at hb
  split_ifs at hb with hcond
  injection hb with hd'
  subst hd'
  obtain ⟨hfinB, -⟩ := hcond
  obtain ⟨⟨hlogB, -⟩, hpow, hvalB⟩ := hd
  simp only at hlogB hpow hvalB
  rw [length_bsRun] at hlogB hpow
  set n := h.bytecodeRounds.length
  have hlog : Nat.log2 bytecode.length = n := by rw [← hpow, Nat.log2_two_pow]
  have hpB : ∀ c ∈ cs, c.fresh.bytecodePoint.length = n ∧ c.carried.bytecodePoint.length = n :=
    fun c hc' ↦ ⟨(hf c hc').1.trans hlog, (hc c hc').1.trans hlog⟩
  have hsubB := sub_pairs cs (lambdasB cs) (length_sq2 _ _)
    (fun c ↦ c.fresh.bytecodeValue) (fun c ↦ c.carried.bytecodeValue)
    (fun c ↦ multilinearEval (bytecode.map ofK) c.fresh.bytecodePoint)
    (fun c ↦ multilinearEval (bytecode.map ofK) c.carried.bytecodePoint)
  rcases gaps_cases hsubB with hzB | hbadB | hneB
  rotate_left
  · exact Or.inr (Or.inl hbadB)
  · refine Or.inr (Or.inr (rounds_sound rfl ?_ ?_))
    · rw [roundChallenges, hfinB, bytecodePoly, hvalB]
    · rw [bytecode_cubeSum hpow.symm hpB]; exact hneB
  refine Or.inl fun c hc' ↦ ?_
  have gB := fun g hg ↦ hzB g (List.mem_flatMap.mpr ⟨c, hc', hg⟩)
  have e1 := sub_eq_zero.mp (gB _ (List.mem_cons_self ..))
  have e2 := sub_eq_zero.mp (gB _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨e1.symm, hc c hc', ?_, e2.symm⟩
  rw [(hpB c hc').2, hpow]

end
end LeanVM.E2E
